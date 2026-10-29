/-
  LeanSys.Http: Zero-Copy Bounded HTTP/1.1 Parser, Smuggling-Safe Framing, Server Loop, and Client
  (`0 import Lean`, `0 sorryAx`)
  - Zero-copy header & body parser over `ByteSlice` (`maxHeaders ≤ 32`, `maxHeaderBytes ≤ 32 KiB`, `maxBody ≤ 4 MiB`)
  - Gated by `LeanSys.Spec.checkHttpBounds` (`leansys_check_http_bounds`) and constant-time bearer auth (`LeanSys.Auth.ctEqString`)
  - Rejects HTTP request smuggling vectors: any `Transfer-Encoding` header, negative/non-digit `Content-Length`,
    or conflicting multiple `Content-Length` headers (`400 Bad Request`)
  - Looped `pollReadable` + `readStreamChunk` framing (`readHttpRequestStream`) handles arbitrarily fragmented
    byte-by-byte / slow-loris headers and bodies under wall-clock timeout and returns pipelined trailing bytes
    for keep-alive sessions without silent message drops
-/
import LeanSys.Spec
import LeanSys.Posix
import LeanSys.Auth

namespace LeanSys.Http

open LeanSys.Spec
open LeanSys.Posix
open LeanSys.Auth

/-- Maximum HTTP/1.1 header section size in bytes (32 KiB). -/
@[inline] def maxHttpHeaderBytes : Nat := 32768

/-- Maximum HTTP/1.1 request body size in bytes (4 MiB). -/
@[inline] def maxHttpBodyBytes : Nat := 4194304

/-- Parsed zero-copy HTTP/1.1 request over a backing `ByteArray`. -/
structure HttpRequest where
  method        : String
  path          : String
  headers       : Array (String × String)
  contentLength : Nat
  authBearer    : Option String
  bodySlice     : ByteSlice

/-- Outgoing HTTP/1.1 response. -/
structure HttpResponse where
  status      : Nat := 200
  contentType : String := "application/json"
  body        : ByteArray

namespace HttpResponse

/-- Construct a JSON `HttpResponse`. -/
@[inline]
def json (status : Nat) (jsonBody : String) : HttpResponse :=
  { status := status, contentType := "application/json", body := jsonBody.toUTF8 }

/-- Canonical HTTP/1.1 reason phrase for status code. -/
def reasonPhrase (status : Nat) : String :=
  match status with
  | 200 => "OK"
  | 201 => "Created"
  | 204 => "No Content"
  | 400 => "Bad Request"
  | 401 => "Unauthorized"
  | 403 => "Forbidden"
  | 404 => "Not Found"
  | 405 => "Method Not Allowed"
  | 408 => "Request Timeout"
  | 413 => "Payload Too Large"
  | 431 => "Request Header Fields Too Large"
  | 500 => "Internal Server Error"
  | _   => "OK"

/-- Serialize an `HttpResponse` into an HTTP/1.1 wire `ByteArray`. -/
def toWireBytes (r : HttpResponse) : ByteArray :=
  let statusText := reasonPhrase r.status
  let head :=
    s!"HTTP/1.1 {r.status} {statusText}\r\n" ++
    s!"Content-Type: {r.contentType}\r\n" ++
    s!"Content-Length: {r.body.size}\r\n" ++
    "Connection: close\r\n\r\n"
  head.toUTF8 ++ r.body

end HttpResponse

/-- Declarative bounded HTTP/1.1 route table entry (`method`, `path`, `handler`). -/
structure RouteEntry where
  method  : String
  path    : String
  handler : HttpRequest → IO HttpResponse

instance : Inhabited RouteEntry :=
  ⟨{ method := "", path := "", handler := fun _ => pure (HttpResponse.json 404 "") }⟩

/--
  Dispatch an `HttpRequest` against a bounded static route table (`routes.size ≤ 64`),
  gated by `leansys_verify_http_route_match`:
  - Invokes the first matching `(method, path)` handler.
  - Returns `500 Internal Server Error` if `routes.size > 64`.
  - Returns `405 Method Not Allowed` if `req.path` matches a route in `routes` but `req.method` does not.
  - Returns `404 Not Found` if no route matches `req.path`.
-/
def dispatchRoutes (routes : Array RouteEntry) (req : HttpRequest) : IO HttpResponse := do
  let n := routes.size
  if n > 64 then
    return HttpResponse.json 500 "{\"ok\":false,\"error\":\"route_table_overflow\"}"
  let mut pathMatched := false
  for i in [0:n] do
    let rt := routes[i]!
    let mMatch : UInt8 := if rt.method == req.method then 1 else 0
    let pMatch : UInt8 := if rt.path == req.path then 1 else 0
    if pMatch == 1 then
      pathMatched := true
    if verifyHttpRouteMatch mMatch pMatch i.toUInt32 n.toUInt32 == 1 then
      return (← rt.handler req)
  if pathMatched then
    return HttpResponse.json 405 "{\"ok\":false,\"error\":\"method_not_allowed\"}"
  else
    return HttpResponse.json 404 "{\"ok\":false,\"error\":\"not_found\"}"

/-- Find the index of `\r\n\r\n` (`13, 10, 13, 10`) in `ba`, returning the byte offset of the body start. -/
def findHeaderEnd? (ba : ByteArray) : Option Nat := Id.run do
  if ba.size < 4 then return none
  let limit := ba.size - 3
  for i in [0:limit] do
    if ba.get! i == 13 && ba.get! (i + 1) == 10 &&
       ba.get! (i + 2) == 13 && ba.get! (i + 3) == 10 then
      return some (i + 4)
  return none

/-- Strict ASCII unsigned decimal parser for `Content-Length`:
    rejects empty strings, negative signs, spaces inside digits, or any non-digit character (`none`). -/
def parseStrictContentLength? (s : String) : Option Nat := Id.run do
  let bytes := s.trimAscii.toString.toUTF8
  if bytes.isEmpty || bytes.size > 16 then return none
  let mut acc : Nat := 0
  for i in [0:bytes.size] do
    let b := bytes.get! i
    if 48 ≤ b && b ≤ 57 then
      acc := acc * 10 + (b - 48).toNat
    else
      return none
  return some acc

/-- Parse a decimal `Nat` from an ASCII string (returns `0` if empty or non-numeric). -/
def parseNatAscii (s : String) : Nat :=
  (parseStrictContentLength? s).getD 0

/-- Case-insensitive ASCII equality for short HTTP header names. -/
def asciiEqIgnoreCase (a b : String) : Bool := Id.run do
  let ba := a.trimAscii.toString.toUTF8
  let bb := b.trimAscii.toString.toUTF8
  if ba.size != bb.size then return false
  for i in [0:ba.size] do
    let ca := ba.get! i
    let cb := bb.get! i
    let la := if 65 ≤ ca && ca ≤ 90 then ca + 32 else ca
    let lb := if 65 ≤ cb && cb ≤ 90 then cb + 32 else cb
    if la != lb then return false
  return true

/-- Inspect raw header lines for framing validity before/during body reads:
    - Rejects `Transfer-Encoding` (`unsupported_transfer_encoding`)
    - Rejects non-digit/negative `Content-Length` (`invalid_content_length`)
    - Rejects conflicting multiple `Content-Length` headers (`conflicting_content_length`)
    - Enforces `headers.size ≤ 32` (`too_many_headers`) and `contentLen ≤ 4194304` (`payload_too_large`). -/
private def parseValidatedHeaders (hdrLines : List String) :
    Except String (Array (String × String) × Option Nat × Option String) := Id.run do
  let mut headers : Array (String × String) := #[]
  let mut seenContentLen : Option Nat := none
  let mut authBearer : Option String := none
  for ln in hdrLines do
    if !ln.isEmpty then
      let lnBytes := ln.toUTF8
      let b0 := if lnBytes.size > 0 then lnBytes.get! 0 else 0
      if b0 == 32 || b0 == 9 then
        return .error "obs_fold_header_rejected"
      match ln.splitOn ":" with
      | [] | [_] =>
        return .error "malformed_header_line"
      | k :: rest =>
        if k.isEmpty || (k.splitOn " ").length > 1 || (k.splitOn "\t").length > 1 then
          return .error "invalid_header_name"
        let kTrim := k.trimAscii.toString
        let vTrim := (String.intercalate ":" rest).trimAscii.toString
        headers := headers.push (kTrim, vTrim)
        if headers.size > 32 then
          return .error "too_many_headers"
        if asciiEqIgnoreCase kTrim "transfer-encoding" then
          return .error "unsupported_transfer_encoding"
        else if asciiEqIgnoreCase kTrim "content-length" then
          match parseStrictContentLength? vTrim with
          | none =>
            return .error "invalid_content_length"
          | some parsedLen =>
            if parsedLen > maxHttpBodyBytes then
              return .error "payload_too_large"
            match seenContentLen with
            | none => seenContentLen := some parsedLen
            | some prevLen =>
              if prevLen != parsedLen then
                return .error "conflicting_content_length"
        else if asciiEqIgnoreCase kTrim "authorization" then
          if vTrim.startsWith "Bearer " then
            authBearer := some (vTrim.drop 7).trimAscii.toString
  return .ok (headers, seenContentLen, authBearer)

/--
  Zero-copy bounded HTTP/1.1 request parser over `raw : ByteArray`, returning `(HttpRequest, consumedBytes)`
  so pipelined / keep-alive connections can slice off `raw.extract consumedBytes raw.size` without losing
  subsequent requests. Gated by `leansys_check_http_bounds` and constant-time `ctEqString` bearer verification.
-/
def parseRequestPrefix (raw : ByteArray) (expectedBearer? : Option String := none)
    (allowTrailingBytes : Bool := false) : Except String (HttpRequest × Nat) := do
  let some bodyStart := findHeaderEnd? raw
    | .error "missing_header_terminator"
  if bodyStart - 4 > maxHttpHeaderBytes then
    .error "headers_too_large"
  let rootSlice := ByteSlice.ofByteArray raw
  let some headSlice := ByteSlice.subSlice? rootSlice 0 (bodyStart - 4)
    | .error "invalid_header_slice"
  let some headStr := String.fromUTF8? headSlice.toByteArray
    | .error "invalid_utf8_headers"
  let lines := headStr.splitOn "\r\n"
  match lines with
  | [] => .error "empty_request_line"
  | reqLine :: hdrLines =>
    let parts := reqLine.trimAscii.toString.splitOn " "
    let (method, path, proto) ← match parts with
      | [m, p, v] => .ok (m.trimAscii.toString, p.trimAscii.toString, v.trimAscii.toString)
      | _ => .error "malformed_request_line"
    if proto != "HTTP/1.1" && proto != "HTTP/1.0" then
      .error "unsupported_http_version"
    if path.isEmpty || !path.startsWith "/" then
      .error "malformed_request_target"
    if method != "GET" && method != "POST" && method != "HEAD" && method != "PUT" && method != "DELETE" then
      .error s!"unsupported_method:{method}"
    let (headers, contentLen?, authBearer) ← parseValidatedHeaders hdrLines
    let declContentLen := contentLen?.getD 0
    let availTotalBody := raw.size - bodyStart
    if availTotalBody < declContentLen then
      .error "content_length_mismatch"
    else if !allowTrailingBytes && availTotalBody != declContentLen then
      .error "content_length_mismatch"
    else
      let framedBodyLen := if allowTrailingBytes then declContentLen else availTotalBody
      let authOk : UInt8 := match expectedBearer? with
        | none => 1
        | some reqTok =>
          match authBearer with
          | some presented => if ctEqString presented reqTok then 1 else 0
          | none => 0
      if checkHttpBounds headers.size.toUInt32 declContentLen.toUInt64 framedBodyLen.toUInt64 authOk != 1 then
        if authOk == 0 then .error "unauthorized_bearer_token"
        else if headers.size > 32 then .error "too_many_headers"
        else if declContentLen > maxHttpBodyBytes then .error "payload_too_large"
        else .error "content_length_mismatch"
      else
        let some bodySlice := ByteSlice.subSlice? rootSlice bodyStart declContentLen
          | .error "invalid_body_slice"
        let req : HttpRequest := {
          method := method
          path := path
          headers := headers
          contentLength := declContentLen
          authBearer := authBearer
          bodySlice := bodySlice
        }
        .ok (req, bodyStart + declContentLen)

/--
  Zero-copy bounded HTTP/1.1 request parser over an exact single-request `raw : ByteArray`,
  gated by `leansys_check_http_bounds`.
-/
def parseRequest (raw : ByteArray) (expectedBearer? : Option String := none) : Except String HttpRequest := do
  let (req, _) ← parseRequestPrefix raw expectedBearer? false
  return req

/-- Map a framing/validation error code to its canonical HTTP status code. -/
def statusForParseError (errMsg : String) : Nat :=
  if errMsg == "unauthorized_bearer_token" then 401
  else if errMsg == "payload_too_large" then 413
  else if errMsg == "headers_too_large" || errMsg == "too_many_headers" then 431
  else if errMsg == "request_timeout" then 408
  else 400

/-- Read one complete bounded HTTP/1.1 request from socket `fd` starting from `initialCarry`
    (leftover bytes from a previous pipelined keep-alive request), looping `pollReadable` + `readStreamChunk`
    until `\r\n\r\n` and all `Content-Length` body bytes arrive or `timeoutMs` expires.
    Returns `.ok (req, remainingCarry)` on success. -/
def readHttpRequestStream (fd : Fd) (initialCarry : ByteArray := ByteArray.empty)
    (expectedBearer? : Option String := none) (timeoutMs : UInt32 := 2000) :
    IO (Except String (HttpRequest × ByteArray)) := do
  let tStart ← IO.monoNanosNow
  let budgetMs : Nat := Nat.max 50 timeoutMs.toNat
  let mut buf := initialCarry

  -- Phase 1: Accumulate until `\r\n\r\n` (enforcing `maxHttpHeaderBytes = 32 KiB`)
  while (findHeaderEnd? buf).isNone do
    if buf.size > maxHttpHeaderBytes + 4 then
      return .error "headers_too_large"
    let now ← IO.monoNanosNow
    let elapsedMs := (now - tStart) / 1000000
    if elapsedMs >= budgetMs then
      return .error (if buf.isEmpty then "empty_socket_read" else "request_timeout")
    let remMs : UInt32 := (budgetMs - elapsedMs).toUInt32
    match ← pollReadable fd remMs with
    | .error .eagain =>
      return .error (if buf.isEmpty then "empty_socket_read" else "request_timeout")
    | .error _ =>
      return .error "socket_poll_error"
    | .ok () =>
      let chunk ← readStreamChunk fd 16384
      if chunk.isEmpty then
        return .error (if buf.isEmpty then "empty_socket_read" else "missing_header_terminator")
      buf := if buf.isEmpty then chunk else buf ++ chunk

  let some bodyStart := findHeaderEnd? buf
    | return .error "missing_header_terminator"
  if bodyStart - 4 > maxHttpHeaderBytes then
    return .error "headers_too_large"

  -- Validate headers early before allocating/reading body bytes
  let some headStr := String.fromUTF8? (buf.extract 0 (bodyStart - 4))
    | return .error "invalid_utf8_headers"
  let hdrLines := (headStr.splitOn "\r\n").drop 1
  let expectedBody ← match parseValidatedHeaders hdrLines with
    | .error e => return .error e
    | .ok (_, cl?, _) => pure (cl?.getD 0)

  -- Phase 2: Loop `pollReadable` + `readStreamChunk` until `expectedBody` bytes are buffered
  while buf.size - bodyStart < expectedBody do
    let now ← IO.monoNanosNow
    let elapsedMs := (now - tStart) / 1000000
    if elapsedMs >= budgetMs then
      return .error "request_timeout"
    let remMs : UInt32 := (budgetMs - elapsedMs).toUInt32
    match ← pollReadable fd remMs with
    | .error .eagain =>
      return .error "request_timeout"
    | .error _ =>
      return .error "socket_poll_error"
    | .ok () =>
      let missing := expectedBody - (buf.size - bodyStart)
      let chunk ← readStreamChunk fd (Nat.min missing 65536)
      if chunk.isEmpty then
        return .error "content_length_mismatch"
      buf := buf ++ chunk

  match parseRequestPrefix buf expectedBearer? true with
  | .error e => return .error e
  | .ok (req, consumed) =>
    let carry := if consumed < buf.size then buf.extract consumed buf.size else ByteArray.empty
    return .ok (req, carry)

/-- Read an entire bounded HTTP/1.1 request from a connected socket `fd` (single-request wrapper). -/
def readHttpRequestFromFd (fd : Fd) (expectedBearer? : Option String := none)
    (timeoutMs : UInt32 := 2000) : IO (Except String HttpRequest) := do
  match ← readHttpRequestStream fd ByteArray.empty expectedBearer? timeoutMs with
  | .error e => return .error e
  | .ok (req, _) => return .ok req

/-- Handle a single accepted client socket connection and close `clientFd` deterministically. -/
def serveSingleConnection (clientFd : Fd) (expectedBearer? : Option String)
    (handler : HttpRequest → IO HttpResponse) (timeoutMs : UInt32 := 2000) : IO Unit := do
  try
    let resp ← match ← readHttpRequestFromFd clientFd expectedBearer? timeoutMs with
      | .ok req => handler req
      | .error errMsg =>
        let code := statusForParseError errMsg
        pure (HttpResponse.json code s!"\{\"ok\":false,\"error\":\"{errMsg}\"}")
    discard <| writeAll clientFd resp.toWireBytes false
  finally
    discard <| closeFd clientFd

/-- Accept and serve up to `maxRequests` on an already-bound `listenFd` (`maxRequests = 0` runs indefinitely). -/
def serveLoop (listenFd : Fd) (maxRequests : Nat := 0) (timeoutMs : UInt32 := 2000)
    (expectedBearer? : Option String := none)
    (handler : HttpRequest → IO HttpResponse) : IO Unit := do
  let mut served := 0
  while maxRequests == 0 || served < maxRequests do
    match ← tcpAcceptPoll listenFd timeoutMs with
    | .ok clientFd =>
      serveSingleConnection clientFd expectedBearer? handler timeoutMs
      served := served + 1
    | .error .eagain =>
      if maxRequests > 0 then break
    | .error _ =>
      if maxRequests > 0 then break

/-- Perform an HTTP/1.1 client request to `host:port`, looping `pollReadable` + `readStreamChunk`
    until `\r\n\r\n` and all declared `Content-Length` response body bytes arrive (or clean EOF when
    no `Content-Length` is declared). Fails closed on deadline expiry (`.error .eagain`), socket poll
    errors, malformed response framing/headers (`.error .einval`), or premature EOF before headers or
    declared `Content-Length` (`.error .eio`). -/
def httpClientRequest (host : String) (port : UInt16) (method : String) (path : String)
    (body : ByteSlice) (bearerToken? : Option String := none) (timeoutMs : UInt32 := 3000) :
    IO (SysResult String) := do
  match ← tcpConnect host port with
  | .error e => pure (.error e)
  | .ok fd =>
    try
      let authHdr := match bearerToken? with
        | some tok => s!"Authorization: Bearer {tok}\r\n"
        | none => ""
      let reqHead :=
        s!"{method} {path} HTTP/1.1\r\n" ++
        s!"Host: {host}:{port}\r\n" ++
        "Content-Type: application/json\r\n" ++
        authHdr ++
        s!"Content-Length: {body.len}\r\n" ++
        "Connection: close\r\n\r\n"
      let wire := reqHead.toUTF8 ++ body.toByteArray
      match ← writeAll fd wire false with
      | .error e => pure (.error e)
      | .ok _ =>
        let t0 ← IO.monoNanosNow
        let budgetMs := Nat.max 50 timeoutMs.toNat
        let mut respBuf := ByteArray.empty
        let mut hdrEnd? : Option Nat := none
        let mut targetTotal : Option Nat := none
        let mut eof := false
        let mut ioErr? : Option Errno := none
        while !eof && ioErr?.isNone do
          match targetTotal with
          | some tot =>
            if respBuf.size >= tot then break
          | none => pure ()
          if hdrEnd?.isNone && respBuf.size > maxHttpHeaderBytes + 4 then
            ioErr? := some .einval
            break
          let now ← IO.monoNanosNow
          let elapsedMs := (now - t0) / 1000000
          if elapsedMs >= budgetMs then
            ioErr? := some .eagain
            break
          match ← pollReadable fd (budgetMs - elapsedMs).toUInt32 with
          | .error e =>
            ioErr? := some e
            break
          | .ok () =>
            let chunk ← readStreamChunk fd 65536
            if chunk.isEmpty then
              eof := true
            else
              respBuf := if respBuf.isEmpty then chunk else respBuf ++ chunk
              if hdrEnd?.isNone then
                if let some bStart := findHeaderEnd? respBuf then
                  if bStart - 4 > maxHttpHeaderBytes then
                    ioErr? := some .einval
                  else
                    match String.fromUTF8? (respBuf.extract 0 (bStart - 4)) with
                    | none => ioErr? := some .einval
                    | some headStr =>
                      match headStr.splitOn "\r\n" with
                      | [] => ioErr? := some .einval
                      | statusLine :: hdrLines =>
                        if !(statusLine.startsWith "HTTP/1.1 " || statusLine.startsWith "HTTP/1.0 ") then
                          ioErr? := some .einval
                        else
                          match parseValidatedHeaders hdrLines with
                          | .error _ => ioErr? := some .einval
                          | .ok (_, cl?, _) =>
                            hdrEnd? := some bStart
                            if let some cl := cl? then
                              targetTotal := some (bStart + cl)
        match ioErr? with
        | some e => pure (.error e)
        | none =>
          match hdrEnd? with
          | none => pure (.error .eio)
          | some bStart =>
            match targetTotal with
            | some tot =>
              if respBuf.size < tot then
                pure (.error .eio)
              else
                let bodyBytes := respBuf.extract bStart tot
                pure (.ok (String.fromUTF8! bodyBytes))
            | none =>
              if respBuf.size - bStart > maxHttpBodyBytes then
                pure (.error .einval)
              else
                let bodyBytes := respBuf.extract bStart respBuf.size
                pure (.ok (String.fromUTF8! bodyBytes))
    finally
      discard <| closeFd fd

end LeanSys.Http
