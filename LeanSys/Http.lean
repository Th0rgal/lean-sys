/-
  LeanSys.Http: Zero-Copy Bounded HTTP/1.1 Parser, Smuggling-Safe Framing, Server Loop, and Client
  (`0 import Lean`, `0 sorryAx`)
  - Zero-copy header & body parser over `ByteSlice` (`maxHeaders ≤ 32`, `maxHeaderBytes ≤ 32 KiB`, `maxBody ≤ 4 MiB`)
  - Gated by `LeanSys.Spec.checkHttpBounds` (`leansys_check_http_bounds`) and constant-time bearer auth (`LeanSys.Auth.ctEqString`)
  - Rejects HTTP request smuggling vectors: any `Transfer-Encoding` header, negative/non-digit `Content-Length`,
    any repeated `Content-Length` or `Authorization` header, non-`token` field names, and control bytes
    in field lines (`400 Bad Request`)
  - Looped `pollReadable` + `readStreamChunk` framing (`readHttpRequestStream`) handles arbitrarily fragmented
    byte-by-byte / slow-loris headers and bodies under wall-clock timeout and returns pipelined trailing bytes
    for keep-alive sessions without silent message drops
-/
import LeanSys.Spec
import LeanSys.Posix
import LeanSys.Auth
import LeanSys.WebSocket

namespace LeanSys.Http

open LeanSys.Spec
open LeanSys.Posix
open LeanSys.Auth

/-- Maximum HTTP/1.1 header section size in bytes (32 KiB). -/
@[inline] def maxHttpHeaderBytes : Nat := 32768

/-- Maximum HTTP/1.1 request body size in bytes (4 MiB). -/
@[inline] def maxHttpBodyBytes : Nat := 4194304

/-- Parsed zero-copy HTTP/1.1 (or HTTP/1.0) request over a backing `ByteArray`. -/
structure HttpRequest where
  method        : String
  path          : String
  version       : String := "HTTP/1.1"
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
  | 101 => "Switching Protocols"
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
  | 426 => "Upgrade Required"
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

/-- RFC 9110 §5.6.2 `tchar`: `!#$%&'*+-.^_`|~`, `DIGIT`, `ALPHA`. -/
@[inline]
def isHttpTokenByte (b : UInt8) : Bool :=
  (48 ≤ b && b ≤ 57) || (65 ≤ b && b ≤ 90) || (97 ≤ b && b ≤ 122) ||
  b == 33 || b == 35 || b == 36 || b == 37 || b == 38 || b == 39 || b == 42 || b == 43 ||
  b == 45 || b == 46 || b == 94 || b == 95 || b == 96 || b == 124 || b == 126

/-- `true` iff `s` is a non-empty RFC 9110 `token` (valid HTTP field name). -/
def isHttpToken (s : String) : Bool := Id.run do
  let b := s.toUTF8
  if b.isEmpty then return false
  for i in [0:b.size] do
    if !isHttpTokenByte (b.get! i) then return false
  return true

/-- `true` iff `s` contains a control byte forbidden in an HTTP field line (`0x00..0x1F` except `HTAB`, or `0x7F`),
    including bare `CR`/`LF` that downstream parsers may treat as line terminators. -/
def hasHttpFieldControlByte (s : String) : Bool := Id.run do
  let b := s.toUTF8
  for i in [0:b.size] do
    let c := b.get! i
    if (c < 32 && c != 9) || c == 127 then return true
  return false

/-- Inspect raw header lines for framing validity before/during body reads:
    - Rejects `Transfer-Encoding` (`unsupported_transfer_encoding`)
    - Rejects non-digit/negative `Content-Length` (`invalid_content_length`)
    - Rejects any repeated `Content-Length` header, identical or not (`conflicting_content_length`)
    - Rejects repeated `Authorization` headers (`duplicate_authorization`)
    - Rejects non-`token` field names (`invalid_header_name`) and control bytes in field lines (`invalid_header_value`)
    - Enforces `headers.size ≤ 32` (`too_many_headers`) and `contentLen ≤ 4194304` (`payload_too_large`). -/
private def parseValidatedHeaders (hdrLines : List String) :
    Except String (Array (String × String) × Option Nat × Option String) := Id.run do
  let mut headers : Array (String × String) := #[]
  let mut seenContentLen : Option Nat := none
  let mut seenAuthorization := false
  let mut authBearer : Option String := none
  for ln in hdrLines do
    if !ln.isEmpty then
      let lnBytes := ln.toUTF8
      let b0 := if lnBytes.size > 0 then lnBytes.get! 0 else 0
      if b0 == 32 || b0 == 9 then
        return .error "obs_fold_header_rejected"
      if hasHttpFieldControlByte ln then
        return .error "invalid_header_value"
      match ln.splitOn ":" with
      | [] | [_] =>
        return .error "malformed_header_line"
      | k :: rest =>
        if !isHttpToken k then
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
            if seenContentLen.isSome then
              return .error "conflicting_content_length"
            seenContentLen := some parsedLen
        else if asciiEqIgnoreCase kTrim "authorization" then
          if seenAuthorization then
            return .error "duplicate_authorization"
          seenAuthorization := true
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
    if method != "GET" && method != "POST" && method != "HEAD" && method != "PUT" &&
       method != "DELETE" && method != "PATCH" && method != "OPTIONS" then
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
          version := proto
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

/-- Strict HTTP/1.x status line check: `HTTP/1.1 ` or `HTTP/1.0 `, a 3-digit status code, then end or `SP`. -/
def isValidStatusLine (line : String) : Bool :=
  let b := line.toUTF8
  let isDigit (i : Nat) : Bool := let c := b.get! i; 48 ≤ c && c ≤ 57
  (line.startsWith "HTTP/1.1 " || line.startsWith "HTTP/1.0 ") && b.size ≥ 12 &&
    isDigit 9 && isDigit 10 && isDigit 11 && (b.size == 12 || b.get! 12 == 32)

/-- Panic-free UTF-8 decoding of a framed response body (`.error .einval` on invalid UTF-8). -/
def decodeResponseBody (bodyBytes : ByteArray) : SysResult String :=
  match String.fromUTF8? bodyBytes with
  | some s => .ok s
  | none => .error .einval

/-- Perform an HTTP/1.1 client request to `host:port`, looping `pollReadable` + `readStreamChunk`
    until `\r\n\r\n` and all declared `Content-Length` response body bytes arrive (or clean EOF when
    no `Content-Length` is declared). Fails closed on deadline expiry (`.error .eagain`), socket poll
    errors, malformed status line/response framing/headers or non-UTF-8 body (`.error .einval`), an
    undeclared-length body exceeding `maxHttpBodyBytes` (`.error .einval`), or premature EOF before headers
    or declared `Content-Length` (`.error .eio`). Never panics on untrusted response bytes. -/
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
          if let some bStart := hdrEnd? then
            if targetTotal.isNone && respBuf.size - bStart > maxHttpBodyBytes then
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
                        if !isValidStatusLine statusLine then
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
                pure (decodeResponseBody (respBuf.extract bStart tot))
            | none =>
              if respBuf.size - bStart > maxHttpBodyBytes then
                pure (.error .einval)
              else
                pure (decodeResponseBody (respBuf.extract bStart respBuf.size))
    finally
      discard <| closeFd fd


/-! ## `AF_UNIX` HTTP/1.1 Client (`requestUnix`) & Zero-Copy `BorrowedSlice` / `ByteSource` Request Parser -/

/-- Execute an HTTP/1.1 request over an already-connected socket descriptor `fd` (closing `fd` on exit). -/
def httpClientRequestOnFd (fd : Fd) (hostHeader : String) (method : String) (path : String)
    (body : ByteSource) (bearerToken? : Option String := none) (timeoutMs : UInt32 := 3000) :
    IO (SysResult String) := do
  try
    let authHdr := match bearerToken? with
      | some tok => s!"Authorization: Bearer {tok}\r\n"
      | none => ""
    let bodyBytes := body.toByteArray
    let reqHead :=
      s!"{method} {path} HTTP/1.1\r\n" ++
      s!"Host: {hostHeader}\r\n" ++
      "Content-Type: application/json\r\n" ++
      authHdr ++
      s!"Content-Length: {bodyBytes.size}\r\n" ++
      "Connection: close\r\n\r\n"
    let wire := reqHead.toUTF8 ++ bodyBytes
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
        | some tot => if respBuf.size >= tot then break
        | none => pure ()
        if hdrEnd?.isNone && respBuf.size > maxHttpHeaderBytes + 4 then
          ioErr? := some .einval; break
        if let some bStart := hdrEnd? then
          if targetTotal.isNone && respBuf.size - bStart > maxHttpBodyBytes then
            ioErr? := some .einval; break
        let now ← IO.monoNanosNow
        let elapsedMs := (now - t0) / 1000000
        if elapsedMs >= budgetMs then
          ioErr? := some .eagain; break
        match ← pollReadable fd (budgetMs - elapsedMs).toUInt32 with
        | .error e => ioErr? := some e; break
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
                      if !isValidStatusLine statusLine then
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
            if respBuf.size < tot then pure (.error .eio)
            else pure (decodeResponseBody (respBuf.extract bStart tot))
          | none =>
            if respBuf.size - bStart > maxHttpBodyBytes then pure (.error .einval)
            else pure (decodeResponseBody (respBuf.extract bStart respBuf.size))
  finally
    discard <| closeFd fd

/-- Execute a bounded HTTP/1.1 client request over an `AF_UNIX` domain socket (`socketPath`)
    gated by `leansys_verify_unix_path_bounds` (e.g. Docker / Podman / Firecracker / local sidecar IPC). -/
def requestUnix (socketPath : String) (method : String) (path : String)
    (body : ByteSlice := ByteSlice.ofByteArray ByteArray.empty)
    (bearerToken? : Option String := none) (timeoutMs : UInt32 := 3000) :
    IO (SysResult String) := do
  match ← unixConnect socketPath with
  | .error e => pure (.error e)
  | .ok fd => httpClientRequestOnFd fd "localhost" method path (ByteSource.ofByteSlice body) bearerToken? timeoutMs

/-- Zero-copy HTTP/1.1 request envelope whose `bodySource` remains a `ByteSource` (`BorrowedSlice` or `ByteSlice`). -/
structure BorrowedHttpRequest where
  method        : String
  path          : String
  headers       : Array (String × String)
  contentLength : Nat
  authBearer    : Option String
  bodySource    : ByteSource

private def findHeaderEndSource? (src : ByteSource) : Option Nat := Id.run do
  let n := src.size
  if n < 4 then return none
  for i in [0 : n - 3] do
    if src.getByteD i == 13 && src.getByteD (i + 1) == 10 &&
       src.getByteD (i + 2) == 13 && src.getByteD (i + 3) == 10 then
      return some (i + 4)
  return none

/-- Parse a bounded HTTP/1.1 request directly from a `ByteSource` (`BorrowedSlice` or `ByteSlice`)
    without copying the body payload into a `ByteArray`, gated by `leansys_check_http_bounds`. -/
def parseRequestSourcePrefix (src : ByteSource) (expectedBearer? : Option String := none)
    (allowTrailingBytes : Bool := false) : Except String (BorrowedHttpRequest × Nat) := do
  let some bodyStart := findHeaderEndSource? src
    | .error "missing_header_terminator"
  if bodyStart - 4 > maxHttpHeaderBytes then
    .error "headers_too_large"
  let some headSrc := src.subSource? 0 (bodyStart - 4)
    | .error "invalid_header_slice"
  let some headStr := String.fromUTF8? headSrc.toByteArray
    | .error "invalid_utf8_headers"
  match headStr.splitOn "\r\n" with
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
    if method != "GET" && method != "POST" && method != "HEAD" && method != "PUT" &&
       method != "DELETE" && method != "PATCH" && method != "OPTIONS" then
      .error s!"unsupported_method:{method}"
    let (headers, contentLen?, authBearer) ← parseValidatedHeaders hdrLines
    let declContentLen := contentLen?.getD 0
    let availTotalBody := src.size - bodyStart
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
        let some bodySrc := src.subSource? bodyStart declContentLen
          | .error "invalid_body_slice"
        .ok ({
          method := method
          path := path
          headers := headers
          contentLength := declContentLen
          authBearer := authBearer
          bodySource := bodySrc
        }, bodyStart + declContentLen)

/--Incremental non-blocking framing inspection: returns `.ok (some (req, remCarry))` when a full frame has
   arrived in `buf`, `.ok none` when more bytes are still needed without violating header/body caps,
   or `.error reason` when framing/caps/auth fail immediately. -/
def tryParseIncremental (buf : ByteArray) (expectedBearer? : Option String := none) :
    Except String (Option (HttpRequest × ByteArray)) := do
  match findHeaderEnd? buf with
  | none =>
    if buf.size > maxHttpHeaderBytes + 4 then
      .error "headers_too_large"
    else
      .ok none
  | some bStart =>
    if bStart - 4 > maxHttpHeaderBytes then
      .error "headers_too_large"
    else
      let some headStr := String.fromUTF8? (buf.extract 0 (bStart - 4))
        | .error "invalid_utf8_headers"
      match headStr.splitOn "\r\n" with
      | [] => .error "empty_request_line"
      | _ :: hdrLines =>
        let (_, cl?, _) ← parseValidatedHeaders hdrLines
        let declCl := cl?.getD 0
        if declCl > maxHttpBodyBytes then
          .error "payload_too_large"
        else if buf.size < bStart + declCl then
          .ok none
        else
          let (req, consumed) ← parseRequestPrefix buf expectedBearer? true
          let rem := if consumed < buf.size then buf.extract consumed buf.size else ByteArray.empty
          .ok (some (req, rem))

/-! ## Parameterized Route Matching, Query-String Parsing, Chunked Responses & RFC 6455 Upgrade -/

/-- Strip any `?query` suffix from `rawTarget`, returning `(cleanPath, queryString)`. -/
def splitPathAndQuery (rawTarget : String) : String × String :=
  match rawTarget.splitOn "?" with
  | [] => ("", "")
  | [onlyPath] => (onlyPath, "")
  | p :: rest => (p, String.intercalate "?" rest)

@[inline]
private def pctNib? (b : UInt8) : Option UInt8 :=
  if 48 ≤ b && b ≤ 57 then some (b - 48)
  else if 65 ≤ b && b ≤ 70 then some (b - 55)
  else if 97 ≤ b && b ≤ 102 then some (b - 87)
  else none

/-- Percent-decode a URL query or path component (`%XX` and `+` → `' '` when `plusAsSpace := true`). -/
def percentDecode (s : String) (plusAsSpace : Bool := false) : String := Id.run do
  let b := s.toUTF8
  let mut out := ByteArray.emptyWithCapacity b.size
  let mut i : Nat := 0
  while i < b.size do
    let c := b.get! i
    if c == 37 && i + 2 < b.size then -- '%'
      match pctNib? (b.get! (i + 1)), pctNib? (b.get! (i + 2)) with
      | some hi, some lo =>
        out := out.push ((hi <<< 4) ||| lo)
        i := i + 3
      | _, _ =>
        out := out.push c
        i := i + 1
    else if plusAsSpace && c == 43 then -- '+'
      out := out.push 32
      i := i + 1
    else
      out := out.push c
      i := i + 1
  return String.fromUTF8? out |>.getD s

/-- Parse a URL query string (`a=1&b=hello%20world`, leading `?a=1`, or `/path?a=1`) into `(key, value)` pairs (bounded `≤ 64` params),
    preserving literal `?` characters inside raw query values (`q=what?ever&limit=2`). -/
def parseQueryParams (rawQueryOrTarget : String) : Array (String × String) := Id.run do
  let q :=
    if rawQueryOrTarget.startsWith "/" then
      (splitPathAndQuery rawQueryOrTarget).2
    else if rawQueryOrTarget.startsWith "?" then
      (rawQueryOrTarget.drop 1).toString
    else
      rawQueryOrTarget
  if q.isEmpty then return #[]
  let parts := q.splitOn "&"
  let mut out : Array (String × String) := #[]
  for part in parts do
    if verifySliceBounds out.size.toUInt64 1 64 != 1 then break
    if !part.isEmpty then
      match part.splitOn "=" with
      | [] => pure ()
      | [kOnly] => out := out.push (percentDecode kOnly true, "")
      | k :: rest => out := out.push (percentDecode k true, percentDecode (String.intercalate "=" rest) true)
  return out

/-- Match a request path against a parameterized route pattern (e.g. `"/api/missions/:id/events"`),
    ignoring any `?query` suffix and rejecting empty or `..` traversal parameter segments.
    Returns `some #[("id", "m-123")]` on match, or `none` on mismatch. -/
def matchRoutePattern? (pattern : String) (reqTarget : String) : Option (Array (String × String)) := Id.run do
  let (cleanPath, _) := splitPathAndQuery reqTarget
  let patSegs := (pattern.splitOn "/").filter (!·.isEmpty)
  let reqSegs := (cleanPath.splitOn "/").filter (!·.isEmpty)
  if patSegs.length != reqSegs.length then
    return none
  let mut params : Array (String × String) := #[]
  let mut pairs := patSegs.zip reqSegs
  while !pairs.isEmpty do
    match pairs with
    | [] => break
    | (pSeg, rSeg) :: rest =>
      pairs := rest
      if pSeg.startsWith ":" then
        let pName := (pSeg.drop 1).toString
        let decoded := percentDecode rSeg false
        if pName.isEmpty || decoded.isEmpty || decoded == "." || decoded == ".." ||
           (decoded.splitOn "/").length > 1 then
          return none
        params := params.push (pName, decoded)
      else if pSeg != rSeg then
        return none
  return some params

/-- Case-insensitive lookup of a single header value on `HttpRequest`. -/
def HttpRequest.findHeader? (req : HttpRequest) (name : String) : Option String := Id.run do
  for (k, v) in req.headers do
    if asciiEqIgnoreCase k name then
      return some v
  return none

/-- Encode a single HTTP/1.1 `Transfer-Encoding: chunked` body chunk (`<hexLen>\r\n<bytes>\r\n`),
    or the terminal `0\r\n\r\n` chunk when `chunk.isEmpty`. -/
def encodeHttpChunk (chunk : ByteSlice) : ByteArray :=
  if chunk.len == 0 then
    "0\r\n\r\n".toUTF8
  else
    let hexChars := "0123456789abcdef".toUTF8
    let hexStr : String := Id.run do
      let mut n := chunk.len
      let mut rev : List UInt8 := []
      while n > 0 do
        rev := hexChars.get! (n &&& 0xF) :: rev
        n := n >>> 4
      String.fromUTF8! (ByteArray.mk rev.toArray)
    (hexStr ++ "\r\n").toUTF8 ++ chunk.toByteArray ++ "\r\n".toUTF8

/-- Decode a complete HTTP/1.1 `Transfer-Encoding: chunked` response body (rejecting chunks exceeding `maxBytes`). -/
def decodeChunkedBody? (raw : ByteArray) (maxBytes : Nat := maxHttpBodyBytes) : Option ByteArray := Id.run do
  let mut p : Nat := 0
  let mut out := ByteArray.empty
  while p < raw.size do
    let mut crlf : Option Nat := none
    for i in [p : raw.size - 1] do
      if raw.get! i == 13 && raw.get! (i + 1) == 10 then
        crlf := some i
        break
    let some lineEnd := crlf | return none
    if lineEnd == p || verifySliceBounds 0 (lineEnd - p).toUInt64 64 != 1 then return none
    -- Parse hex chunk size (ignoring optional `;chunk-ext`)
    let mut chunkLen : Nat := 0
    let mut digitsSeen := false
    for i in [p : lineEnd] do
      let b := raw.get! i
      if b == 59 then break -- ';'
      match pctNib? b with
      | some nib =>
        digitsSeen := true
        chunkLen := (chunkLen <<< 4) + nib.toNat
        if verifySliceBounds 0 chunkLen.toUInt64 maxBytes.toUInt64 != 1 then return none
      | none => return none
    if !digitsSeen then return none
    p := lineEnd + 2
    if chunkLen == 0 then
      -- RFC 9112 §7.1.3: consume optional trailer lines up to terminating empty `\r\n`
      let mut tp := p
      let mut trailerLines : Nat := 0
      while tp + 1 < raw.size do
        if raw.get! tp == 13 && raw.get! (tp + 1) == 10 then
          return some out
        if verifySliceBounds trailerLines.toUInt64 1 64 != 1 then
          return none
        let mut tEnd : Option Nat := none
        for j in [tp : raw.size - 1] do
          if raw.get! j == 13 && raw.get! (j + 1) == 10 then
            tEnd := some j
            break
        let some te := tEnd | return none
        if verifySliceBounds 0 (te - tp).toUInt64 8192 != 1 then return none
        -- Require colon inside trailer header field and no bare control bytes
        let mut colonAt : Option Nat := none
        for j in [tp : te] do
          let b := raw.get! j
          if b == 58 && colonAt.isNone then colonAt := some j
          if b < 0x20 && b != 9 then return none
        let some cIdx := colonAt | return none
        if cIdx == tp then return none
        trailerLines := trailerLines + 1
        tp := te + 2
      return none
    if verifySliceBounds out.size.toUInt64 chunkLen.toUInt64 maxBytes.toUInt64 != 1 ||
       verifySliceBounds p.toUInt64 (chunkLen + 2).toUInt64 raw.size.toUInt64 != 1 then
      return none
    if raw.get! (p + chunkLen) != 13 || raw.get! (p + chunkLen + 1) != 10 then
      return none
    out := out ++ raw.extract p (p + chunkLen)
    p := p + chunkLen + 2
  return none

/-- Check whether a comma-separated HTTP header value contains case-insensitive token `needle`. -/
private def headerContainsTokenCI (hdrVal : String) (needle : String) : Bool := Id.run do
  for part in hdrVal.splitOn "," do
    if asciiEqIgnoreCase part.trimAscii.toString needle then
      return true
  return false

/-- Validate an incoming RFC 6455 §4.2.1 `Sec-WebSocket-Key` (24-char Base64 encoding of a 16-byte nonce ending in `==`). -/
private def isValidSecWebSocketKey (k : String) : Bool := Id.run do
  let b := k.toUTF8
  if b.size != 24 then return false
  if b.get! 22 != 61 || b.get! 23 != 61 then return false
  let isB64 (c : UInt8) : Bool :=
    (65 ≤ c && c ≤ 90) || (97 ≤ c && c ≤ 122) || (48 ≤ c && c ≤ 57) || c == 43 || c == 47
  for i in [0:22] do
    if !isB64 (b.get! i) then return false
  -- 22nd Base64 char encodes 2 payload bits + 4 zero padding bits (`A`, `Q`, `g`, `w`)
  let c21 := b.get! 21
  return c21 == 65 || c21 == 81 || c21 == 103 || c21 == 119

/-- Validate an incoming HTTP/1.1 RFC 6455 WebSocket upgrade request (`GET`, `Connection: Upgrade`,
    `Upgrade: websocket`, `Sec-WebSocket-Version: 13`, valid 16-byte Base64 `Sec-WebSocket-Key`,
    no duplicate singleton handshake headers, and offered `Sec-WebSocket-Protocol` match)
    and build the `101 Switching Protocols` wire response. -/
def buildWebSocketUpgradeResponse? (req : HttpRequest) (protocol? : Option String := none) : Option ByteArray := do
  if req.method != "GET" || req.version != "HTTP/1.1" then none
  -- Reject duplicate singleton WebSocket handshake headers
  let mut keyCount : Nat := 0
  let mut verCount : Nat := 0
  let mut connUpgrade := false
  let mut upgWebsocket := false
  let mut offeredProtos : Array String := #[]
  for (hk, hv) in req.headers do
    if asciiEqIgnoreCase hk "sec-websocket-key" then keyCount := keyCount + 1
    else if asciiEqIgnoreCase hk "sec-websocket-version" then verCount := verCount + 1
    else if asciiEqIgnoreCase hk "connection" then
      if headerContainsTokenCI hv "upgrade" then connUpgrade := true
    else if asciiEqIgnoreCase hk "upgrade" then
      if headerContainsTokenCI hv "websocket" then upgWebsocket := true
    else if asciiEqIgnoreCase hk "sec-websocket-protocol" then
      for pTok in hv.splitOn "," do
        let t := pTok.trimAscii.toString
        if !t.isEmpty then offeredProtos := offeredProtos.push t
  if !connUpgrade || !upgWebsocket || keyCount != 1 || verCount != 1 then none
  let ver ← req.findHeader? "sec-websocket-version"
  if ver.trimAscii.toString != "13" then none
  let wsKey ← req.findHeader? "sec-websocket-key"
  let keyTrim := wsKey.trimAscii.toString
  if !isValidSecWebSocketKey keyTrim || hasHttpFieldControlByte keyTrim then none
  let acceptVal := LeanSys.WebSocket.computeAcceptKey keyTrim
  let protoHdr ← match protocol? with
    | none => some ""
    | some pr =>
      if pr.isEmpty || !isHttpToken pr || !offeredProtos.contains pr then none
      else some s!"Sec-WebSocket-Protocol: {pr}\r\n"
  some (
    "HTTP/1.1 101 Switching Protocols\r\n" ++
    "Upgrade: websocket\r\n" ++
    "Connection: Upgrade\r\n" ++
    s!"Sec-WebSocket-Accept: {acceptVal}\r\n" ++
    protoHdr ++
    "\r\n"
  ).toUTF8

end LeanSys.Http
