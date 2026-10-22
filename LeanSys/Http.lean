/-
  LeanSys.Http: Zero-Copy Bounded HTTP/1.1 Parser, Server Loop, and Client POST
  (`0 import Lean`, `0 sorryAx`)
  - Zero-copy header & body parser over `ByteSlice` (`maxHeaders ≤ 32`, `maxBody ≤ 4 MiB`)
  - Gated by `LeanSys.Spec.checkHttpBounds` (`leansys_check_http_bounds`)
  - Supports `GET`, `POST`, `Authorization: Bearer ...`, and `Content-Length`
-/
import LeanSys.Spec
import LeanSys.Posix

namespace LeanSys.Http

open LeanSys.Spec
open LeanSys.Posix

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

/-- Serialize an `HttpResponse` into an HTTP/1.1 wire `ByteArray`. -/
def toWireBytes (r : HttpResponse) : ByteArray :=
  let statusText := match r.status with
    | 200 => "OK"
    | 400 => "Bad Request"
    | 401 => "Unauthorized"
    | 404 => "Not Found"
    | 413 => "Payload Too Large"
    | _   => "OK"
  let head :=
    s!"HTTP/1.1 {r.status} {statusText}\r\n" ++
    s!"Content-Type: {r.contentType}\r\n" ++
    s!"Content-Length: {r.body.size}\r\n" ++
    "Connection: close\r\n\r\n"
  head.toUTF8 ++ r.body

end HttpResponse

/-- Find the index of `\r\n\r\n` (`13, 10, 13, 10`) in `ba`, returning the byte offset of the body start. -/
def findHeaderEnd? (ba : ByteArray) : Option Nat := Id.run do
  if ba.size < 4 then return none
  let limit := ba.size - 3
  for i in [0:limit] do
    if ba.get! i == 13 && ba.get! (i + 1) == 10 &&
       ba.get! (i + 2) == 13 && ba.get! (i + 3) == 10 then
      return some (i + 4)
  return none

/-- Parse a decimal `Nat` from an ASCII string (returns `0` if empty or non-numeric). -/
def parseNatAscii (s : String) : Nat := Id.run do
  let bytes := s.trimAscii.toString.toUTF8
  let mut acc : Nat := 0
  for i in [0:bytes.size] do
    let b := bytes.get! i
    if 48 ≤ b && b ≤ 57 then
      acc := acc * 10 + (b - 48).toNat
  return acc

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

/--
  Zero-copy bounded HTTP/1.1 request parser over `raw : ByteArray`, gated by `leansys_check_http_bounds`.
  If `expectedBearer?` is `some tok`, enforces `Authorization: Bearer <tok>` through `authOk` in C-ABI.
-/
def parseRequest (raw : ByteArray) (expectedBearer? : Option String := none) : Except String HttpRequest := do
  let some bodyStart := findHeaderEnd? raw
    | .error "missing_header_terminator"
  let rootSlice := ByteSlice.ofByteArray raw
  let some headSlice := ByteSlice.subSlice? rootSlice 0 (bodyStart - 4)
    | .error "invalid_header_slice"
  let headStr := headSlice.toStringLossy
  let lines := headStr.splitOn "\r\n"
  match lines with
  | [] => .error "empty_request_line"
  | reqLine :: hdrLines =>
    let parts := reqLine.trimAscii.toString.splitOn " "
    let (method, path) ← match parts with
      | m :: p :: _ => .ok (m.trimAscii.toString, p.trimAscii.toString)
      | _ => .error "malformed_request_line"
    if method != "GET" && method != "POST" then
      .error s!"unsupported_method:{method}"
    else
      let mut headers : Array (String × String) := #[]
      let mut contentLen : Nat := 0
      let mut authBearer : Option String := none
      for ln in hdrLines do
        let t := ln.trimAscii.toString
        if !t.isEmpty then
          match t.splitOn ":" with
          | k :: rest =>
            let kTrim := k.trimAscii.toString
            let vTrim := (String.intercalate ":" rest).trimAscii.toString
            headers := headers.push (kTrim, vTrim)
            if asciiEqIgnoreCase kTrim "content-length" then
              contentLen := parseNatAscii vTrim
            else if asciiEqIgnoreCase kTrim "authorization" then
              if vTrim.startsWith "Bearer " then
                authBearer := some (vTrim.drop 7).trimAscii.toString
          | [] => pure ()
      let availBody := raw.size - bodyStart
      let effContentLen := if method == "GET" && contentLen == 0 then availBody else contentLen
      let authOk : UInt8 := match expectedBearer? with
        | none => 1
        | some reqTok => if authBearer == some reqTok then 1 else 0
      if checkHttpBounds headers.size.toUInt32 effContentLen.toUInt64 availBody.toUInt64 authOk != 1 then
        if authOk == 0 then .error "unauthorized_bearer_token"
        else if headers.size > 32 then .error "too_many_headers"
        else if effContentLen > 4194304 then .error "payload_too_large"
        else .error "content_length_mismatch"
      else
        let some bodySlice := ByteSlice.subSlice? rootSlice bodyStart effContentLen
          | .error "invalid_body_slice"
        .ok {
          method := method
          path := path
          headers := headers
          contentLength := effContentLen
          authBearer := authBearer
          bodySlice := bodySlice
        }

/-- Read an entire bounded HTTP/1.1 request from a connected socket `fd` (handling multi-chunk body reads up to `Content-Length`). -/
def readHttpRequestFromFd (fd : Fd) (expectedBearer? : Option String := none) : IO (Except String HttpRequest) := do
  let mut buf ← readStreamChunk fd 65536
  if buf.isEmpty then
    return .error "empty_socket_read"
  let mut tries := 0
  while (findHeaderEnd? buf).isNone && tries < 16 && buf.size < 65536 do
    let more ← readStreamChunk fd 16384
    if more.isEmpty then break
    buf := buf ++ more
    tries := tries + 1
  let some bodyStart := findHeaderEnd? buf
    | return .error "missing_header_terminator"
  -- Check if we need more body bytes based on Content-Length
  let headStr := String.fromUTF8! (buf.extract 0 (bodyStart - 4))
  let mut expectedBody := 0
  for ln in headStr.splitOn "\r\n" do
    match ln.splitOn ":" with
    | k :: rest =>
      if asciiEqIgnoreCase k "content-length" then
        expectedBody := parseNatAscii (String.intercalate ":" rest)
    | [] => pure ()
  let mut bodyTries := 0
  while buf.size - bodyStart < expectedBody && expectedBody ≤ 4194304 && bodyTries < 256 do
    let rem := expectedBody - (buf.size - bodyStart)
    let chunk ← readStreamChunk fd (Nat.min rem 65536)
    if chunk.isEmpty then break
    buf := buf ++ chunk
    bodyTries := bodyTries + 1
  return parseRequest buf expectedBearer?

/-- Handle a single accepted client socket connection and close `clientFd` deterministically. -/
def serveSingleConnection (clientFd : Fd) (expectedBearer? : Option String)
    (handler : HttpRequest → IO HttpResponse) : IO Unit := do
  try
    let resp ← match ← readHttpRequestFromFd clientFd expectedBearer? with
      | .ok req => handler req
      | .error errMsg =>
        let code := if errMsg == "unauthorized_bearer_token" then 401 else 400
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
      serveSingleConnection clientFd expectedBearer? handler
      served := served + 1
    | .error .eagain =>
      if maxRequests > 0 then break
    | .error _ =>
      if maxRequests > 0 then break

/-- Perform an HTTP/1.1 client `POST` (or `GET`) request to `host:port` and return the response body string. -/
def httpClientRequest (host : String) (port : UInt16) (method : String) (path : String)
    (body : ByteSlice) (bearerToken? : Option String := none) : IO (SysResult String) := do
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
        let mut respBuf := ByteArray.empty
        for _ in [0:64] do
          let chunk ← readStreamChunk fd 65536
          if chunk.isEmpty then break
          respBuf := respBuf ++ chunk
        match findHeaderEnd? respBuf with
        | some bStart =>
          let bodyBytes := respBuf.extract bStart respBuf.size
          pure (.ok (String.fromUTF8! bodyBytes))
        | none =>
          pure (.ok (String.fromUTF8! respBuf))
    finally
      discard <| closeFd fd

end LeanSys.Http
