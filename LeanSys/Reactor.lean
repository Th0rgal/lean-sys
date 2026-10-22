/-
  LeanSys.Reactor: Non-Blocking Poll Reactor & HTTP/1.1 Keep-Alive Multiplexer
  (`0 import Lean`, `0 sorryAx`)
  - Gated by `LeanSys.Spec.verifyPollInterest` (`leansys_verify_poll_interest`)
  - Supports multi-request HTTP/1.1 Keep-Alive connection reuse and admission control
-/
import LeanSys.Spec
import LeanSys.Posix
import LeanSys.Http

namespace LeanSys.Reactor

open LeanSys.Spec
open LeanSys.Posix
open LeanSys.Http

/-- Reactor configuration for multiplexed & keep-alive connections. -/
structure ReactorConfig where
  maxConns        : UInt32 := 128
  maxKeepAliveReq : UInt32 := 64
  maxIdleMs       : UInt32 := 2000
  expectedBearer? : Option String := none

/-- Serialize an `HttpResponse` with configurable `Connection: keep-alive` or `close`. -/
def toKeepAliveWireBytes (r : HttpResponse) (keepAlive : Bool) : ByteArray :=
  let statusText := match r.status with
    | 200 => "OK"
    | 400 => "Bad Request"
    | 401 => "Unauthorized"
    | 404 => "Not Found"
    | 413 => "Payload Too Large"
    | _   => "OK"
  let connHdr := if keepAlive then "keep-alive" else "close"
  let head :=
    s!"HTTP/1.1 {r.status} {statusText}\r\n" ++
    s!"Content-Type: {r.contentType}\r\n" ++
    s!"Content-Length: {r.body.size}\r\n" ++
    s!"Connection: {connHdr}\r\n\r\n"
  head.toUTF8 ++ r.body

/-- Serve a keep-alive HTTP/1.1 session on `clientFd`, gated on every request by `leansys_verify_poll_interest`. -/
def serveKeepAliveSession (cfg : ReactorConfig) (activeConns : UInt32) (clientFd : Fd)
    (handler : HttpRequest → IO HttpResponse) : IO Nat := do
  let mut reqsServed : Nat := 0
  try
    let mut keepGoing := true
    while keepGoing do
      if verifyPollInterest activeConns cfg.maxConns reqsServed.toUInt32 cfg.maxKeepAliveReq 0 cfg.maxIdleMs != 1 then
        break
      match ← readHttpRequestFromFd clientFd cfg.expectedBearer? with
      | .error _ =>
        keepGoing := false
      | .ok req =>
        reqsServed := reqsServed + 1
        let wantsClose := req.headers.any (fun (k, v) =>
          asciiEqIgnoreCase k "connection" && asciiEqIgnoreCase v "close")
        let canKeepAlive := !wantsClose &&
          verifyPollInterest activeConns cfg.maxConns reqsServed.toUInt32 cfg.maxKeepAliveReq 0 cfg.maxIdleMs == 1
        let resp ← handler req
        discard <| writeAll clientFd (toKeepAliveWireBytes resp canKeepAlive) false
        if !canKeepAlive then
          keepGoing := false
  finally
    discard <| closeFd clientFd
  return reqsServed

/-- Run the non-blocking poll reactor loop for up to `maxSessions` client connections. -/
def runReactorLoop (cfg : ReactorConfig) (listenFd : Fd) (maxSessions : Nat := 1)
    (handler : HttpRequest → IO HttpResponse) : IO Nat := do
  let mut totalReqs : Nat := 0
  let mut sessions : Nat := 0
  while sessions < maxSessions do
    match ← tcpAcceptPoll listenFd cfg.maxIdleMs with
    | .ok clientFd =>
      let n ← serveKeepAliveSession cfg 1 clientFd handler
      totalReqs := totalReqs + n
      sessions := sessions + 1
    | .error _ =>
      break
  return totalReqs

end LeanSys.Reactor
