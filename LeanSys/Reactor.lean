/-
  LeanSys.Reactor: Non-Blocking Poll Reactor & Pipelined HTTP/1.1 Keep-Alive Multiplexer
  (`0 import Lean`, `0 sorryAx`)
  - Gated by `LeanSys.Spec.verifyPollInterest` (`leansys_verify_poll_interest`)
  - Supports multi-request HTTP/1.1 Keep-Alive connection reuse, pipelined carryover buffering
    across consecutive requests on the same socket, and explicit error responses (`400`/`401`/`413`/`431`)
    before closing malformed or unauthorized sessions.
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
  let statusText := HttpResponse.reasonPhrase r.status
  let connHdr := if keepAlive then "keep-alive" else "close"
  let head :=
    s!"HTTP/1.1 {r.status} {statusText}\r\n" ++
    s!"Content-Type: {r.contentType}\r\n" ++
    s!"Content-Length: {r.body.size}\r\n" ++
    s!"Connection: {connHdr}\r\n\r\n"
  head.toUTF8 ++ r.body

/-- Serve a keep-alive HTTP/1.1 session on `clientFd`, preserving pipelined `carry` bytes across requests
    and gating every request via `leansys_verify_poll_interest`. -/
def serveKeepAliveSession (cfg : ReactorConfig) (activeConns : UInt32) (clientFd : Fd)
    (handler : HttpRequest → IO HttpResponse) : IO Nat := do
  let mut reqsServed : Nat := 0
  let mut carry := ByteArray.empty
  try
    let mut keepGoing := true
    while keepGoing do
      if verifyPollInterest activeConns cfg.maxConns reqsServed.toUInt32 cfg.maxKeepAliveReq 0 cfg.maxIdleMs != 1 then
        break
      match ← readHttpRequestStream clientFd carry cfg.expectedBearer? cfg.maxIdleMs with
      | .error errMsg =>
        if errMsg != "empty_socket_read" then
          let code := statusForParseError errMsg
          let errResp := HttpResponse.json code s!"\{\"ok\":false,\"error\":\"{errMsg}\"}"
          discard <| writeAll clientFd (toKeepAliveWireBytes errResp false) false
        keepGoing := false
      | .ok (req, nextCarry) =>
        carry := nextCarry
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


/-! ## Layer I `StepReactor` Runtime Driver & Multi-FD Non-Blocking Event Multiplexer -/

/-- Inbound event delivered to a pure `StepReactorSpec` state machine. -/
inductive ReactorEvent (Msg : Type) where
  | message (epoch : UInt64) (dedupKey : UInt64) (cost : UInt64) (payload : Msg)
  | tick (nowMs : UInt64)
  | childExited (pid : UInt32) (exitCode : UInt32)
  deriving Repr

/-- Outbound side-effect command emitted by a pure `StepReactorSpec` step. -/
inductive ReactorEffect (Out : Type) where
  | emitOutput (payload : Out)
  | appendWal (key : String) (val : ByteArray)
  | rejectTransition (reason : String)

/-- Governed state wrapper composing monotonic fencing epoch (`LinearLeaseSpec`), bounded outbox dedup ring
    (`IdempotentOutboxSpec`), and resource quota accounting (`QuotaCircuitSpec`) gated by `leansys_verify_step_reactor`. -/
structure GovernedReactorState (S : Type) where
  minEpoch    : UInt64 := 0
  usedQuota   : UInt64 := 0
  quotaCap    : UInt64 := 1048576
  activeConns : UInt32 := 0
  maxConns    : UInt32 := 62
  seenKeys    : Array UInt64 := #[]
  appState    : S

/-- Execute one pure deterministic `GovernedReactorState` step gated by `leansys_verify_step_reactor`. -/
def stepGoverned (st : GovernedReactorState S) (ev : ReactorEvent Msg)
    (onMsg : S → Msg → S × Array Out) : GovernedReactorState S × Array (ReactorEffect Out) :=
  match ev with
  | .tick _ => (st, #[])
  | .childExited _ _ => (st, #[])
  | .message epoch dedupKey cost msg =>
    let seen : UInt8 := if st.seenKeys.contains dedupKey then 1 else 0
    let nextUsed := st.usedQuota + cost
    if nextUsed < st.usedQuota ||
       verifyStepReactor epoch st.minEpoch nextUsed st.quotaCap st.activeConns st.maxConns seen != 1 then
      (st, #[.rejectTransition "step_reactor_gate_rejected"])
    else
      let (s', outs) := onMsg st.appState msg
      let nextSeen := if st.seenKeys.size >= 256 then (st.seenKeys.extract 1 st.seenKeys.size).push dedupKey else st.seenKeys.push dedupKey
      let st' : GovernedReactorState S := {
        st with
        minEpoch := epoch
        usedQuota := nextUsed
        seenKeys := nextSeen
        appState := s'
      }
      (st', outs.map ReactorEffect.emitOutput)

/-- Per-connection non-blocking HTTP/1.1 state machine inside the multi-FD `pollFdSet` multiplexer. -/
private structure ConnSlot where
  fd         : Fd
  rxBuf      : ByteArray := ByteArray.empty
  txBuf      : ByteArray := ByteArray.empty
  txOff      : Nat := 0
  reqsServed : Nat := 0
  closeAfter : Bool := false
  openedMs   : UInt64 := 0
  deriving Inhabited

/-- True non-blocking multi-FD `poll(2)` HTTP/1.1 Keep-Alive + subprocess multiplexer (`runMultiplexedReactor`):
    Simultaneously multiplexes `listenFd` + up to `61` concurrent non-blocking Keep-Alive client connections
    AND optional non-blocking `ChildGroup` reaping (`waitOrKillGroup _ 0 true`), so a slow client stalling mid-header
    never blocks sibling connections on the same thread. Every connection admission and request step is gated by
    `leansys_verify_poll_interest` and `leansys_verify_step_reactor`, and cleanup (`try ... finally`) closes all
    accepted sockets and kills/reaps remaining watched subprocesses even if `handler` throws or `maxLoopMs` expires. -/
def runMultiplexedReactor (cfg : ReactorConfig) (listenFd : Fd)
    (targetRequests : Nat) (handler : HttpRequest → IO HttpResponse)
    (watchedChildren : Array ChildGroup := #[])
    (maxLoopMs : UInt64 := 5000) : IO (Nat × Array (UInt32 × UInt32)) := do
  discard <| setNonBlocking listenFd true
  let capConns := Nat.min 61 cfg.maxConns.toNat
  let tStart ← IO.monoNanosNow
  let slotsRef ← IO.mkRef (#[] : Array ConnSlot)
  let completedRef ← IO.mkRef (0 : Nat)
  let reapedRef ← IO.mkRef (#[] : Array (UInt32 × UInt32))
  let pendingRef ← IO.mkRef watchedChildren

  try
    while (← completedRef.get) < targetRequests || !(← slotsRef.get).isEmpty || !(← pendingRef.get).isEmpty do
      let nowNs ← IO.monoNanosNow
      let elapsedMs : UInt64 := ((nowNs - tStart) / 1000000).toUInt64
      if elapsedMs > maxLoopMs then
        break
      if (← completedRef.get) >= targetRequests && (← slotsRef.get).isEmpty && (← pendingRef.get).isEmpty then
        break

      -- Poll any watched subprocess groups without blocking (`WNOHANG`)
      let curPending ← pendingRef.get
      let mut stillRunning : Array ChildGroup := #[]
      for cg in curPending do
        match ← waitOrKillGroup cg 0 true with
        | .ok (some code) => reapedRef.modify (·.push (cg.pid, code))
        | .ok none => stillRunning := stillRunning.push cg
        | .error .eintr => stillRunning := stillRunning.push cg
        | .error _ => pure ()
      pendingRef.set stillRunning

      if (← completedRef.get) >= targetRequests && (← slotsRef.get).isEmpty && (← pendingRef.get).isEmpty then
        break

      -- Build multi-FD poll array: index 0 is `listenFd` (while accepting), indices `1..slots.size` are client FDs
      let mut slots ← slotsRef.get
      let mut pollFds : Array Fd := #[listenFd]
      let mut outMask : UInt64 := 0
      for i in [0:slots.size] do
        let s := slots[i]!
        pollFds := pollFds.push s.fd
        if s.txOff < s.txBuf.size then
          outMask := outMask ||| ((1 : UInt64) <<< (i + 1).toUInt64)

      let sliceTimeout : UInt32 := if (← pendingRef.get).isEmpty then 25 else 5
      let readyIdxs ← match ← pollFdSet pollFds sliceTimeout outMask with
        | .ok r => pure r
        | .error _ => pure #[]

      -- 1. Accept any ready incoming connections on `listenFd` (slot 0)
      if readyIdxs.contains 0 && slots.size < capConns && (← completedRef.get) < targetRequests then
        let mut acceptMore := true
        while acceptMore && slots.size < capConns do
          match ← tcpAcceptPoll listenFd 0 with
          | .ok cfd =>
            if verifyPollInterest (slots.size + 1).toUInt32 cfg.maxConns 0 cfg.maxKeepAliveReq 0 cfg.maxIdleMs == 1 then
              discard <| setNonBlocking cfd true
              slots := slots.push { fd := cfd, openedMs := elapsedMs }
              slotsRef.set slots
            else
              discard <| closeFd cfd
              acceptMore := false
          | .error _ =>
            acceptMore := false

      -- 2. Advance every active client connection state machine without blocking.
      -- Keep `slotsRef` synchronized with the exact live open descriptors before every `handler` call and on `closeFd`,
      -- so exception cleanup (`finally`) never closes an already-dropped (and potentially reused) descriptor.
      let mut nextSlots : Array ConnSlot := #[]
      for idx in [0:slots.size] do
        let mut s := slots[idx]!
        let mut dropConn := false
        let idleAge : UInt32 := (elapsedMs - s.openedMs).toUInt32
        if idleAge > cfg.maxIdleMs then
          dropConn := true
        else if readyIdxs.contains (idx + 1) then
          if s.txOff >= s.txBuf.size && !s.closeAfter then
            let chunk ← readStreamChunk s.fd 16384
            if chunk.isEmpty then
              -- Either EOF or EAGAIN on non-blocking socket; if poll reported ready with 0 bytes, peer closed or stalled
              if s.rxBuf.isEmpty then
                dropConn := true
            else
              s := { s with rxBuf := if s.rxBuf.isEmpty then chunk else s.rxBuf ++ chunk, openedMs := elapsedMs }

          -- Drain all complete pipelined frames already buffered in `s.rxBuf`
          let mut parseLoop := !dropConn && !s.closeAfter && !s.rxBuf.isEmpty
          while parseLoop do
            match tryParseIncremental s.rxBuf cfg.expectedBearer? with
            | .error errMsg =>
              let code := statusForParseError errMsg
              let errResp := HttpResponse.json code s!"\{\"ok\":false,\"error\":\"{errMsg}\"}"
              let remTx := if s.txOff == 0 then s.txBuf else s.txBuf.extract s.txOff s.txBuf.size
              s := { s with rxBuf := ByteArray.empty, txBuf := remTx ++ toKeepAliveWireBytes errResp false, txOff := 0, closeAfter := true }
              parseLoop := false
            | .ok none =>
              parseLoop := false
            | .ok (some (req, rem)) =>
              let nextReqs := s.reqsServed + 1
              if verifyStepReactor 1 1 nextReqs.toUInt64 cfg.maxKeepAliveReq.toUInt64 (nextSlots.size + (slots.size - idx)).toUInt32 cfg.maxConns 0 != 1 then
                dropConn := true
                parseLoop := false
              else
                let wantsClose := req.headers.any fun (k, v) =>
                  asciiEqIgnoreCase k "connection" && asciiEqIgnoreCase v "close"
                let activeCount := (nextSlots.size + (slots.size - idx)).toUInt32
                let canKeep := !wantsClose &&
                  verifyPollInterest activeCount cfg.maxConns nextReqs.toUInt32 cfg.maxKeepAliveReq 0 cfg.maxIdleMs == 1
                slotsRef.set ((nextSlots.push s) ++ slots.extract (idx + 1) slots.size)
                let resp ← handler req
                completedRef.modify (· + 1)
                let remTx := if s.txOff == 0 then s.txBuf else s.txBuf.extract s.txOff s.txBuf.size
                s := {
                  s with
                  rxBuf := rem
                  txBuf := remTx ++ toKeepAliveWireBytes resp canKeep
                  txOff := 0
                  reqsServed := nextReqs
                  closeAfter := !canKeep
                  openedMs := elapsedMs
                }
                if !canKeep || rem.isEmpty then
                  parseLoop := false

        -- Flush outbound response slice `[s.txOff, s.txBuf.size)` via partial-write cursor tracking (`writeSlicePartial`)
        if !dropConn && s.txOff < s.txBuf.size then
          let pendingSlice : ByteSlice := { ba := s.txBuf, off := s.txOff, len := s.txBuf.size - s.txOff }
          match ← writeSlicePartial s.fd pendingSlice with
          | .ok sent =>
            let newOff := s.txOff + sent
            if newOff >= s.txBuf.size then
              s := { s with txBuf := ByteArray.empty, txOff := 0 }
              if s.closeAfter then
                dropConn := true
            else
              s := { s with txOff := newOff, openedMs := elapsedMs }
          | .error .eagain => pure ()
          | .error _ => dropConn := true

        if dropConn then
          slotsRef.set (nextSlots ++ slots.extract (idx + 1) slots.size)
          discard <| closeFd s.fd
        else
          nextSlots := nextSlots.push s
      slotsRef.set nextSlots
  finally
    let leftoverSlots ← slotsRef.get
    slotsRef.set #[]
    for s in leftoverSlots do
      discard <| closeFd s.fd
    let leftoverChildren ← pendingRef.get
    pendingRef.set #[]
    for cg in leftoverChildren do
      match ← waitOrKillGroup cg 9 false with
      | .ok (some code) => reapedRef.modify (·.push (cg.pid, code))
      | _ => pure ()
    discard <| setNonBlocking listenFd false

  return (← completedRef.get, ← reapedRef.get)

end LeanSys.Reactor
