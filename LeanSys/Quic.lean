/-
  LeanSys.Quic: Pure-Lean Sans-I/O RFC 9000 QUIC Varint, Packet Header, RFC 6479 Sliding-Window Anti-Replay & Flow-Control Engine (`0 import Lean`, `0 sorryAx`)
  Every inbound packet admission and stream/connection flow-control update is gated by
  `leansys_verify_quic_packet_window` (`LeanSys.Spec.verifyQuicPacketWindow`).
-/
import LeanSys.Posix
import LeanSys.Spec

namespace LeanSys.Quic

open LeanSys.Posix
open LeanSys.Spec

/-- Maximum RFC 9000 §16 62-bit variable-length integer (`2^62 - 1`). -/
def maxVarInt : UInt64 := ((1 : UInt64) <<< 62) - 1

/-- Encode an RFC 9000 §16 variable-length integer (`1`, `2`, `4`, or `8` bytes; returns `none` if `v >= 2^62`). -/
def encodeVarInt? (v : UInt64) : Option ByteArray :=
  if v > maxVarInt then
    none
  else Id.run do
    let mut out := ByteArray.emptyWithCapacity 8
    if v < 64 then
      out := out.push v.toUInt8
    else if v < 16384 then
      out := out.push ((0x40 : UInt8) ||| ((v >>> 8) &&& 0x3F).toUInt8)
      out := out.push (v &&& 0xFF).toUInt8
    else if v < 1073741824 then
      out := out.push ((0x80 : UInt8) ||| ((v >>> 24) &&& 0x3F).toUInt8)
      out := out.push ((v >>> 16) &&& 0xFF).toUInt8
      out := out.push ((v >>> 8) &&& 0xFF).toUInt8
      out := out.push (v &&& 0xFF).toUInt8
    else
      out := out.push ((0xC0 : UInt8) ||| ((v >>> 56) &&& 0x3F).toUInt8)
      out := out.push ((v >>> 48) &&& 0xFF).toUInt8
      out := out.push ((v >>> 40) &&& 0xFF).toUInt8
      out := out.push ((v >>> 32) &&& 0xFF).toUInt8
      out := out.push ((v >>> 24) &&& 0xFF).toUInt8
      out := out.push ((v >>> 16) &&& 0xFF).toUInt8
      out := out.push ((v >>> 8) &&& 0xFF).toUInt8
      out := out.push (v &&& 0xFF).toUInt8
    return some out

/-- Decode an RFC 9000 §16 variable-length integer at `off` in `src`, returning `(value, nextOff)`.
    Every buffer-extent check (`1` tag byte and `1|2|4|8` varint bytes) is routed through `ByteSource.subSource?`,
    which invokes the exported specification gate `leansys_verify_slice_bounds` (`LeanSys.Spec.verifySliceBounds`). -/
def decodeVarInt? (src : ByteSource) (off : Nat) : Option (UInt64 × Nat) := do
  let head ← src.subSource? off 1
  let first := head.getByteD 0
  let tag := first >>> 6
  let len : Nat := 1 <<< tag.toNat
  let varSub ← src.subSource? off len
  Id.run do
    let mut acc : UInt64 := (first &&& 0x3F).toUInt64
    for i in [1:len] do
      acc := (acc <<< 8) ||| (varSub.getByteD i).toUInt64
    return some (acc, off + len)

/-- Pure Sans-I/O RFC 9000 + RFC 6479 QUIC connection anti-replay & per-stream offset flow-control state. -/
structure QuicConnState where
  hasRxPacket    : Bool   := false
  maxRxPktNum    : UInt64 := 0
  windowMask     : UInt64 := 0
  connRxBytes    : UInt64 := 0
  maxConnData    : UInt64 := 1048576
  maxStreamData  : UInt64 := 262144
  peerAddrTag    : UInt64 := 0
  /-- Per-stream highest received byte offset `(streamId, maxOffsetBytes)` so connection flow-control
      advances strictly by `max(0, endOffset - prevMaxOffset)` (RFC 9000 §4.1). -/
  streamHighOffs : Array (UInt64 × UInt64) := #[]
  deriving Repr, DecidableEq

/-- Look up the tracked high-water byte offset for `streamId` (`0` if unseen). -/
def lookupStreamHighOffset (st : QuicConnState) (streamId : UInt64) : UInt64 :=
  match st.streamHighOffs.find? (fun p => p.1 == streamId) with
  | some (_, hi) => hi
  | none => 0

private def upsertStreamHighOffset (offs : Array (UInt64 × UInt64)) (streamId newHi : UInt64) : Array (UInt64 × UInt64) :=
  match offs.findIdx? (fun p => p.1 == streamId) with
  | some idx => offs.set! idx (streamId, newHi)
  | none => offs.push (streamId, newHi)

/-- Admit a QUIC packet number `pktNum` against the RFC 6479 64-packet anti-replay window (without coupling to a single
    `STREAM` frame, so packets carrying `0` or multiple `STREAM` frames admit the packet number once and then apply
    `accountStreamRange?` for each `STREAM` frame), gated by `leansys_verify_quic_packet_window`. -/
def admitPacketNumber? (st : QuicConnState) (pktNum : UInt64)
    (sourceAddrTag : UInt64 := st.peerAddrTag) : Option QuicConnState :=
  if !st.hasRxPacket then
    if verifyQuicPacketWindow pktNum 0 0 0 st.maxStreamData st.connRxBytes st.maxConnData != 1 then
      none
    else
      some {
        st with
        hasRxPacket := true
        maxRxPktNum := pktNum
        windowMask  := 1
        peerAddrTag := sourceAddrTag
      }
  else if verifyQuicPacketWindow pktNum st.maxRxPktNum st.windowMask
            0 st.maxStreamData st.connRxBytes st.maxConnData != 1 then
    none
  else if pktNum > st.maxRxPktNum then
    let shift := pktNum - st.maxRxPktNum
    let shiftedMask : UInt64 :=
      if shift >= 64 then 1 else (st.windowMask <<< shift) ||| 1
    some {
      st with
      maxRxPktNum := pktNum
      windowMask  := shiftedMask
      peerAddrTag := sourceAddrTag
    }
  else
    let diff := st.maxRxPktNum - pktNum
    some {
      st with
      windowMask := st.windowMask ||| ((1 : UInt64) <<< diff)
    }

/-- Account a single `STREAM` frame's byte range ending at `streamEndOffset` on `streamId` after packet admission
    (advancing connection credit strictly by `max(0, streamEndOffset - prevHighOffset)` with subtraction-safe overflow guard),
    gated by `leansys_verify_quic_packet_window`. Multiple `STREAM` frames in the same packet call this sequentially. -/
def accountStreamRange? (st : QuicConnState) (streamId streamEndOffset : UInt64) : Option QuicConnState :=
  let prevHi := lookupStreamHighOffset st streamId
  let nextHi := if streamEndOffset > prevHi then streamEndOffset else prevHi
  let newDeltaBytes := nextHi - prevHi
  if newDeltaBytes > st.maxConnData || st.connRxBytes > st.maxConnData - newDeltaBytes then
    none
  else
    let connAfter := st.connRxBytes + newDeltaBytes
    if verifyQuicPacketWindow 0 0 0 nextHi st.maxStreamData connAfter st.maxConnData != 1 then
      none
    else
      let nextStreams := if streamEndOffset > prevHi then upsertStreamHighOffset st.streamHighOffs streamId nextHi else st.streamHighOffs
      some {
        st with
        connRxBytes    := connAfter
        streamHighOffs := nextStreams
      }

/-- Atomically admit packet `pktNum` once and account `0..N` `(streamId, streamEndOffset)` `STREAM` frames carried in that packet. -/
def admitMultiStreamPacket? (st : QuicConnState) (pktNum : UInt64)
    (streamRanges : Array (UInt64 × UInt64))
    (sourceAddrTag : UInt64 := st.peerAddrTag) : Option QuicConnState := do
  let mut cur ← admitPacketNumber? st pktNum sourceAddrTag
  for (sid, endOff) in streamRanges do
    cur ← accountStreamRange? cur sid endOff
  pure cur

/-- Advance the RFC 6479 64-packet anti-replay bitmap and per-stream/connection flow-control state for a single-`STREAM` packet
    ending at `streamEndOffset` on `streamId`, gated by `leansys_verify_quic_packet_window`. -/
def admitStreamPacket? (st : QuicConnState) (pktNum : UInt64)
    (streamId : UInt64) (streamEndOffset : UInt64)
    (sourceAddrTag : UInt64 := st.peerAddrTag) : Option QuicConnState :=
  admitMultiStreamPacket? st pktNum #[(streamId, streamEndOffset)] sourceAddrTag

/-- Single-stream convenience wrapper around `admitStreamPacket?` on `streamId = 0` at `streamEndOffset`. -/
def admitPacket? (st : QuicConnState) (pktNum : UInt64)
    (streamEndOffset : UInt64) (_legacyDeltaHint : UInt64 := 0)
    (sourceAddrTag : UInt64 := st.peerAddrTag) : Option QuicConnState :=
  admitStreamPacket? st pktNum 0 streamEndOffset sourceAddrTag

/-- RFC 9000 Appendix A.3: Reconstruct full 62-bit packet number from a 32-bit truncated wire packet number
    relative to `largestAckedOrRx` (`expected = largestAckedOrRx + 1`). -/
def reconstructPacketNumber32 (largestAckedOrRx : UInt64) (truncatedPn : UInt32) : UInt64 :=
  let expected := largestAckedOrRx + 1
  let pnWin : UInt64 := (1 : UInt64) <<< 32
  let pnHalf : UInt64 := (1 : UInt64) <<< 31
  let pnMask : UInt64 := pnWin - 1
  let candidate := (expected &&& (~~~pnMask)) ||| truncatedPn.toUInt64
  if candidate + pnHalf <= expected && candidate + pnWin < ((1 : UInt64) <<< 62) then
    candidate + pnWin
  else if candidate > expected + pnHalf && candidate >= pnWin then
    candidate - pnWin
  else
    candidate

/-- Post-header-protection-removal RFC 9000 §17.3 1-RTT short-header packet envelope
    (`01S00K11`: form=0, fixed=1, reserved bits `0x18 == 0`, key-phase bit `K = 0x04`, 4-byte wire packet number, 8-byte DCID). -/
structure QuicShortPacket where
  dcid     : UInt64
  pktNum   : UInt64
  keyPhase : Bool := false
  payload  : ByteArray
  deriving DecidableEq

/-- Encode an unprotected 1-RTT short-header QUIC envelope (`1 + 8 + 4 + payload.size` bytes; returns `none` if `pktNum >= 2^62`). -/
def encodeShortPacket? (p : QuicShortPacket) : Option ByteArray :=
  if p.pktNum > maxVarInt then
    none
  else Id.run do
    let mut out := ByteArray.emptyWithCapacity (13 + p.payload.size)
    -- Form `0` | Fixed `0x40` | Reserved `0x00` | KeyPhase `(0x04 if keyPhase)` | 4-byte PN length `0x03`
    let hdrByte : UInt8 := (0x43 : UInt8) ||| (if p.keyPhase then (0x04 : UInt8) else (0x00 : UInt8))
    out := out.push hdrByte
    for sh in [56, 48, 40, 32, 24, 16, 8, 0] do
      out := out.push ((p.dcid >>> sh.toUInt64) &&& 0xFF).toUInt8
    let wirePn32 := (p.pktNum &&& 0xFFFFFFFF).toUInt32
    for sh in [24, 16, 8, 0] do
      out := out.push ((wirePn32 >>> sh.toUInt32) &&& 0xFF).toUInt8
    for i in [0:p.payload.size] do
      out := out.push (p.payload.get! i)
    return some out

/-- Decode an unprotected 1-RTT short-header QUIC envelope (`13+` bytes), routing header/payload bounds through
    `ByteSource.subSource?` (`leansys_verify_slice_bounds`), rejecting nonzero reserved bits (`0x18 != 0`),
    preserving `keyPhase`, and reconstructing the 62-bit packet number via RFC 9000 Appendix A.3. -/
def decodeShortPacket? (src : ByteSource) (largestRxPktNum : UInt64 := 0) : Option QuicShortPacket := do
  let hdrSub ← src.subSource? 0 13
  let hdr := hdrSub.getByteD 0
  -- Mask `0xDB = 1101_1011`: Form=0 (`0x80`), Fixed=1 (`0x40`), Reserved=00 (`0x18`), PNLen=4B (`0x03`); Spin (`0x20`) & KeyPhase (`0x04`) allowed
  if (hdr &&& 0xDB) != 0x43 then
    none
  else Id.run do
    let keyPhase := (hdr &&& 0x04) != 0
    let mut dcid : UInt64 := 0
    for i in [1:9] do
      dcid := (dcid <<< 8) ||| (hdrSub.getByteD i).toUInt64
    let mut pn32 : UInt32 := 0
    for i in [9:13] do
      pn32 := (pn32 <<< 8) ||| (hdrSub.getByteD i).toUInt32
    let fullPn := reconstructPacketNumber32 largestRxPktNum pn32
    if fullPn > maxVarInt then
      return none
    match src.subSource? 13 (src.size - 13) with
    | none => return none
    | some sub => return some { dcid := dcid, pktNum := fullPn, keyPhase := keyPhase, payload := sub.toByteArray }

/-- Batch-segment a byte stream into GSO-sized UDP QUIC datagrams (`maxSegmentPayload ≤ 1350`) with monotonic 62-bit packet numbers,
    failing closed (`none`) if packet numbers would reach or exceed RFC 9000 `2^62`. -/
def segmentDatagramsGso? (dcid : UInt64) (startPktNum : UInt64) (data : ByteSource)
    (maxSegmentPayload : Nat := 1200) (keyPhase : Bool := false) : Option (Array ByteArray × UInt64) := Id.run do
  if startPktNum > maxVarInt then
    return none
  let segCap := if maxSegmentPayload == 0 then 1200 else Nat.min maxSegmentPayload 1350
  if data.size == 0 then
    match encodeShortPacket? { dcid := dcid, pktNum := startPktNum, keyPhase := keyPhase, payload := ByteArray.empty } with
    | some pkt => return some (#[pkt], startPktNum + 1)
    | none => return none
  let segCount := (data.size + segCap - 1) / segCap
  if segCount.toUInt64 > maxVarInt + 1 - startPktNum then
    return none
  let mut out : Array ByteArray := Array.mkEmpty segCount
  let mut off := 0
  let mut pn := startPktNum
  while off < data.size do
    let chunkLen := Nat.min segCap (data.size - off)
    match data.subSource? off chunkLen with
    | none => return none
    | some sub =>
      match encodeShortPacket? { dcid := dcid, pktNum := pn, keyPhase := keyPhase, payload := sub.toByteArray } with
      | none => return none
      | some pkt => out := out.push pkt
    off := off + chunkLen
    pn := pn + 1
  return some (out, pn)

end LeanSys.Quic
