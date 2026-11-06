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

/-- Decode an RFC 9000 §16 variable-length integer at `off` in `src`, returning `(value, nextOff)`. -/
def decodeVarInt? (src : ByteSource) (off : Nat) : Option (UInt64 × Nat) :=
  if off >= src.size then
    none
  else
    let first := src.getByteD off
    let tag := first >>> 6
    let len : Nat := 1 <<< tag.toNat
    if off + len > src.size then
      none
    else Id.run do
      let mut acc : UInt64 := (first &&& 0x3F).toUInt64
      for i in [1:len] do
        acc := (acc <<< 8) ||| (src.getByteD (off + i)).toUInt64
      return some (acc, off + len)

/-- Pure Sans-I/O RFC 9000 + RFC 6479 QUIC connection anti-replay & flow-control state. -/
structure QuicConnState where
  hasRxPacket   : Bool   := false
  maxRxPktNum   : UInt64 := 0
  windowMask    : UInt64 := 0
  connRxBytes   : UInt64 := 0
  maxConnData   : UInt64 := 1048576
  maxStreamData : UInt64 := 262144
  peerAddrTag   : UInt64 := 0
  deriving Repr, DecidableEq

/-- Advance the RFC 6479 64-packet anti-replay bitmap and stream/connection byte counters,
    gated by `leansys_verify_quic_packet_window`. Returns `none` on replay, stale packet, or flow-control overrun. -/
def admitPacket? (st : QuicConnState) (pktNum : UInt64)
    (streamBytesAfter : UInt64) (newDeltaBytes : UInt64)
    (sourceAddrTag : UInt64 := st.peerAddrTag) : Option QuicConnState :=
  if newDeltaBytes > st.maxConnData || st.connRxBytes > st.maxConnData - newDeltaBytes then
    none
  else
    let connAfter := st.connRxBytes + newDeltaBytes
    if !st.hasRxPacket then
      if verifyQuicPacketWindow pktNum 0 0 streamBytesAfter st.maxStreamData connAfter st.maxConnData != 1 then
        none
      else
        some {
          st with
          hasRxPacket := true
          maxRxPktNum := pktNum
          windowMask  := 1
          connRxBytes := connAfter
          peerAddrTag := sourceAddrTag
        }
    else if verifyQuicPacketWindow pktNum st.maxRxPktNum st.windowMask
              streamBytesAfter st.maxStreamData connAfter st.maxConnData != 1 then
      none
    else if pktNum > st.maxRxPktNum then
      let shift := pktNum - st.maxRxPktNum
      let shiftedMask : UInt64 :=
        if shift >= 64 then 1 else (st.windowMask <<< shift) ||| 1
      some {
        st with
        maxRxPktNum := pktNum
        windowMask  := shiftedMask
        connRxBytes := connAfter
        peerAddrTag := if pktNum > st.maxRxPktNum then sourceAddrTag else st.peerAddrTag
      }
    else
      let diff := st.maxRxPktNum - pktNum
      some {
        st with
        windowMask  := st.windowMask ||| ((1 : UInt64) <<< diff)
        connRxBytes := connAfter
      }

/-- RFC 9000 §17.3 1-RTT short-header packet envelope (`01xxxxxx` fixed bit, 8-byte DCID, 4-byte packet number). -/
structure QuicShortPacket where
  dcid    : UInt64
  pktNum  : UInt32
  payload : ByteArray
  deriving DecidableEq

/-- Encode a 1-RTT short-header QUIC datagram (`1 + 8 + 4 + payload.size` bytes). -/
def encodeShortPacket (p : QuicShortPacket) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity (13 + p.payload.size)
  -- Fixed bit `0x40` | 4-byte packet-number length (`0x03`)
  out := out.push 0x43
  for sh in [56, 48, 40, 32, 24, 16, 8, 0] do
    out := out.push ((p.dcid >>> sh.toUInt64) &&& 0xFF).toUInt8
  for sh in [24, 16, 8, 0] do
    out := out.push ((p.pktNum >>> sh.toUInt32) &&& 0xFF).toUInt8
  for i in [0:p.payload.size] do
    out := out.push (p.payload.get! i)
  return out

/-- Decode a 1-RTT short-header QUIC datagram (`0x43` header, 8-byte DCID, 4-byte packet number). -/
def decodeShortPacket? (src : ByteSource) : Option QuicShortPacket :=
  if src.size < 13 then
    none
  else
    let hdr := src.getByteD 0
    if (hdr &&& 0xC3) != 0x43 then
      none
    else Id.run do
      let mut dcid : UInt64 := 0
      for i in [1:9] do
        dcid := (dcid <<< 8) ||| (src.getByteD i).toUInt64
      let mut pn : UInt32 := 0
      for i in [9:13] do
        pn := (pn <<< 8) ||| (src.getByteD i).toUInt32
      match src.subSource? 13 (src.size - 13) with
      | none => return none
      | some sub => return some { dcid := dcid, pktNum := pn, payload := sub.toByteArray }

/-- Batch-segment a byte stream into GSO-sized UDP QUIC datagrams (`maxSegmentPayload ≤ 1350`) with monotonic packet numbers. -/
def segmentDatagramsGso (dcid : UInt64) (startPktNum : UInt32) (data : ByteSource)
    (maxSegmentPayload : Nat := 1200) : Array ByteArray := Id.run do
  let segCap := if maxSegmentPayload == 0 then 1200 else Nat.min maxSegmentPayload 1350
  if data.size == 0 then
    return #[encodeShortPacket { dcid := dcid, pktNum := startPktNum, payload := ByteArray.empty }]
  let mut out : Array ByteArray := #[]
  let mut off := 0
  let mut pn := startPktNum
  while off < data.size do
    let chunkLen := Nat.min segCap (data.size - off)
    if let some sub := data.subSource? off chunkLen then
      out := out.push (encodeShortPacket { dcid := dcid, pktNum := pn, payload := sub.toByteArray })
    off := off + chunkLen
    pn := pn + 1
  return out

end LeanSys.Quic
