/-
  LeanSys.H2: Pure-Lean Sans-I/O RFC 9113 HTTP/2 Framing, RFC 7541 HPACK Static/Literal Codec & Flow-Control Engine (`0 import Lean`, `0 sorryAx`)
  Every decoded frame header and DATA flow-control transition is gated by `leansys_verify_h2_frame_header`
  (`LeanSys.Spec.verifyH2FrameHeader`) over zero-copy `ByteSource` / `ByteSlice` views.
-/
import LeanSys.Posix
import LeanSys.Spec

namespace LeanSys.H2

open LeanSys.Posix
open LeanSys.Spec

/-- RFC 9113 §3.4 HTTP/2 24-octet client connection preface (`PRI * HTTP/2.0\r\n\r\nSM\r\n\r\n`). -/
def clientPreface : ByteArray :=
  "PRI * HTTP/2.0\r\n\r\nSM\r\n\r\n".toUTF8

/-- RFC 9113 §6 HTTP/2 frame type codes. -/
inductive H2FrameType where
  | data         -- 0x0
  | headers      -- 0x1
  | priority     -- 0x2
  | rstStream    -- 0x3
  | settings     -- 0x4
  | pushPromise  -- 0x5
  | ping         -- 0x6
  | goaway       -- 0x7
  | windowUpdate -- 0x8
  | continuation -- 0x9
  | unknown (raw : UInt8)
  deriving Repr, DecidableEq

namespace H2FrameType

@[inline] def toByte : H2FrameType → UInt8
  | .data         => 0
  | .headers      => 1
  | .priority     => 2
  | .rstStream    => 3
  | .settings     => 4
  | .pushPromise  => 5
  | .ping         => 6
  | .goaway       => 7
  | .windowUpdate => 8
  | .continuation => 9
  | .unknown b    => b

@[inline] def ofByte : UInt8 → H2FrameType
  | 0 => .data
  | 1 => .headers
  | 2 => .priority
  | 3 => .rstStream
  | 4 => .settings
  | 5 => .pushPromise
  | 6 => .ping
  | 7 => .goaway
  | 8 => .windowUpdate
  | 9 => .continuation
  | b => .unknown b

end H2FrameType

/-- Parsed RFC 9113 HTTP/2 frame over an owned `ByteArray` payload. -/
structure H2Frame where
  frameType : H2FrameType
  flags     : UInt8
  streamId  : UInt32
  payload   : ByteArray
  deriving DecidableEq

instance : Repr H2Frame where
  reprPrec f _ :=
    s!"H2Frame(type={repr f.frameType}, flags={f.flags}, stream={f.streamId}, len={f.payload.size})"

/-- Sans-I/O HTTP/2 frame decode outcome over a `ByteSource`. -/
inductive H2DecodeResult where
  | ok (frame : H2Frame) (consumedBytes : Nat)
  | needMoreBytes
  | protocolError (reason : String)
  deriving Repr, DecidableEq

/-- Validate frame-specific payload invariants after `verifyH2FrameHeader` passes (all slice extents routed through
    `ByteSource.subSource?` -> `leansys_verify_slice_bounds`):
    - `PADDED` (`0x08`) on `DATA` / `HEADERS` / `PUSH_PROMISE`: `padLength` byte + mandatory header fields MUST NOT reach or exceed `payload.size`
    - `WINDOW_UPDATE` (`0x08`): 31-bit increment MUST be nonzero (`1..0x7FFFFFFF`, RFC 9113 §6.9)
    - `PUSH_PROMISE` (`0x05`): 31-bit promised stream ID MUST be nonzero (`RFC 9113 §6.6`). -/
def payloadStructurallyValid (ft : H2FrameType) (flags : UInt8) (payload : ByteSource) : Bool :=
  let padded := (flags &&& 0x08) != 0
  match ft with
  | .data =>
    if !padded then true
    else
      match payload.subSource? 0 1 with
      | none => false
      | some p0 => (payload.subSource? 1 (p0.getByteD 0).toNat).isSome
  | .headers =>
    let prioBytes := if (flags &&& 0x20) != 0 then 5 else 0
    if !padded then (payload.subSource? 0 prioBytes).isSome
    else
      match payload.subSource? 0 (1 + prioBytes) with
      | none => false
      | some hdr => (payload.subSource? (1 + prioBytes) (hdr.getByteD 0).toNat).isSome
  | .pushPromise =>
    let padOff := if padded then 1 else 0
    match payload.subSource? 0 (padOff + 4) with
    | none => false
    | some hdr =>
      let padLen := if padded then (hdr.getByteD 0).toNat else 0
      let p0 := (hdr.getByteD padOff).toUInt32 &&& 0x7F
      let p1 := (hdr.getByteD (padOff + 1)).toUInt32
      let p2 := (hdr.getByteD (padOff + 2)).toUInt32
      let p3 := (hdr.getByteD (padOff + 3)).toUInt32
      let promisedSid := (p0 <<< 24) ||| (p1 <<< 16) ||| (p2 <<< 8) ||| p3
      promisedSid > 0 && (payload.subSource? (padOff + 4) padLen).isSome
  | .windowUpdate =>
    if payload.size != 4 then false
    else
      match payload.subSource? 0 4 with
      | none => false
      | some hdr =>
        let w0 := (hdr.getByteD 0).toUInt32 &&& 0x7F
        let w1 := (hdr.getByteD 1).toUInt32
        let w2 := (hdr.getByteD 2).toUInt32
        let w3 := (hdr.getByteD 3).toUInt32
        ((w0 <<< 24) ||| (w1 <<< 16) ||| (w2 <<< 8) ||| w3) > 0
  | _ => true

/-- Encode an RFC 9113 9-byte frame header + payload gated by `verifyH2FrameHeader` and `payloadStructurallyValid`
    (canonicalizing `H2FrameType.ofByte tyByte` so `.unknown` wrapping a known frame code cannot bypass payload checks). -/
def encodeFrame? (f : H2Frame) (maxFrameSize : UInt32 := 16384)
    (recvWindow : UInt64 := 65535) : Option ByteArray :=
  let payLen := f.payload.size
  if payLen > 16777215 then
    none
  else
    let pay32 := payLen.toUInt32
    let total := (9 + payLen).toUInt64
    let tyByte := f.frameType.toByte
    let canonFt := H2FrameType.ofByte tyByte
    if verifyH2FrameHeader pay32 maxFrameSize tyByte f.flags f.streamId recvWindow total != 1 ||
       !payloadStructurallyValid canonFt f.flags (ByteSource.ofByteArray f.payload) then
      none
    else Id.run do
      let mut out := ByteArray.emptyWithCapacity (9 + payLen)
      out := out.push ((pay32 >>> 16) &&& 0xFF).toUInt8
      out := out.push ((pay32 >>> 8) &&& 0xFF).toUInt8
      out := out.push (pay32 &&& 0xFF).toUInt8
      out := out.push tyByte
      out := out.push f.flags
      let sid := f.streamId &&& 0x7FFFFFFF
      out := out.push ((sid >>> 24) &&& 0x7F).toUInt8
      out := out.push ((sid >>> 16) &&& 0xFF).toUInt8
      out := out.push ((sid >>> 8) &&& 0xFF).toUInt8
      out := out.push (sid &&& 0xFF).toUInt8
      for i in [0:payLen] do
        out := out.push (f.payload.get! i)
      return some out

/-- Decode one RFC 9113 HTTP/2 frame from `src` gated by `subSource?` (`leansys_verify_slice_bounds`),
    `verifyH2FrameHeader`, and `payloadStructurallyValid`. -/
def decodeFramePrefix (src : ByteSource) (maxFrameSize : UInt32 := 16384)
    (recvWindow : UInt64 := 65535) : H2DecodeResult :=
  match src.subSource? 0 9 with
  | none => .needMoreBytes
  | some hdr =>
    let total := src.size
    let b0 := (hdr.getByteD 0).toUInt32
    let b1 := (hdr.getByteD 1).toUInt32
    let b2 := (hdr.getByteD 2).toUInt32
    let pay32 := (b0 <<< 16) ||| (b1 <<< 8) ||| b2
    let tyByte := hdr.getByteD 3
    let flags := hdr.getByteD 4
    let s0 := (hdr.getByteD 5).toUInt32 &&& 0x7F
    let s1 := (hdr.getByteD 6).toUInt32
    let s2 := (hdr.getByteD 7).toUInt32
    let s3 := (hdr.getByteD 8).toUInt32
    let streamId := (s0 <<< 24) ||| (s1 <<< 16) ||| (s2 <<< 8) ||| s3
    let ft := H2FrameType.ofByte tyByte
    if pay32 > maxFrameSize then
      .protocolError "FRAME_SIZE_ERROR"
    else if (src.subSource? 0 (9 + pay32.toNat)).isNone then
      .needMoreBytes
    else if verifyH2FrameHeader pay32 maxFrameSize tyByte flags streamId recvWindow total.toUInt64 != 1 then
      .protocolError "PROTOCOL_OR_FLOW_CONTROL_ERROR"
    else
      match src.subSource? 9 pay32.toNat with
      | none => .protocolError "SLICE_BOUNDS_ERROR"
      | some sub =>
        if !payloadStructurallyValid ft flags sub then
          .protocolError "PROTOCOL_PAYLOAD_ERROR"
        else
          let payload := sub.toByteArray
          .ok { frameType := ft, flags := flags, streamId := streamId, payload := payload }
            (9 + pay32.toNat)

/-! ## RFC 7541 Subset HPACK Static Table + Literal Without Indexing Codec -/

/-- Selected RFC 7541 Appendix A static table entries used across HTTP/2 gateways & clients. -/
def hpackStaticEntry? : Nat → Option (String × String)
  | 1  => some (":authority", "")
  | 2  => some (":method", "GET")
  | 3  => some (":method", "POST")
  | 4  => some (":path", "/")
  | 5  => some (":path", "/index.html")
  | 6  => some (":scheme", "http")
  | 7  => some (":scheme", "https")
  | 8  => some (":status", "200")
  | 9  => some (":status", "204")
  | 10 => some (":status", "206")
  | 11 => some (":status", "304")
  | 12 => some (":status", "400")
  | 13 => some (":status", "404")
  | 14 => some (":status", "500")
  | 16 => some ("accept-encoding", "gzip, deflate")
  | 31 => some ("content-type", "")
  | 58 => some ("user-agent", "")
  | _  => none

/-- Find exact RFC 7541 static-table match `(index)` if `(name, val)` matches an indexed entry. -/
def hpackStaticExactIndex? (name val : String) : Option Nat :=
  match name, val with
  | ":method", "GET"   => some 2
  | ":method", "POST"  => some 3
  | ":path", "/"       => some 4
  | ":scheme", "http"  => some 6
  | ":scheme", "https" => some 7
  | ":status", "200"   => some 8
  | ":status", "204"   => some 9
  | ":status", "400"   => some 12
  | ":status", "404"   => some 13
  | ":status", "500"   => some 14
  | _, _               => none

/-- Encode an RFC 7541 §5.1 integer with `prefixBits` (`1..7`) and high-bit mask `prefixMask`. -/
def encodeHpackInt (val : Nat) (prefixBits : Nat) (prefixMask : UInt8) : ByteArray := Id.run do
  let maxPrefix := (1 <<< prefixBits) - 1
  let mut out := ByteArray.emptyWithCapacity 4
  if val < maxPrefix then
    out := out.push (prefixMask ||| val.toUInt8)
    return out
  out := out.push (prefixMask ||| maxPrefix.toUInt8)
  let mut rem := val - maxPrefix
  while rem >= 128 do
    out := out.push (((rem &&& 0x7F) ||| 0x80).toUInt8)
    rem := rem >>> 7
  out := out.push rem.toUInt8
  return out

/-- Decode an RFC 7541 §5.1 integer starting at `off` in `src` (bounded to `≤ 5` continuation bytes,
    routing every byte read through `ByteSource.subSource?` -> `leansys_verify_slice_bounds`). -/
def decodeHpackInt? (src : ByteSource) (off : Nat) (prefixBits : Nat) : Option (Nat × Nat) := do
  let head ← src.subSource? off 1
  let mask : Nat := (1 <<< prefixBits) - 1
  let first := (head.getByteD 0).toNat &&& mask
  if first < mask then
    some (first, off + 1)
  else Id.run do
    let mut acc := first
    let mut shift := 0
    let mut idx := off + 1
    let mut steps := 0
    while steps < 5 do
      match src.subSource? idx 1 with
      | none => return none
      | some bSub =>
        let b := (bSub.getByteD 0).toNat
        acc := acc + ((b &&& 0x7F) <<< shift)
        idx := idx + 1
        if (b &&& 0x80) == 0 then
          return some (acc, idx)
        shift := shift + 7
        steps := steps + 1
    return none

/-- Encode a raw non-Huffman RFC 7541 §5.2 string literal. -/
def encodeHpackString (s : String) : ByteArray := Id.run do
  let utf8 := s.toUTF8
  let lenBytes := encodeHpackInt utf8.size 7 0x00
  let mut out := ByteArray.emptyWithCapacity (lenBytes.size + utf8.size)
  for i in [0:lenBytes.size] do
    out := out.push (lenBytes.get! i)
  for i in [0:utf8.size] do
    out := out.push (utf8.get! i)
  return out

/-- Decode a non-Huffman RFC 7541 §5.2 string literal at `off` in `src` (bounds routed via `subSource?`). -/
def decodeHpackString? (src : ByteSource) (off : Nat) : Option (String × Nat) := do
  let head ← src.subSource? off 1
  let huff := (head.getByteD 0) &&& 0x80
  if huff != 0 then
    none
  else
    let (strLen, nextOff) ← decodeHpackInt? src off 7
    let sub ← src.subSource? nextOff strLen
    some (String.fromUTF8! sub.toByteArray, nextOff + strLen)

/-- Encode HTTP/2 headers using RFC 7541 indexed static entries (`0x80 | idx`) or literal-without-indexing (`0x00`). -/
def encodeHeadersBlock (headers : Array (String × String)) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity (headers.size * 24)
  for (rawName, val) in headers do
    let name := rawName.toLower
    match hpackStaticExactIndex? name val with
    | some idx =>
      let eb := encodeHpackInt idx 7 0x80
      for i in [0:eb.size] do out := out.push (eb.get! i)
    | none =>
      out := out.push 0x00
      let nb := encodeHpackString name
      for i in [0:nb.size] do out := out.push (nb.get! i)
      let vb := encodeHpackString val
      for i in [0:vb.size] do out := out.push (vb.get! i)
  return out

/-- Decode a static-table-only RFC 7541 header block (`SETTINGS_HEADER_TABLE_SIZE = 0`):
    - Accepts static-table indexed entries (`1xxxxxxx`), literal-without-indexing (`0000xxxx`),
      and literal-never-indexed (`0001xxxx`).
    - Rejects literal-with-incremental-indexing (`01xxxxxx`, since our decoder maintains no dynamic table)
      and rejects dynamic-table-size updates (`001xxxxx`) unless placed at the very start of the block
      with size `0` (`RFC 7541 §4.2`). -/
def decodeHeadersBlock? (src : ByteSource) (maxHeaders : Nat := 128) : Option (Array (String × String)) := Id.run do
  let mut out : Array (String × String) := #[]
  let mut off := 0
  let mut sawField := false
  while off < src.size do
    if out.size >= maxHeaders then
      return none
    let b ← match src.subSource? off 1 with
      | some head => pure (head.getByteD 0)
      | none => return none
    if (b &&& 0x80) != 0 then
      match decodeHpackInt? src off 7 with
      | none => return none
      | some (idx, nextOff) =>
        match hpackStaticEntry? idx with
        | none => return none
        | some kv =>
          out := out.push kv
          sawField := true
          off := nextOff
    else if (b &&& 0x40) != 0 then
      -- Incremental indexing (`01xxxxxx`) requires a dynamic table; reject in static-only mode (`SETTINGS_HEADER_TABLE_SIZE = 0`)
      return none
    else if (b &&& 0xE0) == 0x20 then
      -- Dynamic table size update (`001xxxxx`): RFC 7541 §4.2 requires placement before any header field and `sz == 0`
      if sawField then
        return none
      match decodeHpackInt? src off 5 with
      | some (sz, nextOff) =>
        if sz != 0 then return none
        off := nextOff
      | none => return none
    else
      match decodeHpackInt? src off 4 with
      | none => return none
      | some (nameIdx, afterIdx) =>
        if nameIdx == 0 then
          match decodeHpackString? src afterIdx with
          | none => return none
          | some (name, afterName) =>
            match decodeHpackString? src afterName with
            | none => return none
            | some (val, afterVal) =>
              out := out.push (name, val)
              sawField := true
              off := afterVal
        else
          match hpackStaticEntry? nameIdx, decodeHpackString? src afterIdx with
          | some (name, _), some (val, afterVal) =>
            out := out.push (name, val)
            sawField := true
            off := afterVal
          | _, _ => return none
  return some out

/-- Encode an RFC 9113 `SETTINGS` frame (`streamId = 0`, 6 bytes per `(id : UInt16, val : UInt32)`). -/
def buildSettingsFrame? (params : Array (UInt16 × UInt32)) (ack : Bool := false) : Option ByteArray :=
  if ack && !params.isEmpty then
    none
  else Id.run do
    let mut pay := ByteArray.emptyWithCapacity (params.size * 6)
    for (id, v) in params do
      pay := pay.push ((id >>> 8) &&& 0xFF).toUInt8
      pay := pay.push (id &&& 0xFF).toUInt8
      pay := pay.push ((v >>> 24) &&& 0xFF).toUInt8
      pay := pay.push ((v >>> 16) &&& 0xFF).toUInt8
      pay := pay.push ((v >>> 8) &&& 0xFF).toUInt8
      pay := pay.push (v &&& 0xFF).toUInt8
    return encodeFrame? {
      frameType := .settings
      flags := if ack then 0x01 else 0x00
      streamId := 0
      payload := pay
    }

/-- Encode an RFC 9113 `WINDOW_UPDATE` frame (`1 <= increment <= 0x7FFFFFFF`). -/
def buildWindowUpdateFrame? (streamId : UInt32) (increment : UInt32) : Option ByteArray :=
  if increment == 0 || increment > 0x7FFFFFFF then
    none
  else Id.run do
    let mut pay := ByteArray.emptyWithCapacity 4
    pay := pay.push ((increment >>> 24) &&& 0x7F).toUInt8
    pay := pay.push ((increment >>> 16) &&& 0xFF).toUInt8
    pay := pay.push ((increment >>> 8) &&& 0xFF).toUInt8
    pay := pay.push (increment &&& 0xFF).toUInt8
    return encodeFrame? {
      frameType := .windowUpdate
      flags := 0
      streamId := streamId
      payload := pay
    }

/-- Pure Sans-I/O HTTP/2 connection flow-control state. -/
structure H2ConnState where
  maxFrameSize   : UInt32 := 16384
  connRecvWindow : UInt64 := 65535
  connSendWindow : UInt64 := 65535
  nextClientSid  : UInt32 := 1
  deriving Repr, DecidableEq

/-- Step a Sans-I/O `H2ConnState` on an inbound `ByteSource`, deducting `DATA` flow-control credit cleanly. -/
def stepInboundFrame (st : H2ConnState) (src : ByteSource) : H2DecodeResult × H2ConnState :=
  match decodeFramePrefix src st.maxFrameSize st.connRecvWindow with
  | .ok frame consumed =>
    let st' :=
      match frame.frameType with
      | .data => { st with connRecvWindow := st.connRecvWindow - frame.payload.size.toUInt64 }
      | _ => st
    (.ok frame consumed, st')
  | other => (other, st)

end LeanSys.H2
