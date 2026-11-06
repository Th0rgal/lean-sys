/-
  LeanSys.H3: Pure-Lean Sans-I/O RFC 9114 HTTP/3 Capsule Framing & RFC 9204 Static QPACK Codec (`0 import Lean`, `0 sorryAx`)
  Every HTTP/3 frame capsule is validated by `leansys_verify_h3_frame_capsule`
  (`LeanSys.Spec.verifyH3FrameCapsule`), enforcing stream-role isolation (`bidi_request` vs
  `uni_control` vs `uni_qpack`) and rejecting forbidden HTTP/2 frame types (`0x02`, `0x06`, `0x08`, `0x09`).
-/
import LeanSys.Posix
import LeanSys.Spec
import LeanSys.Quic
import LeanSys.H2

namespace LeanSys.H3

open LeanSys.Posix
open LeanSys.Spec
open LeanSys.Quic

/-- RFC 9114 stream role classification passed to `leansys_verify_h3_frame_capsule`. -/
inductive H3StreamRole where
  | bidiRequest -- 0
  | uniControl  -- 1
  | uniQpack    -- 2
  deriving Repr, DecidableEq

namespace H3StreamRole

@[inline] def toByte : H3StreamRole → UInt8
  | .bidiRequest => 0
  | .uniControl  => 1
  | .uniQpack    => 2

end H3StreamRole

/-- Parsed RFC 9114 HTTP/3 frame capsule (`type` varint + `length` varint + `payload`). -/
structure H3Frame where
  frameType : UInt64
  payload   : ByteArray
  deriving DecidableEq

instance : Repr H3Frame where
  reprPrec f _ := s!"H3Frame(type={f.frameType}, len={f.payload.size})"

/-- Sans-I/O HTTP/3 frame capsule decode result. -/
inductive H3DecodeResult where
  | ok (frame : H3Frame) (consumedBytes : Nat)
  | needMoreBytes
  | frameError (reason : String)
  deriving Repr, DecidableEq

/-- Encode an RFC 9114 HTTP/3 frame capsule for `role`, gated by `verifyH3FrameCapsule`. -/
def encodeCapsule? (f : H3Frame) (role : H3StreamRole) : Option ByteArray := do
  let tyBytes ← encodeVarInt? f.frameType
  let lenBytes ← encodeVarInt? f.payload.size.toUInt64
  let hdrBytes := tyBytes.size + lenBytes.size
  let total := hdrBytes + f.payload.size
  if hdrBytes > 16 ||
     verifyH3FrameCapsule f.frameType f.payload.size.toUInt64 hdrBytes.toUInt8 role.toByte total.toUInt64 != 1 then
    none
  else Id.run do
    let mut out := ByteArray.emptyWithCapacity total
    for i in [0:tyBytes.size] do out := out.push (tyBytes.get! i)
    for i in [0:lenBytes.size] do out := out.push (lenBytes.get! i)
    for i in [0:f.payload.size] do out := out.push (f.payload.get! i)
    return some out

/-- Decode one RFC 9114 HTTP/3 frame capsule from `src` on `role`, gated by `verifyH3FrameCapsule`. -/
def decodeCapsulePrefix (src : ByteSource) (role : H3StreamRole) : H3DecodeResult :=
  if src.size < 2 then
    .needMoreBytes
  else
    match decodeVarInt? src 0 with
    | none => .needMoreBytes
    | some (fType, off1) =>
      match decodeVarInt? src off1 with
      | none => .needMoreBytes
      | some (payLen, hdrEnd) =>
        let hdrBytes := hdrEnd
        if payLen > 67108864 then
          .frameError "H3_EXCESSIVE_LOAD"
        else if src.size < hdrBytes + payLen.toNat then
          .needMoreBytes
        else if verifyH3FrameCapsule fType payLen hdrBytes.toUInt8 role.toByte src.size.toUInt64 != 1 then
          .frameError "H3_FRAME_UNEXPECTED_OR_RESERVED"
        else
          match src.subSource? hdrEnd payLen.toNat with
          | none => .frameError "H3_SLICE_BOUNDS"
          | some sub =>
            .ok { frameType := fType, payload := sub.toByteArray } (hdrEnd + payLen.toNat)

/-! ## RFC 9204 Static-Only QPACK Field Section Codec (`Required Insert Count = 0, Base = 0`) -/

/-- RFC 9204 Appendix A static table subset for HTTP/3 requests & responses. -/
def qpackStaticEntry? : Nat → Option (String × String)
  | 0  => some (":authority", "")
  | 1  => some (":path", "/")
  | 15 => some (":method", "CONNECT")
  | 16 => some (":method", "DELETE")
  | 17 => some (":method", "GET")
  | 18 => some (":method", "HEAD")
  | 19 => some (":method", "OPTIONS")
  | 20 => some (":method", "POST")
  | 21 => some (":method", "PUT")
  | 22 => some (":scheme", "http")
  | 23 => some (":scheme", "https")
  | 24 => some (":status", "103")
  | 25 => some (":status", "200")
  | 26 => some (":status", "304")
  | 27 => some (":status", "404")
  | 28 => some (":status", "503")
  | 63 => some (":status", "100")
  | 64 => some (":status", "204")
  | 67 => some (":status", "400")
  | 71 => some (":status", "500")
  | _  => none

def qpackStaticExactIndex? (name val : String) : Option Nat :=
  match name, val with
  | ":path", "/"       => some 1
  | ":method", "GET"   => some 17
  | ":method", "POST"  => some 20
  | ":scheme", "http"  => some 22
  | ":scheme", "https" => some 23
  | ":status", "100"   => some 63
  | ":status", "200"   => some 25
  | ":status", "204"   => some 64
  | ":status", "400"   => some 67
  | ":status", "404"   => some 27
  | ":status", "500"   => some 71
  | _, _               => none

/-- Encode an RFC 9204 §4.5 static-only QPACK field section (`0x00, 0x00` prefix + static indexed `11xxxxxx` or literal `0010xxxx`). -/
def encodeQpackHeaders (headers : Array (String × String)) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity (2 + headers.size * 24)
  -- Required Insert Count = 0, S = 0, Delta Base = 0
  out := out.push 0x00
  out := out.push 0x00
  for (rawName, val) in headers do
    let name := rawName.toLower
    match qpackStaticExactIndex? name val with
    | some idx =>
      -- Indexed Field Line (`1` `T=1` static `6-bit index`: `0xC0`)
      let eb := LeanSys.H2.encodeHpackInt idx 6 0xC0
      for i in [0:eb.size] do out := out.push (eb.get! i)
    | none =>
      -- Literal Field Line With Literal Name (`001` `N=0` `H=0` `3-bit name len`: `0x20`)
      let nameUtf8 := name.toUTF8
      let nb := LeanSys.H2.encodeHpackInt nameUtf8.size 3 0x20
      for i in [0:nb.size] do out := out.push (nb.get! i)
      for i in [0:nameUtf8.size] do out := out.push (nameUtf8.get! i)
      let vb := LeanSys.H2.encodeHpackString val
      for i in [0:vb.size] do out := out.push (vb.get! i)
  return out

/-- Decode an RFC 9204 §4.5 static-only QPACK field section (`Required Insert Count == 0`). -/
def decodeQpackHeaders? (src : ByteSource) (maxHeaders : Nat := 128) : Option (Array (String × String)) := Id.run do
  if src.size < 2 then
    return none
  -- Enforce Required Insert Count == 0 & Delta Base == 0 for zero-blocking static QPACK
  if src.getByteD 0 != 0 || src.getByteD 1 != 0 then
    return none
  let mut out : Array (String × String) := #[]
  let mut off := 2
  while off < src.size do
    if out.size >= maxHeaders then
      return none
    let b := src.getByteD off
    if (b &&& 0xC0) == 0xC0 then
      match LeanSys.H2.decodeHpackInt? src off 6 with
      | none => return none
      | some (idx, nextOff) =>
        match qpackStaticEntry? idx with
        | none => return none
        | some kv =>
          out := out.push kv
          off := nextOff
    else if (b &&& 0xF8) == 0x20 then
      match LeanSys.H2.decodeHpackInt? src off 3 with
      | none => return none
      | some (nameLen, afterLen) =>
        match src.subSource? afterLen nameLen with
        | none => return none
        | some nameSub =>
          let name := String.fromUTF8! nameSub.toByteArray
          match LeanSys.H2.decodeHpackString? src (afterLen + nameLen) with
          | none => return none
          | some (val, afterVal) =>
            out := out.push (name, val)
            off := afterVal
    else
      return none
  return some out

/-- Encode an RFC 9114 HTTP/3 `HEADERS` (`0x01`) + optional `DATA` (`0x00`) request/response stream payload. -/
def encodeH3Message? (headers : Array (String × String)) (body : ByteArray := ByteArray.empty) : Option ByteArray := do
  let hdrPayload := encodeQpackHeaders headers
  let hdrCap ← encodeCapsule? { frameType := 0x01, payload := hdrPayload } .bidiRequest
  if body.isEmpty then
    some hdrCap
  else
    let dataCap ← encodeCapsule? { frameType := 0x00, payload := body } .bidiRequest
    Id.run do
      let mut out := ByteArray.emptyWithCapacity (hdrCap.size + dataCap.size)
      for i in [0:hdrCap.size] do out := out.push (hdrCap.get! i)
      for i in [0:dataCap.size] do out := out.push (dataCap.get! i)
      return some out

end LeanSys.H3
