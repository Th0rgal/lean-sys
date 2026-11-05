/-
  LeanSys.WebSocket: Pure-Lean RFC 6455 WebSocket Handshake, Framing & Masking Engine
  (`0 import Lean`, `0 sorryAx`, `0 SSL_`, `0 C LOC`)
  - Pure-Lean FIPS 180-4 SHA-1 + RFC 4648 Base64 solely for the RFC 6455 §4.2.2 `Sec-WebSocket-Accept` handshake
    (verified against the official RFC 6455 §1.3 vector `"dGhlIHNhbXBsZSBub25jZQ==" -> "s3pPLMBiTxaQ9kYGzzhZRbK+xOo="`)
  - Frame decoder (`decodeFramePrefix?`) and encoder (`encodeFrame?`) gated by `LeanSys.Spec.verifyWsFrameHeader`:
    enforces client-masked / server-unmasked RFC 6455 §5.1 invariant, rejects RSV bits, rejects fragmented or >125-byte
    control frames (`ping`/`pong`/`close`), and bounds total frame size.
-/
import LeanSys.Spec
import LeanSys.Posix
import LeanSys.Hash

namespace LeanSys.WebSocket

open LeanSys.Spec
open LeanSys.Posix
open LeanSys.Hash (byteAt)

/-- Official RFC 6455 §4.2.2 WebSocket handshake GUID. -/
def wsMagicGuid : String := "258EAFA5-E914-47DA-95CA-C5AB0DC85B11"

/-- RFC 6455 WebSocket opcodes. -/
inductive WsOpcode where
  | continuation
  | text
  | binary
  | close
  | ping
  | pong
  deriving Repr, DecidableEq, Inhabited

namespace WsOpcode

@[inline]
def toUInt8 : WsOpcode → UInt8
  | .continuation => 0x0
  | .text         => 0x1
  | .binary       => 0x2
  | .close        => 0x8
  | .ping         => 0x9
  | .pong         => 0xA

@[inline]
def ofUInt8? : UInt8 → Option WsOpcode
  | 0x0 => some .continuation
  | 0x1 => some .text
  | 0x2 => some .binary
  | 0x8 => some .close
  | 0x9 => some .ping
  | 0xA => some .pong
  | _   => none

end WsOpcode

/-! ## Pure-Lean FIPS 180-4 SHA-1 & RFC 4648 Base64 (RFC 6455 §4.2.2 Handshake Only) -/

@[inline]
private def rotl32 (x : UInt32) (n : UInt32) : UInt32 :=
  (x <<< n) ||| (x >>> (32 - n))

@[inline]
private def readWord32BE (ba : ByteArray) (off : Nat) : UInt32 :=
  ((byteAt ba off).toUInt32 <<< 24) |||
  ((byteAt ba (off + 1)).toUInt32 <<< 16) |||
  ((byteAt ba (off + 2)).toUInt32 <<< 8) |||
  (byteAt ba (off + 3)).toUInt32

@[inline]
private def pushWord32BE (ba : ByteArray) (v : UInt32) : ByteArray :=
  ba.push ((v >>> 24) &&& 0xFF).toUInt8
    |>.push ((v >>> 16) &&& 0xFF).toUInt8
    |>.push ((v >>> 8) &&& 0xFF).toUInt8
    |>.push (v &&& 0xFF).toUInt8

/-- Compute the 20-byte FIPS 180-4 SHA-1 digest over `msg : ByteArray` (used exclusively for RFC 6455 `Sec-WebSocket-Accept`). -/
def sha1Bytes (msg : ByteArray) : ByteArray := Id.run do
  let mLen := msg.size
  let bitLen : UInt64 := mLen.toUInt64 * 8
  let rem := (mLen + 9) % 64
  let padZeros := if rem == 0 then 0 else 64 - rem
  let mut padded := ByteArray.emptyWithCapacity (mLen + 1 + padZeros + 8)
  if mLen > 0 then
    padded := msg.copySlice 0 padded 0 mLen false
  padded := padded.push 0x80
  for _ in [0:padZeros] do
    padded := padded.push 0x00
  padded := pushWord32BE padded ((bitLen >>> 32) &&& 0xFFFFFFFF).toUInt32
  padded := pushWord32BE padded (bitLen &&& 0xFFFFFFFF).toUInt32

  let mut h0 : UInt32 := 0x67452301
  let mut h1 : UInt32 := 0xEFCDAB89
  let mut h2 : UInt32 := 0x98BADCFE
  let mut h3 : UInt32 := 0x10325476
  let mut h4 : UInt32 := 0xC3D2E1F0

  let blocks := padded.size / 64
  for blk in [0:blocks] do
    let base := blk * 64
    let mut w : Array UInt32 := Array.mkEmpty 80
    for t in [0:16] do
      w := w.push (readWord32BE padded (base + t * 4))
    for t in [16:80] do
      let x := w[t - 3]! ^^^ w[t - 8]! ^^^ w[t - 14]! ^^^ w[t - 16]!
      w := w.push (rotl32 x 1)
    let mut a := h0
    let mut b := h1
    let mut c := h2
    let mut d := h3
    let mut e := h4
    for t in [0:80] do
      let (f, k) : UInt32 × UInt32 :=
        if t < 20 then
          (((b &&& c) ||| ((~~~b) &&& d)), 0x5A827999)
        else if t < 40 then
          ((b ^^^ c ^^^ d), 0x6ED9EBA1)
        else if t < 60 then
          (((b &&& c) ||| (b &&& d) ||| (c &&& d)), 0x8F1BBCDC)
        else
          ((b ^^^ c ^^^ d), 0xCA62C1D6)
      let temp := rotl32 a 5 + f + e + k + w[t]!
      e := d
      d := c
      c := rotl32 b 30
      b := a
      a := temp
    h0 := h0 + a
    h1 := h1 + b
    h2 := h2 + c
    h3 := h3 + d
    h4 := h4 + e

  let mut out := ByteArray.emptyWithCapacity 20
  out := pushWord32BE out h0
  out := pushWord32BE out h1
  out := pushWord32BE out h2
  out := pushWord32BE out h3
  out := pushWord32BE out h4
  return out

/-- Encode `ba : ByteArray` to standard RFC 4648 Base64 ASCII `String`. -/
def base64Encode (ba : ByteArray) : String := Id.run do
  let alphabet := "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".toUTF8
  let n := ba.size
  let fullGroups := n / 3
  let rem := n % 3
  let mut out := ByteArray.emptyWithCapacity (((n + 2) / 3) * 4)
  for g in [0:fullGroups] do
    let p := g * 3
    let b0 := (ba.get! p).toNat
    let b1 := (ba.get! (p + 1)).toNat
    let b2 := (ba.get! (p + 2)).toNat
    let triple := (b0 <<< 16) ||| (b1 <<< 8) ||| b2
    out := out.push (alphabet.get! ((triple >>> 18) &&& 0x3F))
      |>.push (alphabet.get! ((triple >>> 12) &&& 0x3F))
      |>.push (alphabet.get! ((triple >>> 6) &&& 0x3F))
      |>.push (alphabet.get! (triple &&& 0x3F))
  if rem == 1 then
    let b0 := (ba.get! (fullGroups * 3)).toNat
    let triple := b0 <<< 16
    out := out.push (alphabet.get! ((triple >>> 18) &&& 0x3F))
      |>.push (alphabet.get! ((triple >>> 12) &&& 0x3F))
      |>.push 61 -- '='
      |>.push 61 -- '='
  else if rem == 2 then
    let b0 := (ba.get! (fullGroups * 3)).toNat
    let b1 := (ba.get! (fullGroups * 3 + 1)).toNat
    let triple := (b0 <<< 16) ||| (b1 <<< 8)
    out := out.push (alphabet.get! ((triple >>> 18) &&& 0x3F))
      |>.push (alphabet.get! ((triple >>> 12) &&& 0x3F))
      |>.push (alphabet.get! ((triple >>> 6) &&& 0x3F))
      |>.push 61 -- '='
  return String.fromUTF8! out

/-- Compute the RFC 6455 §4.2.2 `Sec-WebSocket-Accept` value for `secWebSocketKey`. -/
def computeAcceptKey (secWebSocketKey : String) : String :=
  let concat := (secWebSocketKey.trimAscii.toString ++ wsMagicGuid).toUTF8
  base64Encode (sha1Bytes concat)

/-! ## RFC 6455 Frame Masking, Encoding & Streaming Prefix Decoding -/

/-- Decoded WebSocket frame (with payload already unmasked when `masked == true`). -/
structure WsFrame where
  fin     : Bool := true
  opcode  : WsOpcode
  payload : ByteArray
  deriving DecidableEq, Inhabited

/-- Apply RFC 6455 §5.3 4-byte XOR payload mask (`j mod 4`). -/
def applyMask (payload : ByteArray) (maskKey4 : ByteArray) : ByteArray := Id.run do
  if maskKey4.size < 4 || payload.isEmpty then
    return payload
  let m0 := maskKey4.get! 0
  let m1 := maskKey4.get! 1
  let m2 := maskKey4.get! 2
  let m3 := maskKey4.get! 3
  let mut out := ByteArray.emptyWithCapacity payload.size
  for i in [0:payload.size] do
    let m := match i &&& 3 with
      | 0 => m0
      | 1 => m1
      | 2 => m2
      | _ => m3
    out := out.push (payload.get! i ^^^ m)
  return out

/-- RFC 6455 §7.4 valid wire close status code predicate:
    allows `1000..1003`, `1007..1014`, and `3000..4999`; rejects `1004`, `1005`, `1006`, `1015`, `< 1000`, `>= 5000`. -/
def isValidCloseCode (code : UInt16) : Bool :=
  (code ≥ 1000 && code ≤ 1003) ||
  (code ≥ 1007 && code ≤ 1014) ||
  (code ≥ 3000 && code ≤ 4999)

/-- RFC 6455 §5.5.1 / §5.6 frame payload validation (close payload length/code/UTF-8 & complete text UTF-8). -/
def validateFramePayload (frame : WsFrame) : Bool :=
  match frame.opcode with
  | .close =>
    if frame.payload.isEmpty then true
    else if frame.payload.size == 1 then false
    else
      let code : UInt16 := ((frame.payload.get! 0).toUInt16 <<< 8) ||| (frame.payload.get! 1).toUInt16
      let reasonBytes := frame.payload.extract 2 frame.payload.size
      isValidCloseCode code && (String.fromUTF8? reasonBytes).isSome
  | .text =>
    if frame.fin then (String.fromUTF8? frame.payload).isSome else true
  | _ => true

/-- Encode a `WsFrame` into RFC 6455 wire bytes:
    - Server-to-client frames pass `maskKey4? := none` (`masked = 0`).
    - Client-to-server frames pass `maskKey4? := some key4` (`masked = 1`, `key4.size == 4`).
    - Gated by `LeanSys.Spec.verifyWsFrameHeader` and `validateFramePayload`. -/
def encodeFrame? (frame : WsFrame) (maskKey4? : Option ByteArray := none)
    (maxFrameBytes : Nat := 4194304) : Option ByteArray := Id.run do
  if !validateFramePayload frame then
    return none
  let finBit : UInt8 := if frame.fin then 1 else 0
  let opByte := frame.opcode.toUInt8
  let (maskedBit, maskBytes) : UInt8 × ByteArray :=
    match maskKey4? with
    | none => (0, ByteArray.empty)
    | some k => if k.size == 4 then (1, k) else (2, ByteArray.empty)
  if maskedBit == 2 then return none
  let pLen := frame.payload.size
  let extLenBytes : Nat := if pLen ≤ 125 then 0 else if pLen ≤ 65535 then 2 else 8
  let hdrLen := 2 + extLenBytes + maskBytes.size
  if verifyWsFrameHeader finBit 0 opByte maskedBit maskedBit hdrLen.toUInt64 pLen.toUInt64 maxFrameBytes.toUInt64 != 1 then
    return none
  let mut out := ByteArray.emptyWithCapacity (hdrLen + pLen)
  out := out.push ((finBit <<< 7) ||| opByte)
  let maskFlagByte : UInt8 := maskedBit <<< 7
  if pLen ≤ 125 then
    out := out.push (maskFlagByte ||| pLen.toUInt8)
  else if pLen ≤ 65535 then
    out := out.push (maskFlagByte ||| 126)
      |>.push ((pLen >>> 8) &&& 0xFF).toUInt8
      |>.push (pLen &&& 0xFF).toUInt8
  else
    let u := pLen.toUInt64
    out := out.push (maskFlagByte ||| 127)
      |>.push ((u >>> 56) &&& 0xFF).toUInt8
      |>.push ((u >>> 48) &&& 0xFF).toUInt8
      |>.push ((u >>> 40) &&& 0xFF).toUInt8
      |>.push ((u >>> 32) &&& 0xFF).toUInt8
      |>.push ((u >>> 24) &&& 0xFF).toUInt8
      |>.push ((u >>> 16) &&& 0xFF).toUInt8
      |>.push ((u >>> 8) &&& 0xFF).toUInt8
      |>.push (u &&& 0xFF).toUInt8
  if maskedBit == 1 then
    out := out ++ maskBytes
    out := out ++ applyMask frame.payload maskBytes
  else
    out := out ++ frame.payload
  return some out

/-- Incremental non-blocking RFC 6455 frame decoder over `buf : ByteArray`:
    - `expectMasked = true` for server-side decoding of client frames; `false` for client-side decoding of server frames.
    - Returns `.ok none` when `buf` holds an incomplete frame header or payload within bounds (need more socket bytes).
    - Returns `.ok (some (frame, consumedBytes))` when a complete valid frame is decoded at `buf[0..consumedBytes)`.
    - Returns `.error reason` immediately when `verifyWsFrameHeader` or minimal-length encoding rules reject the header! -/
def decodeFramePrefix (buf : ByteArray) (expectMasked : Bool := true)
    (maxFrameBytes : Nat := 4194304) : Except String (Option (WsFrame × Nat)) := Id.run do
  if buf.size < 2 then
    return .ok none
  let b0 := buf.get! 0
  let b1 := buf.get! 1
  let finBit : UInt8 := (b0 >>> 7) &&& 1
  let rsvBits : UInt8 := (b0 >>> 4) &&& 0x7
  let opByte : UInt8 := b0 &&& 0xF
  let maskedBit : UInt8 := (b1 >>> 7) &&& 1
  let lenCode : Nat := (b1 &&& 0x7F).toNat
  let maskLen : Nat := if maskedBit == 1 then 4 else 0
  let extLen : Nat := if lenCode == 126 then 2 else if lenCode == 127 then 8 else 0
  let hdrLen : Nat := 2 + extLen + maskLen
  let expectMaskBit : UInt8 := if expectMasked then 1 else 0

  -- Fail fast on invalid flags/opcode/mask role even before extended length arrives if possible
  if rsvBits != 0 then
    return .error "ws_nonzero_rsv"
  if maskedBit != expectMaskBit then
    return .error "ws_mask_role_violation"
  let some opcode := WsOpcode.ofUInt8? opByte
    | return .error "ws_invalid_opcode"

  if buf.size < 2 + extLen then
    return .ok none

  let payloadLenU64 : UInt64 ←
    if lenCode ≤ 125 then
      pure lenCode.toUInt64
    else if lenCode == 126 then
      let v16 : UInt64 := ((buf.get! 2).toUInt64 <<< 8) ||| (buf.get! 3).toUInt64
      -- RFC 6455 §5.2: 16-bit extended length MUST encode values >= 126 (minimal length rule)
      if v16 < 126 then return .error "ws_non_minimal_length"
      pure v16
    else
      let hi := readWord32BE buf 2
      let lo := readWord32BE buf 6
      -- RFC 6455 §5.2: MSB of 64-bit length MUST be 0, and value MUST be >= 65536
      if (hi &&& 0x80000000) != 0 then return .error "ws_msb_length_set"
      let v64 : UInt64 := (hi.toUInt64 <<< 32) ||| lo.toUInt64
      if v64 < 65536 then return .error "ws_non_minimal_length"
      pure v64

  if verifyWsFrameHeader finBit rsvBits opByte maskedBit expectMaskBit
       hdrLen.toUInt64 payloadLenU64 maxFrameBytes.toUInt64 != 1 then
    return .error "ws_frame_header_rejected"

  let pLen := payloadLenU64.toNat
  let totalFrame := hdrLen + pLen
  if buf.size < totalFrame then
    return .ok none

  let rawPayload := buf.extract hdrLen totalFrame
  let unmasked :=
    if maskedBit == 1 then
      let maskKey := buf.extract (2 + extLen) hdrLen
      applyMask rawPayload maskKey
    else
      rawPayload
  let decoded : WsFrame := { fin := finBit == 1, opcode := opcode, payload := unmasked }
  if !validateFramePayload decoded then
    return .error "ws_invalid_payload"
  return .ok (some (decoded, totalFrame))

/-- Build a server-side `pong` response frame echoing a `ping` frame's payload (≤ 125 bytes). -/
def makeServerPong? (pingPayload : ByteArray) : Option ByteArray :=
  encodeFrame? { fin := true, opcode := .pong, payload := pingPayload } none 256

/-- Build a server-side `close` frame with an optional 16-bit RFC 6455 §7.4 status code (e.g. `1000` Normal Closure). -/
def makeServerClose? (statusCode : UInt16 := 1000) (reason : String := "") : Option ByteArray :=
  let reasonBytes := reason.toUTF8
  let hdr := (ByteArray.emptyWithCapacity (2 + reasonBytes.size)
    |>.push ((statusCode >>> 8) &&& 0xFF).toUInt8
    |>.push (statusCode &&& 0xFF).toUInt8)
  let body := hdr ++ reasonBytes
  encodeFrame? { fin := true, opcode := .close, payload := body } none 256

end LeanSys.WebSocket
