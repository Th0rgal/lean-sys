/-
  LeanSys.Auth: Constant-Time Token Verification, Rotation, SHA-256 / HMAC-SHA256 & Scoped Lease Gate
  (`0 import Lean`, `0 sorryAx`)
  - Constant-time byte-slice equality (`ctEqSlice`, `ctEqBytes`, `ctEqString`) without early exit on byte mismatch
  - Pure-Lean FIPS 180-4 SHA-256 (`sha256Slice`, `sha256Bytes`) and RFC 2104 / RFC 4231 HMAC-SHA256
    (`hmacSha256Slice`, `hmacSha256Bytes`, `hmacSha256Hex`) with zero OpenSSL / C-shim TCB symbols
  - One-step token rotation & scoped lease verifier gated by
    `LeanSys.Spec.verifyTokenAuth` (`leansys_verify_token_auth`)
-/
import LeanSys.Spec
import LeanSys.Posix
import LeanSys.Hash

namespace LeanSys.Auth

open LeanSys.Spec
open LeanSys.Posix
open LeanSys.Hash

/--
  Constant-time equality over two `ByteSlice` views:
  When lengths match, folds bitwise XOR across every byte without branching on byte values.
-/
def ctEqSlice (a b : ByteSlice) : Bool := Id.run do
  let effA := Nat.min a.len (a.ba.size - Nat.min a.off a.ba.size)
  let effB := Nat.min b.len (b.ba.size - Nat.min b.off b.ba.size)
  if a.len != b.len || effA != a.len || effB != b.len then
    return false
  let mut diff : UInt8 := 0
  for i in [0:a.len] do
    let ba := byteAt a.ba (a.off + i)
    let bb := byteAt b.ba (b.off + i)
    diff := diff ||| (ba ^^^ bb)
  return diff == 0

/-- Constant-time equality over two `ByteArray` buffers. -/
@[inline]
def ctEqBytes (a b : ByteArray) : Bool :=
  ctEqSlice (ByteSlice.ofByteArray a) (ByteSlice.ofByteArray b)

/-- Constant-time equality over two UTF-8 `String` values. -/
@[inline]
def ctEqString (a b : String) : Bool :=
  ctEqSlice (ByteSlice.ofString a) (ByteSlice.ofString b)

/-! ## Pure-Lean FIPS 180-4 SHA-256 & RFC 2104 / RFC 4231 HMAC-SHA256 (`0 SSL_`, `0 C LOC`) -/

@[inline]
private def rotr32 (x : UInt32) (n : UInt32) : UInt32 :=
  (x >>> n) ||| (x <<< (32 - n))

private def sha256K : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
]

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

/-- Compute the 32-byte FIPS 180-4 SHA-256 digest over a `ByteSlice`. -/
def sha256Slice (msg : ByteSlice) : ByteArray := Id.run do
  let effLen := Nat.min msg.len (msg.ba.size - Nat.min msg.off msg.ba.size)
  let bitLen : UInt64 := effLen.toUInt64 * 8
  let rem := (effLen + 9) % 64
  let padZeros := if rem == 0 then 0 else 64 - rem
  let totalLen := effLen + 1 + padZeros + 8
  let mut padded := ByteArray.emptyWithCapacity totalLen
  if effLen > 0 then
    padded := msg.ba.copySlice msg.off padded 0 effLen false
  padded := padded.push 0x80
  for _ in [0:padZeros] do
    padded := padded.push 0x00
  padded := pushWord32BE padded ((bitLen >>> 32) &&& 0xFFFFFFFF).toUInt32
  padded := pushWord32BE padded (bitLen &&& 0xFFFFFFFF).toUInt32

  let mut h0 : UInt32 := 0x6a09e667
  let mut h1 : UInt32 := 0xbb67ae85
  let mut h2 : UInt32 := 0x3c6ef372
  let mut h3 : UInt32 := 0xa54ff53a
  let mut h4 : UInt32 := 0x510e527f
  let mut h5 : UInt32 := 0x9b05688c
  let mut h6 : UInt32 := 0x1f83d9ab
  let mut h7 : UInt32 := 0x5be0cd19

  let blocks := padded.size / 64
  for blk in [0:blocks] do
    let base := blk * 64
    let mut w : Array UInt32 := Array.mkEmpty 64
    for t in [0:16] do
      w := w.push (readWord32BE padded (base + t * 4))
    for t in [16:64] do
      let w15 := w[t - 15]!
      let w2  := w[t - 2]!
      let s0  := rotr32 w15 7 ^^^ rotr32 w15 18 ^^^ (w15 >>> 3)
      let s1  := rotr32 w2 17 ^^^ rotr32 w2 19 ^^^ (w2 >>> 10)
      w := w.push (w[t - 16]! + s0 + w[t - 7]! + s1)

    let mut a := h0
    let mut b := h1
    let mut c := h2
    let mut d := h3
    let mut e := h4
    let mut f := h5
    let mut g := h6
    let mut h := h7

    for t in [0:64] do
      let bigS1 := rotr32 e 6 ^^^ rotr32 e 11 ^^^ rotr32 e 25
      let ch    := (e &&& f) ^^^ ((~~~e) &&& g)
      let temp1 := h + bigS1 + ch + sha256K[t]! + w[t]!
      let bigS0 := rotr32 a 2 ^^^ rotr32 a 13 ^^^ rotr32 a 22
      let maj   := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
      let temp2 := bigS0 + maj
      h := g
      g := f
      f := e
      e := d + temp1
      d := c
      c := b
      b := a
      a := temp1 + temp2

    h0 := h0 + a
    h1 := h1 + b
    h2 := h2 + c
    h3 := h3 + d
    h4 := h4 + e
    h5 := h5 + f
    h6 := h6 + g
    h7 := h7 + h

  let mut out := ByteArray.emptyWithCapacity 32
  out := pushWord32BE out h0
  out := pushWord32BE out h1
  out := pushWord32BE out h2
  out := pushWord32BE out h3
  out := pushWord32BE out h4
  out := pushWord32BE out h5
  out := pushWord32BE out h6
  out := pushWord32BE out h7
  return out

/-- Compute the 32-byte SHA-256 digest over a `ByteArray`. -/
@[inline]
def sha256Bytes (ba : ByteArray) : ByteArray :=
  sha256Slice (ByteSlice.ofByteArray ba)

/-- Compute the 32-byte RFC 2104 HMAC-SHA256 over `msg : ByteSlice` under `key : ByteSlice`. -/
def hmacSha256Slice (key msg : ByteSlice) : ByteArray := Id.run do
  let keyEffLen := Nat.min key.len (key.ba.size - Nat.min key.off key.ba.size)
  let normKey : ByteArray :=
    if keyEffLen > 64 then
      sha256Slice { ba := key.ba, off := key.off, len := keyEffLen }
    else
      key.ba.extract key.off (key.off + keyEffLen)
  let msgEffLen := Nat.min msg.len (msg.ba.size - Nat.min msg.off msg.ba.size)
  let mut innerIn := ByteArray.emptyWithCapacity (64 + msgEffLen)
  let mut outerPad := ByteArray.emptyWithCapacity 64
  for i in [0:64] do
    let kb : UInt8 := if i < normKey.size then normKey.get! i else 0
    innerIn := innerIn.push (kb ^^^ 0x36)
    outerPad := outerPad.push (kb ^^^ 0x5c)
  if msgEffLen > 0 then
    innerIn := msg.ba.copySlice msg.off innerIn 64 msgEffLen false
  let innerDigest := sha256Bytes innerIn
  let mut outerIn := ByteArray.emptyWithCapacity 96
  outerIn := outerPad.copySlice 0 outerIn 0 64 false
  outerIn := innerDigest.copySlice 0 outerIn 64 32 false
  return sha256Bytes outerIn

/-- Compute the 32-byte RFC 2104 HMAC-SHA256 over `ByteArray` key and message. -/
@[inline]
def hmacSha256Bytes (key msg : ByteArray) : ByteArray :=
  hmacSha256Slice (ByteSlice.ofByteArray key) (ByteSlice.ofByteArray msg)

/-- Render an arbitrary `ByteArray` as lowercase hexadecimal ASCII. -/
def bytesToHexLower (ba : ByteArray) : String := Id.run do
  let hexChars := "0123456789abcdef".toUTF8
  let mut out := ByteArray.emptyWithCapacity (ba.size * 2)
  for i in [0:ba.size] do
    let b := ba.get! i
    out := out.push (hexChars.get! ((b >>> 4).toNat &&& 0xF))
    out := out.push (hexChars.get! (b.toNat &&& 0xF))
  return String.fromUTF8! out

/-- Compute the 64-character lowercase hex HMAC-SHA256 tag over UTF-8 `secret` and `payload`. -/
@[inline]
def hmacSha256Hex (secret payload : String) : String :=
  bytesToHexLower (hmacSha256Slice (ByteSlice.ofString secret) (ByteSlice.ofString payload))

/-- Keyed 64-bit truncated HMAC-SHA256 tag over `payload : ByteSlice` using `secret : ByteSlice`
    (replaces invertible `xxh64` construction with the first 64 bits of cryptographic HMAC-SHA256). -/
def mac64Slice (secret payload : ByteSlice) : UInt64 :=
  let d := hmacSha256Slice secret payload
  ((byteAt d 0).toUInt64 <<< 56) |||
  ((byteAt d 1).toUInt64 <<< 48) |||
  ((byteAt d 2).toUInt64 <<< 40) |||
  ((byteAt d 3).toUInt64 <<< 32) |||
  ((byteAt d 4).toUInt64 <<< 24) |||
  ((byteAt d 5).toUInt64 <<< 16) |||
  ((byteAt d 6).toUInt64 <<< 8) |||
  (byteAt d 7).toUInt64

/-- Keyed 64-bit truncated HMAC-SHA256 tag over UTF-8 `secret` and `payload`. -/
@[inline]
def mac64 (secret payload : String) : UInt64 :=
  mac64Slice (ByteSlice.ofString secret) (ByteSlice.ofString payload)

/-- Verify all 6 official IETF RFC 4231 HMAC-SHA256 test vectors plus NIST FIPS 180-4 SHA-256 vectors. -/
def verifyRfc4231Vectors : Bool :=
  let sEmpty := bytesToHexLower (sha256Bytes ByteArray.empty) ==
    "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
  let sAbc := bytesToHexLower (sha256Slice (ByteSlice.ofString "abc")) ==
    "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
  let k1 := ByteArray.mk (Array.replicate 20 (0x0b : UInt8))
  let m1 := "Hi There".toUTF8
  let v1 := bytesToHexLower (hmacSha256Bytes k1 m1) ==
    "b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7"
  let v2 := hmacSha256Hex "Jefe" "what do ya want for nothing?" ==
    "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843"
  let k3 := ByteArray.mk (Array.replicate 20 (0xaa : UInt8))
  let m3 := ByteArray.mk (Array.replicate 50 (0xdd : UInt8))
  let v3 := bytesToHexLower (hmacSha256Bytes k3 m3) ==
    "773ea91e36800e46854db8ebd09181a72959098b3ef8c122d9635514ced565fe"
  let k4 := ByteArray.mk ((List.range 25).map (fun i => (i + 1).toUInt8)).toArray
  let m4 := ByteArray.mk (Array.replicate 50 (0xcd : UInt8))
  let v4 := bytesToHexLower (hmacSha256Bytes k4 m4) ==
    "82558a389a443c0ea4cc819899f2083a85f0faa3e578f8077a2e3ff46729665b"
  let k5 := ByteArray.mk (Array.replicate 131 (0xaa : UInt8))
  let m5 := "Test Using Larger Than Block-Size Key - Hash Key First".toUTF8
  let v5 := bytesToHexLower (hmacSha256Bytes k5 m5) ==
    "60e431591ee0b67f0d8a26aacbf5b77f8e0bc6213728c5140546040f0ee37f54"
  let m6 := "This is a test using a larger than block-size key and a larger than block-size data. The key needs to be hashed before being used by the HMAC algorithm.".toUTF8
  let v6 := bytesToHexLower (hmacSha256Bytes k5 m6) ==
    "9b09ffa71b942fcb27635fbcd5b0e944bfdc63644f0713938a7f51535c3a35e2"
  sEmpty && sAbc && v1 && v2 && v3 && v4 && v5 && v6

/-! ## Constant-Time Bearer Rotation & Cryptographic HMAC-SHA256 Scoped Leases -/

/--
  Verify a presented bearer token against `currentToken` and optional `previousToken?`
  (supporting zero-downtime rotation), gated by `leansys_verify_token_auth`.
-/
def verifyRotatedBearer (presented currentToken : String) (previousToken? : Option String := none) : Bool :=
  if presented.isEmpty || currentToken.isEmpty then
    false
  else
    let matchCur : UInt8 := if ctEqString presented currentToken then 1 else 0
    let (hasPrev, matchPrev) : UInt8 × UInt8 :=
      match previousToken? with
      | none => (0, 0)
      | some prev =>
        if prev.isEmpty then (0, 0)
        else (1, if ctEqString presented prev then 1 else 0)
    verifyTokenAuth matchCur hasPrev matchPrev 1 0 1 == 1

/-- Canonical length-delimited signing transcript preventing delimiter-collision forgery across fields. -/
@[inline]
def canonicalLeasePayload (nodeId scope : String) (expiresAt : UInt64) : ByteArray :=
  s!"lean-sys.lease.v2:{nodeId.utf8ByteSize}:{nodeId}:{scope.utf8ByteSize}:{scope}:{expiresAt}".toUTF8

/-- Scoped lease descriptor for node/worker execution authenticated by full 256-bit HMAC-SHA256 (`macHex` 64-char lowercase hex). -/
structure ScopedLease where
  nodeId    : String
  scope     : String
  expiresAt : UInt64
  macHex    : String
  deriving Repr, DecidableEq

/-- Mint a `ScopedLease` bound to `(nodeId, scope, expiresAt)` authenticated with 256-bit HMAC-SHA256 under `secret`. -/
def mintLease (secret nodeId scope : String) (expiresAt : UInt64) : ScopedLease :=
  let msg := canonicalLeasePayload nodeId scope expiresAt
  let tagHex := bytesToHexLower (hmacSha256Bytes secret.toUTF8 msg)
  { nodeId := nodeId, scope := scope, expiresAt := expiresAt, macHex := tagHex }

/--
  Validate a `ScopedLease` against `(expectedNode, expectedScope, nowEpoch)` and non-empty `secret`
  (with optional `previousSecret?`) using constant-time 256-bit HMAC-SHA256 comparison (`ctEqString`),
  gated by `leansys_verify_token_auth`.
  An empty current `secret` fails closed even when `previousSecret?` would match: rotation always installs a
  non-empty new secret, and clearing it must revoke (never silently fall back to) the previous secret,
  mirroring `verifyRotatedBearer`.
-/
def validateLease (lease : ScopedLease) (secret : String) (previousSecret? : Option String)
    (expectedNode expectedScope : String) (nowEpoch : UInt64) : Bool :=
  if secret.isEmpty || lease.macHex.utf8ByteSize != 64 then
    false
  else
    let msg := canonicalLeasePayload lease.nodeId lease.scope lease.expiresAt
    let expectedCur := bytesToHexLower (hmacSha256Bytes secret.toUTF8 msg)
    let matchCur : UInt8 := if ctEqString lease.macHex expectedCur then 1 else 0
    let (hasPrev, matchPrev) : UInt8 × UInt8 :=
      match previousSecret? with
      | none => (0, 0)
      | some prev =>
        if prev.isEmpty then (0, 0)
        else
          let expectedPrev := bytesToHexLower (hmacSha256Bytes prev.toUTF8 msg)
          (1, if ctEqString lease.macHex expectedPrev then 1 else 0)
    let scopeOk : UInt8 :=
      if ctEqString lease.nodeId expectedNode && ctEqString lease.scope expectedScope then 1 else 0
    verifyTokenAuth matchCur hasPrev matchPrev scopeOk nowEpoch lease.expiresAt == 1

end LeanSys.Auth
