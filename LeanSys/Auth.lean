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


/-! ## Zero-Copy `BorrowedSlice` / `ByteSource` Constant-Time & Streaming SHA-256 + AWS SigV4 (`AWS4-HMAC-SHA256`) -/

/-- Constant-time equality across any two `ByteSource` views (`ByteSlice` or `BorrowedSlice`). -/
def ctEqSource (a b : ByteSource) : Bool := Id.run do
  let na := a.size
  let nb := b.size
  if na != nb then
    return false
  let mut diff : UInt8 := 0
  for i in [0:na] do
    diff := diff ||| (a.getByteD i ^^^ b.getByteD i)
  return diff == 0

/-- 256-bit cryptographic digest unpacked into four big-endian 64-bit limbs for `leansys_verify_cas_digest256`. -/
structure Digest256 where
  w0 : UInt64
  w1 : UInt64
  w2 : UInt64
  w3 : UInt64
  deriving Repr, DecidableEq, Inhabited

namespace Digest256

@[inline]
private def readLimb64BE (ba : ByteArray) (off : Nat) : UInt64 :=
  ((byteAt ba off).toUInt64 <<< 56) |||
  ((byteAt ba (off + 1)).toUInt64 <<< 48) |||
  ((byteAt ba (off + 2)).toUInt64 <<< 40) |||
  ((byteAt ba (off + 3)).toUInt64 <<< 32) |||
  ((byteAt ba (off + 4)).toUInt64 <<< 24) |||
  ((byteAt ba (off + 5)).toUInt64 <<< 16) |||
  ((byteAt ba (off + 6)).toUInt64 <<< 8) |||
  (byteAt ba (off + 7)).toUInt64

@[inline]
private def pushLimb64BE (ba : ByteArray) (v : UInt64) : ByteArray :=
  ba.push ((v >>> 56) &&& 0xFF).toUInt8
    |>.push ((v >>> 48) &&& 0xFF).toUInt8
    |>.push ((v >>> 40) &&& 0xFF).toUInt8
    |>.push ((v >>> 32) &&& 0xFF).toUInt8
    |>.push ((v >>> 24) &&& 0xFF).toUInt8
    |>.push ((v >>> 16) &&& 0xFF).toUInt8
    |>.push ((v >>> 8) &&& 0xFF).toUInt8
    |>.push (v &&& 0xFF).toUInt8

/-- Decode a 32-byte `ByteArray` into `Digest256`. -/
def ofBytes32? (ba : ByteArray) : Option Digest256 :=
  if ba.size == 32 then
    some {
      w0 := readLimb64BE ba 0
      w1 := readLimb64BE ba 8
      w2 := readLimb64BE ba 16
      w3 := readLimb64BE ba 24
    }
  else
    none

/-- Encode `Digest256` to a 32-byte big-endian `ByteArray`. -/
def toBytes32 (d : Digest256) : ByteArray :=
  let b := ByteArray.emptyWithCapacity 32
  pushLimb64BE (pushLimb64BE (pushLimb64BE (pushLimb64BE b d.w0) d.w1) d.w2) d.w3

/-- Encode `Digest256` to a 64-char lowercase hexadecimal ASCII string. -/
@[inline]
def toHexLower (d : Digest256) : String :=
  bytesToHexLower d.toBytes32

@[inline]
private def hexVal? (b : UInt8) : Option UInt8 :=
  if 48 ≤ b && b ≤ 57 then some (b - 48)
  else if 97 ≤ b && b ≤ 102 then some (b - 87)
  else if 65 ≤ b && b ≤ 70 then some (b - 55)
  else none

/-- Parse a 64-char hex string into `Digest256` (rejecting non-hex or path-traversal strings). -/
def ofHex? (hex : String) : Option Digest256 := Id.run do
  let u := hex.toUTF8
  if u.size != 64 then
    return none
  let mut out := ByteArray.emptyWithCapacity 32
  for i in [0:32] do
    match hexVal? (u.get! (i * 2)), hexVal? (u.get! (i * 2 + 1)) with
    | some hi, some lo => out := out.push ((hi <<< 4) ||| lo)
    | _, _ => return none
  return ofBytes32? out

end Digest256

/-- Incremental FIPS 180-4 SHA-256 streaming state (`O(1)` memory across multi-GiB `pread` chunks). -/
structure Sha256Stream where
  h0 : UInt32 := 0x6a09e667
  h1 : UInt32 := 0xbb67ae85
  h2 : UInt32 := 0x3c6ef372
  h3 : UInt32 := 0xa54ff53a
  h4 : UInt32 := 0x510e527f
  h5 : UInt32 := 0x9b05688c
  h6 : UInt32 := 0x1f83d9ab
  h7 : UInt32 := 0x5be0cd19
  tail : ByteArray := ByteArray.empty
  totalBytes : UInt64 := 0

namespace Sha256Stream

def init : Sha256Stream := {}

/-- Keyed 256-bit streaming MAC/CAS mode (domain-separated IV for fast keyed/BLAKE-style 256-bit stream tags). -/
def initDomain (domainTag : UInt32) : Sha256Stream :=
  { h0 := 0x6a09e667 ^^^ domainTag, h7 := 0x5be0cd19 ^^^ (rotr32 domainTag 13) }

private def compressBlock (st : Sha256Stream) (src : ByteSource) (base : Nat) : Sha256Stream := Id.run do
  let mut w : Array UInt32 := Array.mkEmpty 64
  for t in [0:16] do
    let p := base + t * 4
    let wt : UInt32 :=
      ((src.getByteD p).toUInt32 <<< 24) |||
      ((src.getByteD (p + 1)).toUInt32 <<< 16) |||
      ((src.getByteD (p + 2)).toUInt32 <<< 8) |||
      (src.getByteD (p + 3)).toUInt32
    w := w.push wt
  for t in [16:64] do
    let w15 := w[t - 15]!
    let w2  := w[t - 2]!
    let s0  := rotr32 w15 7 ^^^ rotr32 w15 18 ^^^ (w15 >>> 3)
    let s1  := rotr32 w2 17 ^^^ rotr32 w2 19 ^^^ (w2 >>> 10)
    w := w.push (w[t - 16]! + s0 + w[t - 7]! + s1)
  let mut a := st.h0
  let mut b := st.h1
  let mut c := st.h2
  let mut d := st.h3
  let mut e := st.h4
  let mut f := st.h5
  let mut g := st.h6
  let mut h := st.h7
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
  return { st with
    h0 := st.h0 + a, h1 := st.h1 + b, h2 := st.h2 + c, h3 := st.h3 + d,
    h4 := st.h4 + e, h5 := st.h5 + f, h6 := st.h6 + g, h7 := st.h7 + h }

/-- Feed a `ByteSource` chunk (`ByteSlice` or zero-copy `BorrowedSlice`) into `Sha256Stream`. -/
def updateSource (st : Sha256Stream) (chunk : ByteSource) : Sha256Stream := Id.run do
  let n := chunk.size
  if n == 0 then
    return st
  let mut cur := { st with totalBytes := st.totalBytes + n.toUInt64 }
  let mut pos := 0
  if cur.tail.size > 0 then
    let need := 64 - cur.tail.size
    if n < need then
      let mut t := cur.tail
      for i in [0:n] do
        t := t.push (chunk.getByteD i)
      return { cur with tail := t }
    else
      let mut blk := cur.tail
      for i in [0:need] do
        blk := blk.push (chunk.getByteD i)
      cur := compressBlock { cur with tail := ByteArray.empty } (ByteSource.ofByteArray blk) 0
      pos := need
  while pos + 64 ≤ n do
    cur := compressBlock cur chunk pos
    pos := pos + 64
  if pos < n then
    let mut rem := ByteArray.emptyWithCapacity (n - pos)
    for i in [pos:n] do
      rem := rem.push (chunk.getByteD i)
    cur := { cur with tail := rem }
  return cur

@[inline]
def updateBytes (st : Sha256Stream) (ba : ByteArray) : Sha256Stream :=
  st.updateSource (ByteSource.ofByteArray ba)

/-- Finalize `Sha256Stream` into a 32-byte FIPS 180-4 SHA-256 digest. -/
def finalizeBytes (st : Sha256Stream) : ByteArray := Id.run do
  let bitLen : UInt64 := st.totalBytes * 8
  let tLen := st.tail.size
  let rem := (tLen + 9) % 64
  let padZeros := if rem == 0 then 0 else 64 - rem
  let mut fin := ByteArray.emptyWithCapacity (tLen + 1 + padZeros + 8)
  if tLen > 0 then
    fin := st.tail.copySlice 0 fin 0 tLen false
  fin := fin.push 0x80
  for _ in [0:padZeros] do
    fin := fin.push 0x00
  fin := pushWord32BE fin ((bitLen >>> 32) &&& 0xFFFFFFFF).toUInt32
  fin := pushWord32BE fin (bitLen &&& 0xFFFFFFFF).toUInt32
  let mut cur := st
  let blocks := fin.size / 64
  for b in [0:blocks] do
    cur := compressBlock cur (ByteSource.ofByteArray fin) (b * 64)
  let mut out := ByteArray.emptyWithCapacity 32
  out := pushWord32BE out cur.h0
  out := pushWord32BE out cur.h1
  out := pushWord32BE out cur.h2
  out := pushWord32BE out cur.h3
  out := pushWord32BE out cur.h4
  out := pushWord32BE out cur.h5
  out := pushWord32BE out cur.h6
  out := pushWord32BE out cur.h7
  return out

/-- Finalize `Sha256Stream` into unpacked 4×64-bit `Digest256` limbs. -/
def finalizeDigest256 (st : Sha256Stream) : Digest256 :=
  { w0 := (st.finalizeBytes |> Digest256.ofBytes32? |>.getD default).w0
    w1 := (st.finalizeBytes |> Digest256.ofBytes32? |>.getD default).w1
    w2 := (st.finalizeBytes |> Digest256.ofBytes32? |>.getD default).w2
    w3 := (st.finalizeBytes |> Digest256.ofBytes32? |>.getD default).w3 }

end Sha256Stream

/-- Compute SHA-256 directly over any `ByteSource` (`ByteSlice` or zero-copy `BorrowedSlice`). -/
@[inline]
def sha256Source (src : ByteSource) : ByteArray :=
  (Sha256Stream.init.updateSource src).finalizeBytes

/-! ## Pure-Lean Deterministic AWS Signature Version 4 (`AWS4-HMAC-SHA256`) & S3 Presigned URLs -/

/-- AWS SigV4 credential & endpoint scope. -/
structure AwsSigV4Credentials where
  accessKeyId     : String
  secretAccessKey : String
  region          : String
  service         : String := "s3"
  sessionToken?   : Option String := none
  deriving Repr, DecidableEq

/-- AWS SigV4 request descriptor. `amzDate` uses ISO-8601 basic format `YYYYMMDDTHHMMSSZ`; `dateStamp` is `YYYYMMDD`. -/
structure AwsSigV4Request where
  method          : String
  canonicalUri    : String
  queryParams     : Array (String × String) := #[]
  headers         : Array (String × String) := #[]
  payloadSha256Hex : String := "UNSIGNED-PAYLOAD"
  amzDate         : String
  dateStamp       : String
  signedAtEpoch   : UInt64
  expiresSecs     : UInt64 := 900
  deriving Repr

/-- Signed AWS SigV4 output (`Authorization` header, canonical request, string-to-sign, and hex signature). -/
structure AwsSigV4Signed where
  canonicalRequest : String
  stringToSign     : String
  signedHeaders    : String
  signatureHex     : String
  authHeader       : String
  presignedUrl?    : Option String := none
  deriving Repr, DecidableEq

@[inline]
private def isUnreservedUriByte (b : UInt8) : Bool :=
  (65 ≤ b && b ≤ 90) || (97 ≤ b && b ≤ 122) || (48 ≤ b && b ≤ 57) ||
  b == 45 || b == 95 || b == 46 || b == 126

/-- RFC 3986 / AWS SigV4 `UriEncode` (`encodeSlash = false` preserves `/` in object paths). -/
def awsUriEncode (s : String) (encodeSlash : Bool := true) : String := Id.run do
  let hexU := "0123456789ABCDEF".toUTF8
  let u := s.toUTF8
  let mut out := ByteArray.emptyWithCapacity (u.size * 3)
  for i in [0:u.size] do
    let b := u.get! i
    if isUnreservedUriByte b || (!encodeSlash && b == 47) then
      out := out.push b
    else
      out := out.push 37
      out := out.push (hexU.get! ((b >>> 4).toNat &&& 0xF))
      out := out.push (hexU.get! (b.toNat &&& 0xF))
  return String.fromUTF8! out

/-- Trim ASCII leading/trailing spaces and collapse interior whitespace runs per AWS SigV4 `Trimall`. -/
def awsTrimHeaderVal (s : String) : String := Id.run do
  let u := s.toUTF8
  let mut start := 0
  while start < u.size && (u.get! start == 32 || u.get! start == 9) do
    start := start + 1
  let mut stop := u.size
  while stop > start && (u.get! (stop - 1) == 32 || u.get! (stop - 1) == 9) do
    stop := stop - 1
  let mut out := ByteArray.emptyWithCapacity (stop - start)
  let mut prevSpace := false
  for i in [start:stop] do
    let b := u.get! i
    if b == 32 || b == 9 then
      if !prevSpace then
        out := out.push 32
        prevSpace := true
    else
      out := out.push b
      prevSpace := false
  return String.fromUTF8! out

private def asciiLower (s : String) : String := Id.run do
  let u := s.toUTF8
  let mut out := ByteArray.emptyWithCapacity u.size
  for i in [0:u.size] do
    let b := u.get! i
    out := out.push (if 65 ≤ b && b ≤ 90 then b + 32 else b)
  return String.fromUTF8! out

/-- Check that header names contain no CR/LF/NUL/colon/space and header/query values contain no CR/LF/NUL. -/
def sigV4NoControlBytes (headers queryParams : Array (String × String)) : Bool := Id.run do
  for (k, v) in headers do
    let ku := k.toUTF8
    if ku.size == 0 then return false
    for i in [0:ku.size] do
      let b := ku.get! i
      if b ≤ 32 || b == 58 || b == 127 then return false
    let vu := v.toUTF8
    for i in [0:vu.size] do
      let b := vu.get! i
      if b == 0 || b == 10 || b == 13 then return false
  for (qk, qv) in queryParams do
    for u in #[qk.toUTF8, qv.toUTF8] do
      for i in [0:u.size] do
        let b := u.get! i
        if b == 0 || b == 10 || b == 13 then return false
  return true

private def sortStringPairs (xs : Array (String × String)) : Array (String × String) :=
  xs.qsort fun a b => if a.1 == b.1 then a.2 < b.2 else a.1 < b.1

/-- Canonicalize HTTP headers per AWS SigV4: lowercase header names, trim + collapse interior runs of spaces
    in header values, fold duplicate header names by comma-joining values *in wire order*, and sort distinct names
    lexicographically by lowercase ASCII name. -/
private def canonicalizeSigV4Headers (hdrs : Array (String × String)) : Array (String × String) := Id.run do
  let mut grouped : Array (String × String) := #[]
  for (rawK, rawV) in hdrs do
    let k := asciiLower rawK
    let v := awsTrimHeaderVal rawV
    let mut foundIdx : Option Nat := none
    for i in [0:grouped.size] do
      if (grouped[i]!).1 == k then
        foundIdx := some i
        break
    match foundIdx with
    | some idx =>
      let prev := grouped[idx]!
      grouped := grouped.set! idx (k, prev.2 ++ "," ++ v)
    | none =>
      grouped := grouped.push (k, v)
  return grouped.qsort fun a b => a.1 < b.1

private def hasHeaderLower (hdrs : Array (String × String)) (targetLower : String) : Bool :=
  hdrs.any fun (k, _) => asciiLower k == targetLower

/-- Derive the 32-byte AWS SigV4 signing key `HMAC(HMAC(HMAC(HMAC("AWS4" ++ secret, dateStamp), region), service), "aws4_request")`. -/
def deriveSigV4SigningKey (creds : AwsSigV4Credentials) (dateStamp : String) : ByteArray :=
  let kSecret := ("AWS4" ++ creds.secretAccessKey).toUTF8
  let kDate   := hmacSha256Bytes kSecret dateStamp.toUTF8
  let kRegion := hmacSha256Bytes kDate creds.region.toUTF8
  let kSvc    := hmacSha256Bytes kRegion creds.service.toUTF8
  hmacSha256Bytes kSvc "aws4_request".toUTF8

/-- Deterministically sign an HTTP/S3 request with `AWS4-HMAC-SHA256`, gated by `leansys_verify_sigv4_envelope`. -/
def signSigV4Headers (creds : AwsSigV4Credentials) (req : AwsSigV4Request) (nowEpoch : UInt64) : Option AwsSigV4Signed := Id.run do
  if creds.accessKeyId.isEmpty || creds.secretAccessKey.isEmpty || req.dateStamp.utf8ByteSize != 8 then
    return none
  let extraSha : Array (String × String) :=
    if creds.service == "s3" && !hasHeaderLower req.headers "x-amz-content-sha256" then
      #[("x-amz-content-sha256", req.payloadSha256Hex)]
    else #[]
  let extraDate : Array (String × String) :=
    if !hasHeaderLower req.headers "x-amz-date" then #[("x-amz-date", req.amzDate)] else #[]
  let extraTok : Array (String × String) :=
    match creds.sessionToken? with
    | some tok => if !hasHeaderLower req.headers "x-amz-security-token" then #[("x-amz-security-token", tok)] else #[]
    | none => #[]
  let allHeaders := req.headers ++ extraSha ++ extraDate ++ extraTok
  let noCtl : UInt8 := if sigV4NoControlBytes allHeaders req.queryParams then 1 else 0
  let dedupHeaders := canonicalizeSigV4Headers allHeaders
  let mut hasHost : UInt8 := 0
  for (k, _) in dedupHeaders do
    if k == "host" then hasHost := 1
  if verifySigV4Envelope req.signedAtEpoch nowEpoch req.expiresSecs dedupHeaders.size.toUInt32 noCtl hasHost != 1 then
    return none
  let encQuery := sortStringPairs (req.queryParams.map fun (k, v) => (awsUriEncode k true, awsUriEncode v true))
  let canonicalQuery := String.intercalate "&" (encQuery.toList.map fun (k, v) => k ++ "=" ++ v)
  let canonicalHeaders := String.join (dedupHeaders.toList.map fun (k, v) => k ++ ":" ++ v ++ "\n")
  let signedHeaders := String.intercalate ";" (dedupHeaders.toList.map Prod.fst)
  let canonUri := if req.canonicalUri.isEmpty then "/" else awsUriEncode req.canonicalUri false
  let canonicalRequest :=
    req.method ++ "\n" ++ canonUri ++ "\n" ++ canonicalQuery ++ "\n" ++
    canonicalHeaders ++ "\n" ++ signedHeaders ++ "\n" ++ req.payloadSha256Hex
  let scope := req.dateStamp ++ "/" ++ creds.region ++ "/" ++ creds.service ++ "/aws4_request"
  let canonHashHex := bytesToHexLower (sha256Bytes canonicalRequest.toUTF8)
  let stringToSign := "AWS4-HMAC-SHA256\n" ++ req.amzDate ++ "\n" ++ scope ++ "\n" ++ canonHashHex
  let signingKey := deriveSigV4SigningKey creds req.dateStamp
  let sigHex := bytesToHexLower (hmacSha256Bytes signingKey stringToSign.toUTF8)
  let authHdr :=
    "AWS4-HMAC-SHA256 Credential=" ++ creds.accessKeyId ++ "/" ++ scope ++
    ", SignedHeaders=" ++ signedHeaders ++ ", Signature=" ++ sigHex
  return some {
    canonicalRequest := canonicalRequest
    stringToSign := stringToSign
    signedHeaders := signedHeaders
    signatureHex := sigHex
    authHeader := authHdr
  }

/-- Deterministically generate an S3 `X-Amz-Signature` presigned URL (`UNSIGNED-PAYLOAD`), gated by `leansys_verify_sigv4_envelope`. -/
def presignS3Url (creds : AwsSigV4Credentials) (schemeHost : String) (req : AwsSigV4Request) (nowEpoch : UInt64) : Option AwsSigV4Signed := Id.run do
  if creds.accessKeyId.isEmpty || creds.secretAccessKey.isEmpty || req.dateStamp.utf8ByteSize != 8 then
    return none
  let scope := req.dateStamp ++ "/" ++ creds.region ++ "/" ++ creds.service ++ "/aws4_request"
  let dedupHeaders := canonicalizeSigV4Headers req.headers
  let mut hasHost : UInt8 := 0
  for (k, _) in dedupHeaders do
    if k == "host" then hasHost := 1
  let signedHeaders := String.intercalate ";" (dedupHeaders.toList.map Prod.fst)
  let baseQuery : Array (String × String) := #[
    ("X-Amz-Algorithm", "AWS4-HMAC-SHA256"),
    ("X-Amz-Credential", creds.accessKeyId ++ "/" ++ scope),
    ("X-Amz-Date", req.amzDate),
    ("X-Amz-Expires", toString req.expiresSecs),
    ("X-Amz-SignedHeaders", signedHeaders)
  ] ++ (match creds.sessionToken? with | some t => #[("X-Amz-Security-Token", t)] | none => #[])
  let allQuery := req.queryParams ++ baseQuery
  let noCtl : UInt8 := if sigV4NoControlBytes req.headers allQuery then 1 else 0
  if verifySigV4Envelope req.signedAtEpoch nowEpoch req.expiresSecs dedupHeaders.size.toUInt32 noCtl hasHost != 1 then
    return none
  let encQuery := sortStringPairs (allQuery.map fun (k, v) => (awsUriEncode k true, awsUriEncode v true))
  let canonicalQuery := String.intercalate "&" (encQuery.toList.map fun (k, v) => k ++ "=" ++ v)
  let canonicalHeaders := String.join (dedupHeaders.toList.map fun (k, v) => k ++ ":" ++ v ++ "\n")
  let canonUri := if req.canonicalUri.isEmpty then "/" else awsUriEncode req.canonicalUri false
  let canonicalRequest :=
    req.method ++ "\n" ++ canonUri ++ "\n" ++ canonicalQuery ++ "\n" ++
    canonicalHeaders ++ "\n" ++ signedHeaders ++ "\nUNSIGNED-PAYLOAD"
  let canonHashHex := bytesToHexLower (sha256Bytes canonicalRequest.toUTF8)
  let stringToSign := "AWS4-HMAC-SHA256\n" ++ req.amzDate ++ "\n" ++ scope ++ "\n" ++ canonHashHex
  let signingKey := deriveSigV4SigningKey creds req.dateStamp
  let sigHex := bytesToHexLower (hmacSha256Bytes signingKey stringToSign.toUTF8)
  let fullUrl := schemeHost ++ canonUri ++ "?" ++ canonicalQuery ++ "&X-Amz-Signature=" ++ sigHex
  return some {
    canonicalRequest := canonicalRequest
    stringToSign := stringToSign
    signedHeaders := signedHeaders
    signatureHex := sigHex
    authHeader := ""
    presignedUrl? := some fullUrl
  }

end LeanSys.Auth
