/-
  LeanSys.Auth: Constant-Time Token Verification, Rotation & Scoped Lease Gate
  (`0 import Lean`, `0 sorryAx`)
  - Constant-time byte-slice equality (`ctEqSlice`, `ctEqString`) without early exit on byte mismatch
  - One-step token rotation & scoped lease verifier gated by
    `LeanSys.Spec.verifyTokenAuth` (`leansys_verify_token_auth`)
  - Keyed 64-bit MAC tag (`mac64Slice`) for lightweight internal node/session lease tokens
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
  if a.len != b.len then
    return false
  let mut diff : UInt8 := 0
  for i in [0:a.len] do
    let ba := byteAt a.ba (a.off + i)
    let bb := byteAt b.ba (b.off + i)
    diff := diff ||| (ba ^^^ bb)
  return diff == 0

/-- Constant-time equality over two UTF-8 `String` values. -/
@[inline]
def ctEqString (a b : String) : Bool :=
  ctEqSlice (ByteSlice.ofString a) (ByteSlice.ofString b)

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

/-- Keyed 64-bit MAC over `payload` using `secret` via two-pass `xxh64Slice` domain separation. -/
def mac64 (secret payload : String) : UInt64 :=
  let kHash := xxh64String secret 0x517CC1B727220A95
  xxh64Slice (ByteSlice.ofString payload) kHash

/-- Scoped lease descriptor for node/worker execution. -/
structure ScopedLease where
  nodeId    : String
  scope     : String
  expiresAt : UInt64
  tag       : UInt64
  deriving Repr, DecidableEq

/-- Mint a `ScopedLease` bound to `(nodeId, scope, expiresAt)` signed with `secret`. -/
def mintLease (secret nodeId scope : String) (expiresAt : UInt64) : ScopedLease :=
  let canonical := s!"{nodeId}|{scope}|{expiresAt}"
  { nodeId := nodeId, scope := scope, expiresAt := expiresAt, tag := mac64 secret canonical }

/--
  Validate a `ScopedLease` against `(expectedNode, expectedScope, nowEpoch)` and `secret`
  (with optional `previousSecret?`), gated by `leansys_verify_token_auth`.
-/
def validateLease (lease : ScopedLease) (secret : String) (previousSecret? : Option String)
    (expectedNode expectedScope : String) (nowEpoch : UInt64) : Bool :=
  let canonical := s!"{lease.nodeId}|{lease.scope}|{lease.expiresAt}"
  let expectedCur := mac64 secret canonical
  let matchCur : UInt8 := if lease.tag == expectedCur then 1 else 0
  let (hasPrev, matchPrev) : UInt8 × UInt8 :=
    match previousSecret? with
    | none => (0, 0)
    | some prev =>
      if prev.isEmpty then (0, 0)
      else (1, if lease.tag == mac64 prev canonical then 1 else 0)
  let scopeOk : UInt8 :=
    if ctEqString lease.nodeId expectedNode && ctEqString lease.scope expectedScope then 1 else 0
  verifyTokenAuth matchCur hasPrev matchPrev scopeOk nowEpoch lease.expiresAt == 1

end LeanSys.Auth
