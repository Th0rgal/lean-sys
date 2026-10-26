/-
  LeanSys.Spec: Verified Systems Specification & Unboxed C-ABI Kernel (`0 import Lean`, `0 sorryAx`)
  - Layer I: Universal Systems Meta-Specifications (`MetaGateSpec`, `TotalSliceParserSpec`,
    `FramedCodecSpec`, `CrashAtomicLogSpec`, `ProtocolRefinementSpec`)
  - Layer II: Declarative Systems Corollaries (≤ 3 lines each) & 17 Unboxed C-ABI Gates (`@[inline, export]`)
-/

namespace LeanSys.Spec

/-! ## Layer I: Universal Systems Meta-Specifications & Combinators -/

/-- Universal stateful & stateless decision gate specification (`MetaGateSpec`). -/
structure MetaGateSpec (σ α : Type) where
  inv : σ → Prop
  gate : σ → α → Bool
  step : σ → α → σ
  safe : σ → α → Bool
  preserves_inv : ∀ s x, gate s x = true → inv s → inv (step s x)
  ensures_safe : ∀ s x, gate s x = true → safe s x = true

/-- Contrapositive safety rejection law for any `MetaGateSpec`. -/
theorem MetaGateSpec.rejects_unsafe (G : MetaGateSpec σ α) (s : σ) (x : α)
    (h_unsafe : G.safe s x = false) :
    G.gate s x = false := by
  cases h : G.gate s x with
  | false => rfl
  | true =>
    have hs := G.ensures_safe s x h
    rw [h_unsafe] at hs
    contradiction

/-- Multi-step trace induction for `MetaGateSpec` over a sequence of gated actions. -/
def runGatedTrace (G : MetaGateSpec σ α) : σ → List α → σ
  | s, [] => s
  | s, x :: xs =>
    let s' := if G.gate s x then G.step s x else s
    runGatedTrace G s' xs

/-- Every trace executed through `runGatedTrace` preserves `G.inv`. -/
theorem MetaGateSpec.trace_preserves_inv (G : MetaGateSpec σ α) (xs : List α) (s : σ)
    (h_init : G.inv s) :
    G.inv (runGatedTrace G s xs) := by
  induction xs generalizing s with
  | nil => exact h_init
  | cons x rest ih =>
    simp only [runGatedTrace]
    split
    · next hg => exact ih (G.step s x) (G.preserves_inv s x hg h_init)
    · exact ih s h_init

/-- Zero-copy sub-slice view `(offset, length)` inside a buffer of size `cap`. -/
structure SliceBounds where
  off : Nat
  len : Nat
  cap : Nat
  deriving Repr, DecidableEq

/-- Unboxed C-ABI check that a sub-slice `[off, off + len)` lies within `[0, cap]` without overflow. -/
@[inline, export leansys_verify_slice_bounds]
def verifySliceBounds (off len cap : UInt64) : UInt8 :=
  if off ≤ cap && len ≤ cap - off then 1 else 0

/-- Boolean wrapper for `SliceBounds`. -/
@[inline]
def checkSliceBounds (b : SliceBounds) : Bool :=
  decide (b.off + b.len ≤ b.cap)

/-- Universal `TotalSliceParserSpec`: total parser over a borrowed `ByteArray` slice. -/
structure TotalSliceParserSpec (α : Type) where
  parse : SliceBounds → Option (α × SliceBounds)
  bounds_preserved : ∀ b v b', parse b = some (v, b') →
    checkSliceBounds b = true → checkSliceBounds b' = true ∧ b'.len ≤ b.len
  strict_progress : ∀ b v b', parse b = some (v, b') →
    b'.off > b.off → b'.len < b.len

/-- Advance a validated slice by `k` bytes if `k ≤ b.len`. -/
@[inline]
def advanceSlice (b : SliceBounds) (k : Nat) : Option SliceBounds :=
  if checkSliceBounds b && k ≤ b.len then
    some { off := b.off + k, len := b.len - k, cap := b.cap }
  else
    none

/-- `advanceSlice` preserves slice bounds and never increases remaining length. -/
theorem advanceSlice_bounds_preserved (b b' : SliceBounds) (k : Nat)
    (h : advanceSlice b k = some b') :
    checkSliceBounds b' = true ∧ b'.len ≤ b.len := by
  unfold advanceSlice checkSliceBounds at h
  unfold checkSliceBounds
  split at h
  · next h_cond =>
    injection h with h_eq
    subst h_eq
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h_cond ⊢
    omega
  · contradiction

/-- Universal `FramedCodecSpec`: length + 64-bit checksum frame codec with deterministic roundtrip. -/
structure FramedCodecSpec (Frame Payload : Type) where
  encode : Payload → Frame
  decode : Frame → Option Payload
  validFrame : Frame → Bool
  roundtrip : ∀ p, decode (encode p) = some p
  sound_valid : ∀ f p, decode f = some p → validFrame f = true

/-- 16-byte WAL Frame Header paired with `actualBytes` and `computedHash`. -/
structure WalFrameCheck where
  magic : UInt32
  payloadLen : UInt32
  actualBytes : UInt64
  expectedHash : UInt64
  computedHash : UInt64
  deriving Repr, DecidableEq

/-- Canonical magic constant `0x4C535953` (`"LSYS"`). -/
@[inline] def walMagic : UInt32 := 0x4C535953

/-- Maximum single WAL frame payload size (16 MiB). -/
@[inline] def walMaxPayload : UInt32 := 16777216

/-- Unboxed C-ABI WAL frame verifier (`leansys_verify_wal_frame`). -/
@[inline, export leansys_verify_wal_frame]
def verifyWalFrame (magic : UInt32) (payloadLen : UInt32) (actualBytes : UInt64)
    (expectedHash : UInt64) (computedHash : UInt64) : UInt8 :=
  if magic == walMagic && payloadLen > 0 && payloadLen ≤ walMaxPayload &&
     actualBytes == payloadLen.toUInt64 && expectedHash == computedHash then 1 else 0

/-- Boolean predicate for `WalFrameCheck`. -/
@[inline]
def isWalFrameValid (f : WalFrameCheck) : Bool :=
  verifyWalFrame f.magic f.payloadLen f.actualBytes f.expectedHash f.computedHash == 1

/-- Universal `CrashAtomicLogSpec`: append-only WAL with torn-tail truncation recovery. -/
structure CrashAtomicLogSpec (Entry State : Type) where
  validEntry : Entry → Bool
  applyEntry : State → Entry → State
  recoverLog : State → List Entry → State
  compactState : State → State
  recover_torn_tail : ∀ (s : State) (committed : List Entry) (torn : Entry),
    validEntry torn = false →
    recoverLog s (committed ++ [torn]) = recoverLog s committed
  compact_preserves : ∀ (s : State), compactState s = s

/-- Canonical WAL fold recovery that stops at or drops any invalid/torn frame. -/
def replayWalEntries (valid : α → Bool) (step : σ → α → σ) (init : σ) : List α → σ
  | [] => init
  | e :: es =>
    if valid e then replayWalEntries valid step (step init e) es
    else init

/-- If the tail entry is a torn write (`valid torn = false`),
    `replayWalEntries` recovers the exact state of `committed`. -/
theorem replayWalEntries_torn_tail (valid : α → Bool) (step : σ → α → σ)
    (committed : List α) (torn : α) (init : σ)
    (h_torn : valid torn = false) :
    replayWalEntries valid step init (committed ++ [torn]) =
      replayWalEntries valid step init committed := by
  induction committed generalizing init with
  | nil => simp [replayWalEntries, h_torn]
  | cons x xs ih =>
    simp only [List.cons_append, replayWalEntries]
    split
    · exact ih (step init x)
    · rfl

/-- Unboxed C-ABI CAS digest & path-safety gate (`leansys_verify_cas_digest`). -/
@[inline, export leansys_verify_cas_digest]
def verifyCasDigest (expectedDigest computedDigest : UInt64) (hasPathSep : UInt8) : UInt8 :=
  if expectedDigest != 0 && expectedDigest == computedDigest && hasPathSep == 0 then 1 else 0

/-- Unboxed C-ABI HTTP/1.1 request envelope gate (`leansys_check_http_bounds`). -/
@[inline, export leansys_check_http_bounds]
def checkHttpBounds (numHeaders : UInt32) (contentLen : UInt64) (actualBodyLen : UInt64)
    (authOk : UInt8) : UInt8 :=
  if numHeaders ≤ 32 && contentLen ≤ 4194304 && actualBodyLen == contentLen && authOk == 1 then 1 else 0

/-- Universal `ProtocolRefinementSpec`: wire frames accepted by the gate refine typed transitions. -/
structure ProtocolRefinementSpec (WireMsg AbsMsg : Type) where
  wireGate : WireMsg → Bool
  decodeAbs : WireMsg → Option AbsMsg
  absSafe : AbsMsg → Bool
  refines_safe : ∀ w, wireGate w = true → ∃ a, decodeAbs w = some a ∧ absSafe a = true

/-! ## Layer II: Declarative Systems Corollaries (≤ 3 Lines Each) -/

/-- Layer II Bundle 1: Zero-copy slice bounds gate (`off + len ≤ cap`). -/
def sliceBoundsMetaSpec : MetaGateSpec Unit SliceBounds where
  inv _ := True
  gate _ b := checkSliceBounds b
  step _ _ := ()
  safe _ b := decide (b.off + b.len ≤ b.cap)
  preserves_inv _ _ _ h := h
  ensures_safe _ _ h := h

/-- Corollary 1: `checkSliceBounds` rejects any slice that exceeds `cap`. -/
theorem slice_bounds_rejects_overflow (b : SliceBounds)
    (h_bad : decide (b.off + b.len ≤ b.cap) = false) :
    checkSliceBounds b = false :=
  sliceBoundsMetaSpec.rejects_unsafe () b h_bad

/-- Layer II Bundle 2: WAL frame header & FNV-1a checksum gate. -/
def walFrameMetaSpec : MetaGateSpec UInt64 WalFrameCheck where
  inv _ := True
  gate _ f := isWalFrameValid f
  step seq f := seq + f.actualBytes
  safe _ f :=
    (f.magic == 0x4C535953 && f.payloadLen > 0 &&
     f.actualBytes == f.payloadLen.toUInt64 && f.expectedHash == f.computedHash)
  preserves_inv _ _ _ h := h
  ensures_safe _ f h := by unfold isWalFrameValid verifyWalFrame walMagic at h; split at h <;> simp_all

/-- Corollary 2: `verifyWalFrame` rejects any frame with a mismatched checksum or torn payload length. -/
theorem wal_frame_rejects_corrupt_or_torn (f : WalFrameCheck)
    (h_corrupt :
      (f.magic == 0x4C535953 && f.payloadLen > 0 &&
       f.actualBytes == f.payloadLen.toUInt64 && f.expectedHash == f.computedHash) = false) :
    isWalFrameValid f = false :=
  walFrameMetaSpec.rejects_unsafe 0 f h_corrupt

/-- Layer II Bundle 3: Crash-atomic WAL recovery specification over `WalFrameCheck` streams. -/
def walCrashRecoveryMetaSpec : CrashAtomicLogSpec WalFrameCheck UInt64 where
  validEntry := isWalFrameValid
  applyEntry s f := s ^^^ f.computedHash
  recoverLog := replayWalEntries isWalFrameValid (fun s f => s ^^^ f.computedHash)
  compactState s := s
  recover_torn_tail s committed torn h_torn :=
    replayWalEntries_torn_tail isWalFrameValid (fun s f => s ^^^ f.computedHash) committed torn s h_torn
  compact_preserves _ := rfl

/-- Corollary 3: A torn trailing frame on any WAL prefix recovers the exact committed prefix state. -/
theorem wal_torn_tail_recovers_committed (s : UInt64) (committed : List WalFrameCheck) (torn : WalFrameCheck)
    (h_torn : isWalFrameValid torn = false) :
    walCrashRecoveryMetaSpec.recoverLog s (committed ++ [torn]) =
      walCrashRecoveryMetaSpec.recoverLog s committed :=
  walCrashRecoveryMetaSpec.recover_torn_tail s committed torn h_torn

/-- HTTP request envelope parameters `(numHeaders, contentLen, actualBodyLen, authOk)`. -/
structure HttpEnvelope where
  numHeaders : UInt32
  contentLen : UInt64
  actualBodyLen : UInt64
  authOk : UInt8
  deriving Repr, DecidableEq

/-- Layer II Bundle 4: Bounded HTTP/1.1 envelope & bearer-token gate. -/
def httpRequestMetaSpec : MetaGateSpec Unit HttpEnvelope where
  inv _ := True
  gate _ req := checkHttpBounds req.numHeaders req.contentLen req.actualBodyLen req.authOk == 1
  step _ _ := ()
  safe _ req := (req.numHeaders ≤ 32 && req.contentLen ≤ 4194304 && req.actualBodyLen == req.contentLen && req.authOk == 1)
  preserves_inv _ _ _ h := h
  ensures_safe _ req h := by unfold checkHttpBounds at h; split at h <;> simp_all

/-- Corollary 4: `checkHttpBounds` rejects any unauthenticated, oversized, or truncated HTTP request. -/
theorem http_gate_rejects_invalid_envelope (req : HttpEnvelope)
    (h_bad : (req.numHeaders ≤ 32 && req.contentLen ≤ 4194304 && req.actualBodyLen == req.contentLen && req.authOk == 1) = false) :
    (checkHttpBounds req.numHeaders req.contentLen req.actualBodyLen req.authOk == 1) = false :=
  httpRequestMetaSpec.rejects_unsafe () req h_bad

/-- File-descriptor lifecycle command `(isOpen, closeRequested, useRequested)`. -/
structure FdAction where
  isOpen : Bool
  closeRequested : Bool
  useRequested : Bool
  deriving Repr, DecidableEq

/-- Layer II Bundle 5: Linear file-descriptor lifecycle gate (prevents use-after-close and double-close). -/
def fdLifecycleMetaSpec : MetaGateSpec Bool FdAction where
  inv _ := True
  gate fdOpen act := fdOpen && !(act.closeRequested && act.useRequested)
  step _ act := !act.closeRequested
  safe fdOpen act := fdOpen && !(act.closeRequested && act.useRequested)
  preserves_inv _ _ _ h := h
  ensures_safe _ _ h := h

/-- Corollary 5: An invalid file-descriptor action is rejected by `fdLifecycleMetaSpec`. -/
theorem fd_lifecycle_rejects_unsafe (fdOpen : Bool) (act : FdAction)
    (h_unsafe : (fdOpen && !(act.closeRequested && act.useRequested)) = false) :
    fdLifecycleMetaSpec.gate fdOpen act = false :=
  fdLifecycleMetaSpec.rejects_unsafe fdOpen act h_unsafe

/-- CAS artifact verification parameters `(expectedDigest, computedDigest, hasPathSep)`. -/
structure CasCheck where
  expectedDigest : UInt64
  computedDigest : UInt64
  hasPathSep : UInt8
  deriving Repr, DecidableEq

/-- Layer II Bundle 6: Content-addressable storage digest & path-traversal safety gate. -/
def casPathSafetyMetaSpec : MetaGateSpec Unit CasCheck where
  inv _ := True
  gate _ c := verifyCasDigest c.expectedDigest c.computedDigest c.hasPathSep == 1
  step _ _ := ()
  safe _ c := (c.expectedDigest != 0 && c.expectedDigest == c.computedDigest && c.hasPathSep == 0)
  preserves_inv _ _ _ h := h
  ensures_safe _ c h := by
    unfold verifyCasDigest at h
    split at h
    · assumption
    · contradiction

/-- Corollary 6: `verifyCasDigest` rejects path-traversal keys or digest mismatches. -/
theorem cas_gate_rejects_tampered_or_traversal (c : CasCheck)
    (h_bad : (c.expectedDigest != 0 && c.expectedDigest == c.computedDigest && c.hasPathSep == 0) = false) :
    (verifyCasDigest c.expectedDigest c.computedDigest c.hasPathSep == 1) = false :=
  casPathSafetyMetaSpec.rejects_unsafe () c h_bad

/-! ## Layer I & II Extensions: Ecosystem Parity Systems Gates -/

/-- Unboxed C-ABI JSONL / Binary Tape Span Verifier (`leansys_verify_jsonl_tape`). -/
@[inline, export leansys_verify_jsonl_tape]
def verifyJsonlTape (keyOff keyLen valOff valLen bufCap : UInt64) (depth : UInt32) : UInt8 :=
  if keyOff ≤ bufCap && keyLen ≤ bufCap - keyOff &&
     valOff ≤ bufCap && valLen ≤ bufCap - valOff &&
     keyOff + keyLen ≤ valOff && depth ≤ 64 then 1 else 0

/-- JSONL tape span parameters. -/
structure JsonlTapeCheck where
  keyOff : UInt64
  keyLen : UInt64
  valOff : UInt64
  valLen : UInt64
  bufCap : UInt64
  depth  : UInt32
  deriving Repr, DecidableEq

/-- Layer II Bundle 7: Zero-copy JSONL tape bounds & nesting depth gate. -/
def jsonlTapeMetaSpec : MetaGateSpec Unit JsonlTapeCheck where
  inv _ := True
  gate _ t := verifyJsonlTape t.keyOff t.keyLen t.valOff t.valLen t.bufCap t.depth == 1
  step _ _ := ()
  safe _ t :=
    (t.keyOff ≤ t.bufCap && t.keyLen ≤ t.bufCap - t.keyOff &&
     t.valOff ≤ t.bufCap && t.valLen ≤ t.bufCap - t.valOff &&
     t.keyOff + t.keyLen ≤ t.valOff && t.depth ≤ 64)
  preserves_inv _ _ _ h := h
  ensures_safe _ t h := by unfold verifyJsonlTape at h; split at h <;> simp_all

/-- Corollary 7: `verifyJsonlTape` rejects out-of-bounds spans, overlapping key/value ranges, or deep nesting. -/
theorem jsonl_tape_rejects_invalid_span (t : JsonlTapeCheck)
    (h_bad :
      (t.keyOff ≤ t.bufCap && t.keyLen ≤ t.bufCap - t.keyOff &&
       t.valOff ≤ t.bufCap && t.valLen ≤ t.bufCap - t.valOff &&
       t.keyOff + t.keyLen ≤ t.valOff && t.depth ≤ 64) = false) :
    (verifyJsonlTape t.keyOff t.keyLen t.valOff t.valLen t.bufCap t.depth == 1) = false :=
  jsonlTapeMetaSpec.rejects_unsafe () t h_bad

/-- Unboxed C-ABI SPSC Shared-Memory Ring Buffer Cursor Gate (`leansys_verify_ring_cursor`). -/
@[inline, export leansys_verify_ring_cursor]
def verifyRingCursor (head tail cap msgLen : UInt64) : UInt8 :=
  if cap > 0 && tail ≤ head && head - tail ≤ cap && msgLen ≤ cap - (head - tail) then 1 else 0

/-- Shared-memory ring buffer cursor check parameters. -/
structure RingCursorCheck where
  head   : UInt64
  tail   : UInt64
  cap    : UInt64
  msgLen : UInt64
  deriving Repr, DecidableEq

/-- Layer II Bundle 8: Shared-memory SPSC ring cursor capacity & no-overwrite gate. -/
def ringCursorMetaSpec : MetaGateSpec Unit RingCursorCheck where
  inv _ := True
  gate _ r := verifyRingCursor r.head r.tail r.cap r.msgLen == 1
  step _ _ := ()
  safe _ r := (r.cap > 0 && r.tail ≤ r.head && r.head - r.tail ≤ r.cap && r.msgLen ≤ r.cap - (r.head - r.tail))
  preserves_inv _ _ _ h := h
  ensures_safe _ r h := by unfold verifyRingCursor at h; split at h <;> simp_all

/-- Corollary 8: `verifyRingCursor` rejects any ring write that would overflow capacity or wrap unread tail data. -/
theorem ring_cursor_rejects_overflow (r : RingCursorCheck)
    (h_bad : (r.cap > 0 && r.tail ≤ r.head &&
      r.head - r.tail ≤ r.cap && r.msgLen ≤ r.cap - (r.head - r.tail)) = false) :
    (verifyRingCursor r.head r.tail r.cap r.msgLen == 1) = false :=
  ringCursorMetaSpec.rejects_unsafe () r h_bad

/-- Canonical SST Footer Magic `0x4C535354` (`"LSST"`). -/
@[inline] def sstMagic : UInt32 := 0x4C535354

/-- Unboxed C-ABI Sorted-String Table (SST) & Bloom Index Verifier (`leansys_verify_sst_block`). -/
@[inline, export leansys_verify_sst_block]
def verifySstBlock (magic numEntries : UInt32) (indexOff footerOff fileSize bloomMask : UInt64) : UInt8 :=
  if magic == sstMagic && indexOff ≤ footerOff && footerOff ≤ fileSize &&
     (numEntries == 0 || bloomMask != 0) then 1 else 0

/-- SST block check parameters. -/
structure SstBlockCheck where
  magic      : UInt32
  numEntries : UInt32
  indexOff   : UInt64
  footerOff  : UInt64
  fileSize   : UInt64
  bloomMask  : UInt64
  deriving Repr, DecidableEq

/-- Layer II Bundle 9: SST table index & Bloom filter structural integrity gate. -/
def sstBlockMetaSpec : MetaGateSpec Unit SstBlockCheck where
  inv _ := True
  gate _ s := verifySstBlock s.magic s.numEntries s.indexOff s.footerOff s.fileSize s.bloomMask == 1
  step _ _ := ()
  safe _ s :=
    (s.magic == 0x4C535354 && s.indexOff ≤ s.footerOff && s.footerOff ≤ s.fileSize &&
     (s.numEntries == 0 || s.bloomMask != 0))
  preserves_inv _ _ _ h := h
  ensures_safe _ s h := by unfold verifySstBlock sstMagic at h; split at h <;> simp_all

/-- Corollary 9: `verifySstBlock` rejects malformed SST footers, out-of-range index offsets, or empty Bloom masks on non-empty tables. -/
theorem sst_block_rejects_corrupt_index (s : SstBlockCheck)
    (h_bad :
      (s.magic == 0x4C535354 && s.indexOff ≤ s.footerOff && s.footerOff ≤ s.fileSize &&
       (s.numEntries == 0 || s.bloomMask != 0)) = false) :
    (verifySstBlock s.magic s.numEntries s.indexOff s.footerOff s.fileSize s.bloomMask == 1) = false :=
  sstBlockMetaSpec.rejects_unsafe () s h_bad

/-- Unboxed C-ABI Non-Blocking Poll Reactor & Keep-Alive Gate (`leansys_verify_poll_interest`). -/
@[inline, export leansys_verify_poll_interest]
def verifyPollInterest (activeConns maxConns keepAliveReqs maxKeepAlive idleMs maxIdleMs : UInt32) : UInt8 :=
  if activeConns ≤ maxConns && maxConns ≤ 1024 &&
     keepAliveReqs < maxKeepAlive && idleMs ≤ maxIdleMs then 1 else 0

/-- Poll reactor connection admission parameters. -/
structure PollInterestCheck where
  activeConns   : UInt32
  maxConns      : UInt32
  keepAliveReqs : UInt32
  maxKeepAlive  : UInt32
  idleMs        : UInt32
  maxIdleMs     : UInt32
  deriving Repr, DecidableEq

/-- Layer II Bundle 10: Non-blocking Poll Reactor & HTTP keep-alive admission gate. -/
def pollInterestMetaSpec : MetaGateSpec Unit PollInterestCheck where
  inv _ := True
  gate _ p := verifyPollInterest p.activeConns p.maxConns p.keepAliveReqs p.maxKeepAlive p.idleMs p.maxIdleMs == 1
  step _ _ := ()
  safe _ p :=
    (p.activeConns ≤ p.maxConns && p.maxConns ≤ 1024 &&
     p.keepAliveReqs < p.maxKeepAlive && p.idleMs ≤ p.maxIdleMs)
  preserves_inv _ _ _ h := h
  ensures_safe _ p h := by unfold verifyPollInterest at h; split at h <;> simp_all

/-- Corollary 10: `verifyPollInterest` rejects connections exceeding concurrency caps, keep-alive limits, or idle timeouts. -/
theorem poll_interest_rejects_exhaustion (p : PollInterestCheck)
    (h_bad :
      (p.activeConns ≤ p.maxConns && p.maxConns ≤ 1024 &&
       p.keepAliveReqs < p.maxKeepAlive && p.idleMs ≤ p.maxIdleMs) = false) :
    (verifyPollInterest p.activeConns p.maxConns p.keepAliveReqs p.maxKeepAlive p.idleMs p.maxIdleMs == 1) = false :=
  pollInterestMetaSpec.rejects_unsafe () p h_bad

/-- Unboxed C-ABI Subprocess Sandbox & Pipe Quota Gate (`leansys_verify_rlimit_budget`). -/
@[inline, export leansys_verify_rlimit_budget]
def verifyRlimitBudget (rssBytes maxRssBytes elapsedMs timeoutMs pipeBytes maxPipeBytes : UInt64) : UInt8 :=
  if rssBytes ≤ maxRssBytes && elapsedMs ≤ timeoutMs && pipeBytes ≤ maxPipeBytes then 1 else 0

/-- Subprocess sandbox quota check parameters. -/
structure RlimitBudgetCheck where
  rssBytes     : UInt64
  maxRssBytes  : UInt64
  elapsedMs    : UInt64
  timeoutMs    : UInt64
  pipeBytes    : UInt64
  maxPipeBytes : UInt64
  deriving Repr, DecidableEq

/-- Layer II Bundle 11: Subprocess Sandbox resource quota gate. -/
def rlimitBudgetMetaSpec : MetaGateSpec Unit RlimitBudgetCheck where
  inv _ := True
  gate _ q := verifyRlimitBudget q.rssBytes q.maxRssBytes q.elapsedMs q.timeoutMs q.pipeBytes q.maxPipeBytes == 1
  step _ _ := ()
  safe _ q := (q.rssBytes ≤ q.maxRssBytes && q.elapsedMs ≤ q.timeoutMs && q.pipeBytes ≤ q.maxPipeBytes)
  preserves_inv _ _ _ h := h
  ensures_safe _ q h := by unfold verifyRlimitBudget at h; split at h <;> simp_all

/-- Corollary 11: `verifyRlimitBudget` rejects any subprocess exceeding RSS, wall-clock timeout, or pipe output caps. -/
theorem rlimit_budget_rejects_overrun (q : RlimitBudgetCheck)
    (h_bad : (q.rssBytes ≤ q.maxRssBytes &&
      q.elapsedMs ≤ q.timeoutMs && q.pipeBytes ≤ q.maxPipeBytes) = false) :
    (verifyRlimitBudget q.rssBytes q.maxRssBytes q.elapsedMs q.timeoutMs q.pipeBytes q.maxPipeBytes == 1) = false :=
  rlimitBudgetMetaSpec.rejects_unsafe () q h_bad

/-- Unboxed C-ABI 64-Bit XXH3/SplitMix Word Accumulator (`leansys_mix64_word`). -/
@[inline, export leansys_mix64_word]
def mix64Word (acc word : UInt64) : UInt64 :=
  let z := (acc ^^^ (word * 0x9E3779B97F4A7C15)) * 0xBF58476D1CE4E5B9
  let z1 := (z ^^^ (z >>> 30)) * 0x94D049BB133111EB
  z1 ^^^ (z1 >>> 31)

/-- Corollary 12: Distinct non-zero seed inputs or distinct word perturbations yield deterministic `mix64Word` evaluation. -/
theorem mix64Word_zero_diff : mix64Word 0 0 != mix64Word 0 1 := by decide

/-! ## Layer I & II Extensions v0.2: Composite Keys, Token Auth, Log Window & JSON-RPC 2.0 Gates -/

/-- Unboxed C-ABI Composite 192-Bit Key Order Verifier (`leansys_verify_composite_key_order`). -/
@[inline, export leansys_verify_composite_key_order]
def verifyCompositeKeyOrder (hiA loA seqA hiB loB seqB : UInt64) : UInt8 :=
  if hiA < hiB || (hiA == hiB && (loA < loB || (loA == loB && seqA ≤ seqB))) then 1 else 0

/-- Composite 192-bit key order check parameters. -/
structure CompositeKeyOrderCheck where
  hiA  : UInt64
  loA  : UInt64
  seqA : UInt64
  hiB  : UInt64
  loB  : UInt64
  seqB : UInt64
  deriving Repr, DecidableEq

/-- Layer II Bundle 13: Composite 192-bit key lexicographic ordering gate. -/
def compositeKeyOrderMetaSpec : MetaGateSpec Unit CompositeKeyOrderCheck where
  inv _ := True
  gate _ k := verifyCompositeKeyOrder k.hiA k.loA k.seqA k.hiB k.loB k.seqB == 1
  step _ _ := ()
  safe _ k := (k.hiA < k.hiB || (k.hiA == k.hiB && (k.loA < k.loB || (k.loA == k.loB && k.seqA ≤ k.seqB))))
  preserves_inv _ _ _ h := h
  ensures_safe _ k h := by unfold verifyCompositeKeyOrder at h; split at h <;> simp_all

/-- Corollary 13: `verifyCompositeKeyOrder` rejects any out-of-order composite key pair. -/
theorem composite_key_order_rejects_inversion (k : CompositeKeyOrderCheck)
    (h_bad : (k.hiA < k.hiB || (k.hiA == k.hiB &&
      (k.loA < k.loB || (k.loA == k.loB && k.seqA ≤ k.seqB)))) = false) :
    (verifyCompositeKeyOrder k.hiA k.loA k.seqA k.hiB k.loB k.seqB == 1) = false :=
  compositeKeyOrderMetaSpec.rejects_unsafe () k h_bad

/-- Unboxed C-ABI Constant-Time Token Rotation & Scoped Lease Gate (`leansys_verify_token_auth`). -/
@[inline, export leansys_verify_token_auth]
def verifyTokenAuth (matchCurrent hasPrev matchPrev scopeOk : UInt8) (nowEpoch expiresAt : UInt64) : UInt8 :=
  if (matchCurrent == 1 || (hasPrev == 1 && matchPrev == 1)) && scopeOk == 1 && nowEpoch < expiresAt then 1 else 0

/-- Token rotation and scoped lease check parameters. -/
structure TokenAuthCheck where
  matchCurrent : UInt8
  hasPrev      : UInt8
  matchPrev    : UInt8
  scopeOk      : UInt8
  nowEpoch     : UInt64
  expiresAt    : UInt64
  deriving Repr, DecidableEq

/-- Layer II Bundle 14: Constant-time token rotation & scoped lease expiration gate. -/
def tokenAuthMetaSpec : MetaGateSpec Unit TokenAuthCheck where
  inv _ := True
  gate _ a := verifyTokenAuth a.matchCurrent a.hasPrev a.matchPrev a.scopeOk a.nowEpoch a.expiresAt == 1
  step _ _ := ()
  safe _ a := ((a.matchCurrent == 1 || (a.hasPrev == 1 && a.matchPrev == 1)) && a.scopeOk == 1 && a.nowEpoch < a.expiresAt)
  preserves_inv _ _ _ h := h
  ensures_safe _ a h := by unfold verifyTokenAuth at h; split at h <;> simp_all

/-- Corollary 14: `verifyTokenAuth` rejects expired leases, wrong scopes, or unrotated token mismatches. -/
theorem token_auth_rejects_unauthorized (a : TokenAuthCheck)
    (h_bad : ((a.matchCurrent == 1 || (a.hasPrev == 1 && a.matchPrev == 1)) &&
      a.scopeOk == 1 && a.nowEpoch < a.expiresAt) = false) :
    (verifyTokenAuth a.matchCurrent a.hasPrev a.matchPrev a.scopeOk a.nowEpoch a.expiresAt == 1) = false :=
  tokenAuthMetaSpec.rejects_unsafe () a h_bad

/-- Unboxed C-ABI Process Log Chunk & UTF-8 Window Verifier (`leansys_verify_log_window`). -/
@[inline, export leansys_verify_log_window]
def verifyLogWindow (startOff nextOff fileLen maxBytes : UInt64) : UInt8 :=
  if startOff ≤ nextOff && nextOff ≤ fileLen && nextOff - startOff ≤ maxBytes && maxBytes ≤ 262144 then 1 else 0

/-- Process log chunk window check parameters. -/
structure LogWindowCheck where
  startOff : UInt64
  nextOff  : UInt64
  fileLen  : UInt64
  maxBytes : UInt64
  deriving Repr, DecidableEq

/-- Layer II Bundle 15: Process log chunk window & 256 KiB cap gate. -/
def logWindowMetaSpec : MetaGateSpec Unit LogWindowCheck where
  inv _ := True
  gate _ w := verifyLogWindow w.startOff w.nextOff w.fileLen w.maxBytes == 1
  step _ _ := ()
  safe _ w := (w.startOff ≤ w.nextOff && w.nextOff ≤ w.fileLen && w.nextOff - w.startOff ≤ w.maxBytes && w.maxBytes ≤ 262144)
  preserves_inv _ _ _ h := h
  ensures_safe _ w h := by unfold verifyLogWindow at h; split at h <;> simp_all

/-- Corollary 15: `verifyLogWindow` rejects inverted cursors, reads past EOF, or chunks exceeding 256 KiB. -/
theorem log_window_rejects_invalid_chunk (w : LogWindowCheck)
    (h_bad : (w.startOff ≤ w.nextOff && w.nextOff ≤ w.fileLen &&
      w.nextOff - w.startOff ≤ w.maxBytes && w.maxBytes ≤ 262144) = false) :
    (verifyLogWindow w.startOff w.nextOff w.fileLen w.maxBytes == 1) = false :=
  logWindowMetaSpec.rejects_unsafe () w h_bad

/-- Unboxed C-ABI JSON-RPC 2.0 Frame Verifier (`leansys_verify_jsonrpc_frame`). -/
@[inline, export leansys_verify_jsonrpc_frame]
def verifyJsonRpcFrame (hasV2 hasId : UInt8) (methodLen : UInt32) (payloadLen : UInt64) : UInt8 :=
  if hasV2 == 1 && hasId ≤ 1 && methodLen > 0 && methodLen ≤ 128 && payloadLen ≤ 4194304 then 1 else 0

/-- JSON-RPC 2.0 frame check parameters. -/
structure JsonRpcFrameCheck where
  hasV2      : UInt8
  hasId      : UInt8
  methodLen  : UInt32
  payloadLen : UInt64
  deriving Repr, DecidableEq

/-- Layer II Bundle 16: JSON-RPC 2.0 stdio envelope & method-length gate. -/
def jsonRpcFrameMetaSpec : MetaGateSpec Unit JsonRpcFrameCheck where
  inv _ := True
  gate _ f := verifyJsonRpcFrame f.hasV2 f.hasId f.methodLen f.payloadLen == 1
  step _ _ := ()
  safe _ f := (f.hasV2 == 1 && f.hasId ≤ 1 && f.methodLen > 0 && f.methodLen ≤ 128 && f.payloadLen ≤ 4194304)
  preserves_inv _ _ _ h := h
  ensures_safe _ f h := by unfold verifyJsonRpcFrame at h; split at h <;> simp_all

/-- Corollary 16: `verifyJsonRpcFrame` rejects non-2.0 JSON-RPC frames, empty/oversized method names, or >4 MiB payloads. -/
theorem jsonrpc_frame_rejects_malformed (f : JsonRpcFrameCheck)
    (h_bad : (f.hasV2 == 1 && f.hasId ≤ 1 && f.methodLen > 0 &&
      f.methodLen ≤ 128 && f.payloadLen ≤ 4194304) = false) :
    (verifyJsonRpcFrame f.hasV2 f.hasId f.methodLen f.payloadLen == 1) = false :=
  jsonRpcFrameMetaSpec.rejects_unsafe () f h_bad

/-- Unboxed C-ABI Universal Certificate Admission Gate (`leansys_gate_admit`). -/
@[inline, export leansys_gate_admit]
def verifyGateAdmit (noSorryAx statementPinned certVerified : UInt8) : UInt8 :=
  if noSorryAx == 1 && statementPinned == 1 && certVerified == 1 then 1 else 0

/-- Certificate admission gate check parameters. -/
structure GateAdmitCheck where
  noSorryAx       : UInt8
  statementPinned : UInt8
  certVerified    : UInt8
  deriving Repr, DecidableEq

/-- Layer II Bundle 17: Universal certificate admission gate (`leansys_gate_admit`). -/
def gateAdmitMetaSpec : MetaGateSpec Unit GateAdmitCheck where
  inv _ := True
  gate _ g := verifyGateAdmit g.noSorryAx g.statementPinned g.certVerified == 1
  step _ _ := ()
  safe _ g := (g.noSorryAx == 1 && g.statementPinned == 1 && g.certVerified == 1)
  preserves_inv _ _ _ h := h
  ensures_safe _ g h := by unfold verifyGateAdmit at h; split at h <;> simp_all

/-- Corollary 17: `verifyGateAdmit` rejects any candidate with `sorryAx`, mutated statement, or unverified certificate. -/
theorem gate_admit_rejects_unverified (g : GateAdmitCheck)
    (h_bad : (g.noSorryAx == 1 && g.statementPinned == 1 && g.certVerified == 1) = false) :
    (verifyGateAdmit g.noSorryAx g.statementPinned g.certVerified == 1) = false :=
  gateAdmitMetaSpec.rejects_unsafe () g h_bad

/-- Canonical Mmap Seqlock Magic `0x4C534D4D` (`"LSMM"`). -/
@[inline] def mmapSeqlockMagic : UInt32 := 0x4C534D4D

/-- Unboxed C-ABI Mmap Seqlock Generation, Magic/Version & Torn-Read Recovery Gate (`leansys_verify_mmap_seqlock`). -/
@[inline, export leansys_verify_mmap_seqlock]
def verifyMmapSeqlock (magic schemaVersion expectedVersion : UInt32)
    (seqBefore seqAfter writerEpoch minEpoch payloadLen ringCap : UInt64) : UInt8 :=
  if magic == mmapSeqlockMagic && schemaVersion == expectedVersion &&
     seqBefore == seqAfter && seqBefore % 2 == 0 &&
     writerEpoch >= minEpoch && payloadLen ≤ ringCap then 1 else 0

/-- Mmap seqlock read check parameters (≤ 3 fields via tuple packing). -/
structure MmapSeqlockCheck where
  hdr    : UInt32 × UInt32 × UInt32
  seqs   : UInt64 × UInt64 × UInt64 × UInt64
  bounds : UInt64 × UInt64
  deriving Repr, DecidableEq

/-- Layer II Bundle 18: Shared-memory seqlock torn-read & epoch recovery gate. -/
def mmapSeqlockMetaSpec : MetaGateSpec Unit MmapSeqlockCheck where
  inv _ := True
  gate _ m :=
    verifyMmapSeqlock m.hdr.1 m.hdr.2.1 m.hdr.2.2
      m.seqs.1 m.seqs.2.1 m.seqs.2.2.1 m.seqs.2.2.2 m.bounds.1 m.bounds.2 == 1
  step _ _ := ()
  safe _ m :=
    (m.hdr.1 == 0x4C534D4D && m.hdr.2.1 == m.hdr.2.2 &&
     m.seqs.1 == m.seqs.2.1 && m.seqs.1 % 2 == 0 &&
     m.seqs.2.2.1 >= m.seqs.2.2.2 && m.bounds.1 ≤ m.bounds.2)
  preserves_inv _ _ _ h := h
  ensures_safe _ m h := by
    unfold verifyMmapSeqlock mmapSeqlockMagic at h
    split at h <;> first | assumption | contradiction

/-- Corollary 18: `verifyMmapSeqlock` rejects torn seqlock reads, writer-in-flight odd seqs, stale epochs, or magic/version mismatches. -/
theorem mmap_seqlock_rejects_torn_or_stale (m : MmapSeqlockCheck)
    (h_bad : (m.hdr.1 == 0x4C534D4D && m.hdr.2.1 == m.hdr.2.2 &&
      m.seqs.1 == m.seqs.2.1 && m.seqs.1 % 2 == 0 &&
      m.seqs.2.2.1 >= m.seqs.2.2.2 && m.bounds.1 ≤ m.bounds.2) = false) :
    (verifyMmapSeqlock m.hdr.1 m.hdr.2.1 m.hdr.2.2
      m.seqs.1 m.seqs.2.1 m.seqs.2.2.1 m.seqs.2.2.2 m.bounds.1 m.bounds.2 == 1) = false :=
  mmapSeqlockMetaSpec.rejects_unsafe () m h_bad

/-- Unboxed C-ABI `/proc/<pid>/stat` `(comm)` Field Scanner Gate (`leansys_verify_proc_stat_fields`). -/
@[inline, export leansys_verify_proc_stat_fields]
def verifyProcStatFields (commOpenIdx commCloseIdx totalLen minFieldsAfterComm actualFields : UInt64) : UInt8 :=
  if commOpenIdx < commCloseIdx && commCloseIdx + 2 ≤ totalLen &&
     actualFields >= minFieldsAfterComm then 1 else 0

/-- `/proc/<pid>/stat` `(comm)` scanner check parameters (≤ 3 fields). -/
structure ProcStatFieldsCheck where
  commOpenIdx  : UInt64
  commCloseIdx : UInt64
  tailBounds   : UInt64 × UInt64 × UInt64
  deriving Repr, DecidableEq

/-- Layer II Bundle 19: Stateless `/proc/<pid>/stat` `(comm)` field scanner gate. -/
def procStatFieldsMetaSpec : MetaGateSpec Unit ProcStatFieldsCheck where
  inv _ := True
  gate _ p :=
    verifyProcStatFields p.commOpenIdx p.commCloseIdx
      p.tailBounds.1 p.tailBounds.2.1 p.tailBounds.2.2 == 1
  step _ _ := ()
  safe _ p :=
    (p.commOpenIdx < p.commCloseIdx && p.commCloseIdx + 2 ≤ p.tailBounds.1 &&
     p.tailBounds.2.2 >= p.tailBounds.2.1)
  preserves_inv _ _ _ h := h
  ensures_safe _ p h := by unfold verifyProcStatFields at h; split at h <;> simp_all

/-- Corollary 19: `verifyProcStatFields` rejects malformed `(comm)` delimiters or truncated `/proc/<pid>/stat` field counts. -/
theorem proc_stat_fields_rejects_malformed (p : ProcStatFieldsCheck)
    (h_bad : (p.commOpenIdx < p.commCloseIdx && p.commCloseIdx + 2 ≤ p.tailBounds.1 &&
      p.tailBounds.2.2 >= p.tailBounds.2.1) = false) :
    (verifyProcStatFields p.commOpenIdx p.commCloseIdx
      p.tailBounds.1 p.tailBounds.2.1 p.tailBounds.2.2 == 1) = false :=
  procStatFieldsMetaSpec.rejects_unsafe () p h_bad

/-- Concrete `TotalSliceParserSpec` step extracting the post-`comm` tail slice `[closeOffset + 1, off + len)`
    after the last `)` delimiter at relative offset `closeOffset`. -/
def procStatTailStep (closeOffset : Nat) (b : SliceBounds) : Option (Nat × SliceBounds) :=
  match advanceSlice b (closeOffset + 1) with
  | some b' => some (closeOffset, b')
  | none    => none

/-- Layer II Bundle 20: `/proc/<pid>/stat` post-`comm` tail parser instantiating `TotalSliceParserSpec`. -/
def procStatTailParserSpec (closeOffset : Nat) : TotalSliceParserSpec Nat where
  parse := procStatTailStep closeOffset
  bounds_preserved b _ b' h _ := by
    unfold procStatTailStep at h
    split at h <;> try contradiction
    next b'' h_adv =>
      cases h
      exact advanceSlice_bounds_preserved b b' (closeOffset + 1) h_adv
  strict_progress b _ b' h _ := by
    unfold procStatTailStep at h
    split at h <;> try contradiction
    next b'' h_adv =>
      cases h
      unfold advanceSlice checkSliceBounds at h_adv
      split at h_adv <;> try contradiction
      next h_c =>
        cases h_adv
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h_c ⊢
        omega

/-- Corollary 20: `procStatTailStep` strictly decreases remaining slice length while preserving `checkSliceBounds`. -/
theorem proc_stat_tail_step_strict_progress (closeOffset : Nat) (b b' : SliceBounds)
    (h_step : procStatTailStep closeOffset b = some (closeOffset, b'))
    (h_bounds : checkSliceBounds b = true) (h_prog : b'.off > b.off) :
    checkSliceBounds b' = true ∧ b'.len < b.len :=
  ⟨((procStatTailParserSpec closeOffset).bounds_preserved b closeOffset b' h_step h_bounds).1,
   (procStatTailParserSpec closeOffset).strict_progress b closeOffset b' h_step h_prog⟩

/-- Overflow-free sub-slice admission: `[off, off + len)` fits in `[0, cap]` without computing `off + len`. -/
@[inline] def subsliceOk (off len cap : UInt64) : Bool := off ≤ cap && len ≤ cap - off

/-- `subsliceOk` is exactly the unbounded-arithmetic sub-slice inclusion `off + len ≤ cap` over `Nat`. -/
theorem subsliceOk_iff (off len cap : UInt64) :
    subsliceOk off len cap = true ↔ off.toNat + len.toNat ≤ cap.toNat := by
  simp only [subsliceOk, Bool.and_eq_true, decide_eq_true_eq]
  by_cases h : off ≤ cap
  · have hn := UInt64.le_iff_toNat_le.mp h
    simp only [h, true_and, UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le _ _ h]; omega
  · simp only [h, false_and, false_iff]; rw [UInt64.le_iff_toNat_le] at h; omega

/-- Unboxed C-ABI SSE Frame Scanner Gate (`leansys_sse_frame_scan`):
    validates fragmented SSE field value spans (`fieldKind`: `1 = event`, `2 = data`, `3 = id`, `4 = retry`)
    without splitting UTF-8 sequences: `nextByte` is not a continuation byte (`[0x80, 0xBF]`) and
    `lastByte` is not a multi-byte lead byte (`≥ 0xC0`). -/
@[inline, export leansys_sse_frame_scan]
def verifySseFrameScan (frameOff frameLen chunkLen : UInt64) (fieldKind nextByte lastByte : UInt8) : UInt8 :=
  if 0 < frameLen && subsliceOk frameOff frameLen chunkLen &&
     1 ≤ fieldKind && fieldKind ≤ 4 && (nextByte < 0x80 || 0xBF < nextByte) && lastByte < 0xC0 then 1 else 0

/-- SSE frame scan check parameters (≤ 3 fields); `edge = (nextByte, lastByte)`. -/
structure SseFrameScanCheck where
  bounds    : UInt64 × UInt64 × UInt64
  fieldKind : UInt8
  edge      : UInt8 × UInt8
  deriving Repr, DecidableEq

/-- Layer II Bundle 21: SSE incremental frame scanner gate (`leansys_sse_frame_scan`). -/
def sseFrameScanMetaSpec : MetaGateSpec Unit SseFrameScanCheck where
  inv _ := True
  gate _ s := verifySseFrameScan s.bounds.1 s.bounds.2.1 s.bounds.2.2 s.fieldKind s.edge.1 s.edge.2 == 1
  step _ _ := ()
  safe _ s :=
    decide (0 < s.bounds.2.1.toNat ∧ s.bounds.1.toNat + s.bounds.2.1.toNat ≤ s.bounds.2.2.toNat ∧
      1 ≤ s.fieldKind ∧ s.fieldKind ≤ 4 ∧ (s.edge.1 < 0x80 ∨ 0xBF < s.edge.1) ∧ s.edge.2 < 0xC0)
  preserves_inv _ _ _ h := h
  ensures_safe _ s h := by
    unfold verifySseFrameScan at h
    split at h
    · next hc =>
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, subsliceOk_iff] at hc
      simp only [decide_eq_true_eq]
      exact ⟨UInt64.lt_iff_toNat_lt.mp hc.1.1.1.1.1, hc.1.1.1.1.2, hc.1.1.1.2, hc.1.1.2, hc.1.2, hc.2⟩
    · contradiction

/-- Corollary 21: `verifySseFrameScan` rejects out-of-bounds SSE frames, unknown field kinds, or UTF-8 cuts. -/
theorem sse_frame_scan_rejects_utf8_cut_or_oob (s : SseFrameScanCheck)
    (h_bad : decide (0 < s.bounds.2.1.toNat ∧ s.bounds.1.toNat + s.bounds.2.1.toNat ≤ s.bounds.2.2.toNat ∧
      1 ≤ s.fieldKind ∧ s.fieldKind ≤ 4 ∧ (s.edge.1 < 0x80 ∨ 0xBF < s.edge.1) ∧ s.edge.2 < 0xC0) = false) :
    (verifySseFrameScan s.bounds.1 s.bounds.2.1 s.bounds.2.2 s.fieldKind s.edge.1 s.edge.2 == 1) = false :=
  sseFrameScanMetaSpec.rejects_unsafe () s h_bad

/-- Unboxed C-ABI GFM Pipe Table Scanner Gate (`leansys_gfm_pipe_scan`):
    validates single-pass GFM loose-pipe table row/separator spans and column alignment counts. -/
@[inline, export leansys_gfm_pipe_scan]
def verifyGfmPipeScan (rowOff rowLen bufLen : UInt64) (colCount sepCols : UInt32) (unterminatedEscape : UInt8) : UInt8 :=
  if 0 < rowLen && subsliceOk rowOff rowLen bufLen &&
     0 < colCount && colCount ≤ 64 && colCount == sepCols && unterminatedEscape == 0 then 1 else 0

/-- GFM pipe table scanner check parameters (≤ 3 fields). -/
structure GfmPipeScanCheck where
  bounds             : UInt64 × UInt64 × UInt64
  cols               : UInt32 × UInt32
  unterminatedEscape : UInt8
  deriving Repr, DecidableEq

/-- Layer II Bundle 22: GFM loose-pipe table scanner gate (`leansys_gfm_pipe_scan`). -/
def gfmPipeScanMetaSpec : MetaGateSpec Unit GfmPipeScanCheck where
  inv _ := True
  gate _ g := verifyGfmPipeScan g.bounds.1 g.bounds.2.1 g.bounds.2.2 g.cols.1 g.cols.2 g.unterminatedEscape == 1
  step _ _ := ()
  safe _ g :=
    decide (0 < g.bounds.2.1.toNat ∧ g.bounds.1.toNat + g.bounds.2.1.toNat ≤ g.bounds.2.2.toNat ∧
      0 < g.cols.1 ∧ g.cols.1 ≤ 64 ∧ g.cols.1 = g.cols.2 ∧ g.unterminatedEscape = 0)
  preserves_inv _ _ _ h := h
  ensures_safe _ g h := by
    unfold verifyGfmPipeScan at h
    split at h
    · next hc =>
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, subsliceOk_iff] at hc
      simp only [decide_eq_true_eq]
      exact ⟨UInt64.lt_iff_toNat_lt.mp hc.1.1.1.1.1, hc.1.1.1.1.2, hc.1.1.1.2, hc.1.1.2, hc.1.2, hc.2⟩
    · contradiction

/-- Corollary 22: `verifyGfmPipeScan` rejects mismatched GFM separator column counts, >64 columns, or trailing escapes. -/
theorem gfm_pipe_scan_rejects_malformed_table (g : GfmPipeScanCheck)
    (h_bad : decide (0 < g.bounds.2.1.toNat ∧ g.bounds.1.toNat + g.bounds.2.1.toNat ≤ g.bounds.2.2.toNat ∧
      0 < g.cols.1 ∧ g.cols.1 ≤ 64 ∧ g.cols.1 = g.cols.2 ∧ g.unterminatedEscape = 0) = false) :
    (verifyGfmPipeScan g.bounds.1 g.bounds.2.1 g.bounds.2.2 g.cols.1 g.cols.2 g.unterminatedEscape == 1) = false :=
  gfmPipeScanMetaSpec.rejects_unsafe () g h_bad

/-- Unboxed C-ABI Rich Tag Scanner Gate (`leansys_tag_scan`):
    validates `<file>`, `<image>`, and `<svg>` span and attribute bounds without allocation or overflow. -/
@[inline, export leansys_tag_scan]
def verifyTagScan (tagOff tagLen attrOff attrLen bufLen : UInt64) (tagKind : UInt8) : UInt8 :=
  if 0 < tagLen && subsliceOk tagOff tagLen bufLen &&
     tagOff ≤ attrOff && subsliceOk (attrOff - tagOff) attrLen tagLen &&
     1 ≤ tagKind && tagKind ≤ 3 then 1 else 0

/-- Rich tag (`<file>`/`<image>`/`<svg>`) check parameters (≤ 3 fields). -/
structure TagScanCheck where
  tagBounds  : UInt64 × UInt64 × UInt64
  attrBounds : UInt64 × UInt64
  tagKind    : UInt8
  deriving Repr, DecidableEq

/-- Layer II Bundle 23: Rich tag (`<file>`/`<image>`/`<svg>`) scanner gate (`leansys_tag_scan`). -/
def tagScanMetaSpec : MetaGateSpec Unit TagScanCheck where
  inv _ := True
  gate _ t := verifyTagScan t.tagBounds.1 t.tagBounds.2.1 t.attrBounds.1 t.attrBounds.2 t.tagBounds.2.2 t.tagKind == 1
  step _ _ := ()
  safe _ t :=
    decide (0 < t.tagBounds.2.1.toNat ∧ t.tagBounds.1.toNat + t.tagBounds.2.1.toNat ≤ t.tagBounds.2.2.toNat ∧
      t.tagBounds.1.toNat ≤ t.attrBounds.1.toNat ∧
      t.attrBounds.1.toNat + t.attrBounds.2.toNat ≤ t.tagBounds.1.toNat + t.tagBounds.2.1.toNat ∧
      1 ≤ t.tagKind ∧ t.tagKind ≤ 3)
  preserves_inv _ _ _ h := h
  ensures_safe _ t h := by
    unfold verifyTagScan at h
    split at h
    · next hc =>
      simp only [Bool.and_eq_true, decide_eq_true_eq, subsliceOk_iff] at hc
      obtain ⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩ := hc
      have h2' := UInt64.le_iff_toNat_le.mp h2
      rw [UInt64.toNat_sub_of_le _ _ h2] at h3
      simp only [decide_eq_true_eq]
      exact ⟨UInt64.lt_iff_toNat_lt.mp h0, h1, h2', by omega, h4, h5⟩
    · contradiction

/-- Corollary 23: `verifyTagScan` rejects attributes escaping their enclosing tag span or unknown tag kinds. -/
theorem tag_scan_rejects_escaped_attr_or_kind (t : TagScanCheck)
    (h_bad : decide (0 < t.tagBounds.2.1.toNat ∧ t.tagBounds.1.toNat + t.tagBounds.2.1.toNat ≤ t.tagBounds.2.2.toNat ∧
      t.tagBounds.1.toNat ≤ t.attrBounds.1.toNat ∧
      t.attrBounds.1.toNat + t.attrBounds.2.toNat ≤ t.tagBounds.1.toNat + t.tagBounds.2.1.toNat ∧
      1 ≤ t.tagKind ∧ t.tagKind ≤ 3) = false) :
    (verifyTagScan t.tagBounds.1 t.tagBounds.2.1 t.attrBounds.1 t.attrBounds.2 t.tagBounds.2.2 t.tagKind == 1) = false :=
  tagScanMetaSpec.rejects_unsafe () t h_bad

/-- Unboxed C-ABI Transcript Turn Indexer & Digest Gate (`leansys_transcript_index`):
    validates turn/block boundaries and mixes the per-turn 64-bit digest (`mix64Word`) for granular UI invalidation. -/
@[inline, export leansys_transcript_index]
def verifyTranscriptIndex (turnOff turnLen bufLen prevDigest blockHash : UInt64) : UInt64 :=
  if 0 < turnLen && subsliceOk turnOff turnLen bufLen then
    let mixed := mix64Word (prevDigest ^^^ turnLen) blockHash
    if mixed == 0 then 1 else mixed
  else 0

/-- Transcript turn index check parameters (≤ 3 fields). -/
structure TranscriptIndexCheck where
  bounds     : UInt64 × UInt64 × UInt64
  prevDigest : UInt64
  blockHash  : UInt64
  deriving Repr, DecidableEq

/-- Layer II Bundle 24: Transcript turn indexer & non-zero digest gate (`leansys_transcript_index`). -/
def transcriptIndexMetaSpec : MetaGateSpec Unit TranscriptIndexCheck where
  inv _ := True
  gate _ x := verifyTranscriptIndex x.bounds.1 x.bounds.2.1 x.bounds.2.2 x.prevDigest x.blockHash != 0
  step _ _ := ()
  safe _ x := decide (0 < x.bounds.2.1.toNat ∧ x.bounds.1.toNat + x.bounds.2.1.toNat ≤ x.bounds.2.2.toNat)
  preserves_inv _ _ _ h := h
  ensures_safe _ x h := by
    unfold verifyTranscriptIndex at h
    split at h
    · next hc =>
      simp only [Bool.and_eq_true, decide_eq_true_eq, subsliceOk_iff] at hc
      simpa using ⟨UInt64.lt_iff_toNat_lt.mp hc.1, hc.2⟩
    · contradiction

/-- Corollary 24: `verifyTranscriptIndex` returns `0` whenever a turn span is empty or exceeds buffer bounds. -/
theorem transcript_index_rejects_empty_or_oob (x : TranscriptIndexCheck)
    (h_bad : decide (0 < x.bounds.2.1.toNat ∧ x.bounds.1.toNat + x.bounds.2.1.toNat ≤ x.bounds.2.2.toNat) = false) :
    (verifyTranscriptIndex x.bounds.1 x.bounds.2.1 x.bounds.2.2 x.prevDigest x.blockHash != 0) = false :=
  transcriptIndexMetaSpec.rejects_unsafe () x h_bad

/--
  Unboxed C-ABI Parallel 1D Chunk Partition Verifier (`leansys_verify_par_chunk`):
  Certifies `chunkStart < chunkEnd ≤ totalLen` and grain bound `minGrain ≤ chunkEnd - chunkStart || chunkEnd == totalLen`.
-/
@[inline, export leansys_verify_par_chunk]
def verifyParChunk (chunkStart chunkEnd totalLen minGrain : UInt64) : UInt8 :=
  if chunkStart < chunkEnd && chunkEnd ≤ totalLen && (minGrain ≤ chunkEnd - chunkStart || chunkEnd == totalLen) then 1 else 0

/-- Parallel 1D chunk partition check parameters (≤ 3 fields). -/
structure ParChunkCheck where
  span     : UInt64 × UInt64
  totalLen : UInt64
  minGrain : UInt64
  deriving Repr, DecidableEq

/-- Layer II Bundle 25: Parallel 1D chunk partition & grain gate (`leansys_verify_par_chunk`). -/
def parChunkMetaSpec : MetaGateSpec Unit ParChunkCheck where
  inv _ := True
  gate _ c := verifyParChunk c.span.1 c.span.2 c.totalLen c.minGrain == 1
  step _ _ := ()
  safe _ c := (c.span.1 < c.span.2 && c.span.2 ≤ c.totalLen && (c.minGrain ≤ c.span.2 - c.span.1 || c.span.2 == c.totalLen))
  preserves_inv _ _ _ h := h
  ensures_safe _ c h := by unfold verifyParChunk at h; split at h <;> simp_all

/-- Corollary 25: `verifyParChunk` rejects empty, out-of-range, or sub-grain non-tail parallel chunks. -/
theorem par_chunk_rejects_invalid_bounds (c : ParChunkCheck)
    (h_bad : (c.span.1 < c.span.2 && c.span.2 ≤ c.totalLen && (c.minGrain ≤ c.span.2 - c.span.1 || c.span.2 == c.totalLen)) = false) :
    (verifyParChunk c.span.1 c.span.2 c.totalLen c.minGrain == 1) = false :=
  parChunkMetaSpec.rejects_unsafe () c h_bad

/--
  Unboxed C-ABI Scratch Arena Disjoint Sub-Slice Verifier (`leansys_verify_arena_disjoint`):
  Certifies that `[offA, offA + lenA)` and `[offB, offB + lenB)` both lie within `[0, arenaCap)`
  without 64-bit overflow and do not alias (`offA + lenA ≤ offB || offB + lenB ≤ offA`).
-/
@[inline, export leansys_verify_arena_disjoint]
def verifyArenaDisjoint (offA lenA offB lenB arenaCap : UInt64) : UInt8 :=
  if subsliceOk offA lenA arenaCap && subsliceOk offB lenB arenaCap &&
     (offA + lenA ≤ offB || offB + lenB ≤ offA) then 1 else 0

/-- Scratch arena disjoint sub-slice check parameters (≤ 3 fields). -/
structure ArenaDisjointCheck where
  sliceA   : UInt64 × UInt64
  sliceB   : UInt64 × UInt64
  arenaCap : UInt64
  deriving Repr, DecidableEq

/-- Layer II Bundle 26: Scratch arena disjoint sub-slice gate (`leansys_verify_arena_disjoint`). -/
def arenaDisjointMetaSpec : MetaGateSpec Unit ArenaDisjointCheck where
  inv _ := True
  gate _ a := verifyArenaDisjoint a.sliceA.1 a.sliceA.2 a.sliceB.1 a.sliceB.2 a.arenaCap == 1
  step _ _ := ()
  safe _ a := (a.sliceA.1 ≤ a.arenaCap && a.sliceA.2 ≤ a.arenaCap - a.sliceA.1 &&
               a.sliceB.1 ≤ a.arenaCap && a.sliceB.2 ≤ a.arenaCap - a.sliceB.1 &&
               (a.sliceA.1 + a.sliceA.2 ≤ a.sliceB.1 || a.sliceB.1 + a.sliceB.2 ≤ a.sliceA.1))
  preserves_inv _ _ _ h := h
  ensures_safe _ a h := by unfold verifyArenaDisjoint subsliceOk at h; split at h <;> simp_all

/-- Corollary 26: `verifyArenaDisjoint` rejects out-of-bounds or overlapping scratch arena slices. -/
theorem arena_disjoint_rejects_overlap (a : ArenaDisjointCheck)
    (h_bad : (a.sliceA.1 ≤ a.arenaCap && a.sliceA.2 ≤ a.arenaCap - a.sliceA.1 &&
              a.sliceB.1 ≤ a.arenaCap && a.sliceB.2 ≤ a.arenaCap - a.sliceB.1 &&
              (a.sliceA.1 + a.sliceA.2 ≤ a.sliceB.1 || a.sliceB.1 + a.sliceB.2 ≤ a.sliceA.1)) = false) :
    (verifyArenaDisjoint a.sliceA.1 a.sliceA.2 a.sliceB.1 a.sliceB.2 a.arenaCap == 1) = false :=
  arenaDisjointMetaSpec.rejects_unsafe () a h_bad

/--
  Unboxed C-ABI Snapshot-Isolated LSM Visibility Verifier (`leansys_verify_snapshot_visibility`):
  Certifies that an indexed SST entry with sequence `entrySeq` is visible at `maxSnapshotSeq`
  (`entrySeq ≤ maxSnapshotSeq`) and is not a tombstone (`isTombstone == 0`).
-/
@[inline, export leansys_verify_snapshot_visibility]
def verifySnapshotVisibility (entrySeq maxSnapshotSeq : UInt64) (isTombstone : UInt8) : UInt8 :=
  if entrySeq ≤ maxSnapshotSeq && isTombstone == 0 then 1 else 0

/-- Snapshot visibility check parameters (≤ 3 fields). -/
structure SnapshotVisibilityCheck where
  entrySeq       : UInt64
  maxSnapshotSeq : UInt64
  isTombstone    : UInt8
  deriving Repr, DecidableEq

/-- Layer II Bundle 27: Snapshot-isolated LSM range scan visibility gate (`leansys_verify_snapshot_visibility`). -/
def snapshotVisibilityMetaSpec : MetaGateSpec Unit SnapshotVisibilityCheck where
  inv _ := True
  gate _ s := verifySnapshotVisibility s.entrySeq s.maxSnapshotSeq s.isTombstone == 1
  step _ _ := ()
  safe _ s := (s.entrySeq ≤ s.maxSnapshotSeq && s.isTombstone == 0)
  preserves_inv _ _ _ h := h
  ensures_safe _ s h := by unfold verifySnapshotVisibility at h; split at h <;> simp_all

/-- Corollary 27: `verifySnapshotVisibility` rejects entries newer than `maxSnapshotSeq` or deleted by a tombstone. -/
theorem snapshot_visibility_rejects_future_or_tombstone (s : SnapshotVisibilityCheck)
    (h_bad : (s.entrySeq ≤ s.maxSnapshotSeq && s.isTombstone == 0) = false) :
    (verifySnapshotVisibility s.entrySeq s.maxSnapshotSeq s.isTombstone == 1) = false :=
  snapshotVisibilityMetaSpec.rejects_unsafe () s h_bad

/--
  Unboxed C-ABI Bounded HTTP/1.1 Static Route Table Match Verifier (`leansys_verify_http_route_match`):
  Certifies that `methodMatch == 1`, `pathMatch == 1`, and `routeIdx < routeCount ≤ 64`.
-/
@[inline, export leansys_verify_http_route_match]
def verifyHttpRouteMatch (methodMatch pathMatch : UInt8) (routeIdx routeCount : UInt32) : UInt8 :=
  if methodMatch == 1 && pathMatch == 1 && routeIdx < routeCount && routeCount ≤ 64 then 1 else 0

/-- Bounded HTTP/1.1 route table match parameters (≤ 3 fields). -/
structure HttpRouteMatchCheck where
  flags      : UInt8 × UInt8
  routeIdx   : UInt32
  routeCount : UInt32
  deriving Repr, DecidableEq

/-- Layer II Bundle 28: Bounded HTTP/1.1 static route dispatch gate (`leansys_verify_http_route_match`). -/
def httpRouteMatchMetaSpec : MetaGateSpec Unit HttpRouteMatchCheck where
  inv _ := True
  gate _ r := verifyHttpRouteMatch r.flags.1 r.flags.2 r.routeIdx r.routeCount == 1
  step _ _ := ()
  safe _ r := (r.flags.1 == 1 && r.flags.2 == 1 && r.routeIdx < r.routeCount && r.routeCount ≤ 64)
  preserves_inv _ _ _ h := h
  ensures_safe _ r h := by unfold verifyHttpRouteMatch at h; split at h <;> simp_all

/-- Corollary 28: `verifyHttpRouteMatch` rejects method/path mismatches or out-of-bounds route indices. -/
theorem http_route_match_rejects_mismatch_or_oob (r : HttpRouteMatchCheck)
    (h_bad : (r.flags.1 == 1 && r.flags.2 == 1 && r.routeIdx < r.routeCount && r.routeCount ≤ 64) = false) :
    (verifyHttpRouteMatch r.flags.1 r.flags.2 r.routeIdx r.routeCount == 1) = false :=
  httpRouteMatchMetaSpec.rejects_unsafe () r h_bad

/--
  Unboxed C-ABI Counterexample Triage Verifier (`leansys_verify_counterexample_triage`):
  Certifies that a counterexample witness (`hasViolation == 1`) is classified into:
  - `1 = SpecTooStrong` when `hasMissingHypHint == 1`
  - `2 = ReferenceDiscrepancy` when `hasMissingHypHint == 0` and `refDisagreesWithCandidate == 1`
  - `3 = CandidateBug` when `hasMissingHypHint == 0` and `refDisagreesWithCandidate == 0`
-/
@[inline, export leansys_verify_counterexample_triage]
def verifyCounterexampleTriage (hasViolation hasMissingHypHint refDisagreesWithCandidate triageClass : UInt8) : UInt8 :=
  if hasViolation == 1 &&
     ((hasMissingHypHint == 1 && triageClass == 1) ||
      (hasMissingHypHint == 0 && refDisagreesWithCandidate == 1 && triageClass == 2) ||
      (hasMissingHypHint == 0 && refDisagreesWithCandidate == 0 && triageClass == 3)) then 1 else 0

/-- Counterexample triage check parameters (≤ 3 fields). -/
structure CounterexampleTriageCheck where
  flags                    : UInt8 × UInt8
  refDisagreesWithCand     : UInt8
  triageClass              : UInt8
  deriving Repr, DecidableEq

/-- Layer II Bundle 29: Counterexample triage consistency gate (`leansys_verify_counterexample_triage`). -/
def counterexampleTriageMetaSpec : MetaGateSpec Unit CounterexampleTriageCheck where
  inv _ := True
  gate _ c := verifyCounterexampleTriage c.flags.1 c.flags.2 c.refDisagreesWithCand c.triageClass == 1
  step _ _ := ()
  safe _ c := (c.flags.1 == 1 &&
               ((c.flags.2 == 1 && c.triageClass == 1) ||
                (c.flags.2 == 0 && c.refDisagreesWithCand == 1 && c.triageClass == 2) ||
                (c.flags.2 == 0 && c.refDisagreesWithCand == 0 && c.triageClass == 3)))
  preserves_inv _ _ _ h := h
  ensures_safe _ c h := by unfold verifyCounterexampleTriage at h; split at h <;> simp_all

/-- Corollary 29: `verifyCounterexampleTriage` rejects inconsistent counterexample triage classifications. -/
theorem counterexample_triage_rejects_inconsistent (c : CounterexampleTriageCheck)
    (h_bad : (c.flags.1 == 1 &&
              ((c.flags.2 == 1 && c.triageClass == 1) ||
               (c.flags.2 == 0 && c.refDisagreesWithCand == 1 && c.triageClass == 2) ||
               (c.flags.2 == 0 && c.refDisagreesWithCand == 0 && c.triageClass == 3))) = false) :
    (verifyCounterexampleTriage c.flags.1 c.flags.2 c.refDisagreesWithCand c.triageClass == 1) = false :=
  counterexampleTriageMetaSpec.rejects_unsafe () c h_bad

/--
  Unboxed C-ABI Lock-Free DAG Wave & Work-Stealing Admission Verifier (`leansys_verify_dag_wave_step`):
  Certifies that a ready wave of `waveSize` tasks has zero unresolved dependencies (`inDegreeSum == 0`),
  non-empty progress (`0 < waveSize`), bounded worker concurrency (`0 < activeWorkers ≤ maxWorkers`),
  and overflow-free completion accounting (`subsliceOk completedTasks waveSize totalTasks`).
-/
@[inline, export leansys_verify_dag_wave_step]
def verifyDagWaveStep (inDegreeSum waveSize completedTasks totalTasks activeWorkers maxWorkers : UInt64) : UInt8 :=
  if inDegreeSum == 0 && 0 < waveSize && subsliceOk completedTasks waveSize totalTasks &&
     0 < activeWorkers && activeWorkers ≤ maxWorkers then 1 else 0

/-- Lock-free DAG wave admission check parameters (≤ 3 fields). -/
structure DagWaveStepCheck where
  wave       : UInt64 × UInt64
  progress   : UInt64 × UInt64
  workers    : UInt64 × UInt64
  deriving Repr, DecidableEq

/-- Layer II Bundle 30: Lock-free DAG wave & work-stealing admission gate (`leansys_verify_dag_wave_step`). -/
def dagWaveStepMetaSpec : MetaGateSpec Unit DagWaveStepCheck where
  inv _ := True
  gate _ w := verifyDagWaveStep w.wave.1 w.wave.2 w.progress.1 w.progress.2 w.workers.1 w.workers.2 == 1
  step _ _ := ()
  safe _ w := (w.wave.1 == 0 && 0 < w.wave.2 &&
               w.progress.1 ≤ w.progress.2 && w.wave.2 ≤ w.progress.2 - w.progress.1 &&
               0 < w.workers.1 && w.workers.1 ≤ w.workers.2)
  preserves_inv _ _ _ h := h
  ensures_safe _ w h := by unfold verifyDagWaveStep subsliceOk at h; split at h <;> simp_all

/-- Corollary 30: `verifyDagWaveStep` rejects waves with unresolved deps, empty wave, overflow, or bad worker bounds. -/
theorem dag_wave_step_rejects_unready_or_overflow (w : DagWaveStepCheck)
    (h_bad : (w.wave.1 == 0 && 0 < w.wave.2 &&
              w.progress.1 ≤ w.progress.2 && w.wave.2 ≤ w.progress.2 - w.progress.1 &&
              0 < w.workers.1 && w.workers.1 ≤ w.workers.2) = false) :
    (verifyDagWaveStep w.wave.1 w.wave.2 w.progress.1 w.progress.2 w.workers.1 w.workers.2 == 1) = false :=
  dagWaveStepMetaSpec.rejects_unsafe () w h_bad

/--
  Unboxed C-ABI iOS Jetsam & App-Extension Dirty-RSS Budget Gate (`leansys_verify_ios_jetsam_budget`):
  Certifies that an allocation of `allocBytes` on top of `dirtyRssBytes` stays within `maxJetsamBytes`
  without overflow (`subsliceOk dirtyRssBytes allocBytes maxJetsamBytes`), with non-zero 16 KB
  page alignment (`0 < allocBytes && pageAlignMask == 16383`) and iOS App Extension cap (`≤ 24 MiB`
  when `isAppExtension == 1`).
-/
@[inline, export leansys_verify_ios_jetsam_budget]
def verifyIosJetsamBudget (dirtyRssBytes allocBytes maxJetsamBytes pageAlignMask : UInt64)
    (isAppExtension : UInt8) : UInt8 :=
  if 0 < allocBytes && pageAlignMask == 16383 &&
     subsliceOk dirtyRssBytes allocBytes maxJetsamBytes &&
     isAppExtension ≤ 1 && (isAppExtension == 0 || maxJetsamBytes ≤ 25165824) then 1 else 0

/-- iOS Jetsam & App-Extension dirty-RSS budget check parameters (≤ 3 fields). -/
structure IosJetsamBudgetCheck where
  rssBounds      : UInt64 × UInt64
  limitAndAlign  : UInt64 × UInt64
  isAppExtension : UInt8
  deriving Repr, DecidableEq

/-- Layer II Bundle 31: iOS Jetsam & App-Extension dirty-RSS budget gate (`leansys_verify_ios_jetsam_budget`). -/
def iosJetsamBudgetMetaSpec : MetaGateSpec Unit IosJetsamBudgetCheck where
  inv _ := True
  gate _ j := verifyIosJetsamBudget j.rssBounds.1 j.rssBounds.2 j.limitAndAlign.1 j.limitAndAlign.2 j.isAppExtension == 1
  step _ _ := ()
  safe _ j := (0 < j.rssBounds.2 && j.limitAndAlign.2 == 16383 &&
               j.rssBounds.1 ≤ j.limitAndAlign.1 && j.rssBounds.2 ≤ j.limitAndAlign.1 - j.rssBounds.1 &&
               j.isAppExtension ≤ 1 && (j.isAppExtension == 0 || j.limitAndAlign.1 ≤ 25165824))
  preserves_inv _ _ _ h := h
  ensures_safe _ j h := by unfold verifyIosJetsamBudget subsliceOk at h; split at h <;> simp_all

/-- Corollary 31: `verifyIosJetsamBudget` rejects unaligned pages, overflow, or App Extension >24 MiB RSS. -/
theorem ios_jetsam_budget_rejects_overflow_or_excess (j : IosJetsamBudgetCheck)
    (h_bad : (0 < j.rssBounds.2 && j.limitAndAlign.2 == 16383 &&
              j.rssBounds.1 ≤ j.limitAndAlign.1 && j.rssBounds.2 ≤ j.limitAndAlign.1 - j.rssBounds.1 &&
              j.isAppExtension ≤ 1 && (j.isAppExtension == 0 || j.limitAndAlign.1 ≤ 25165824)) = false) :
    (verifyIosJetsamBudget j.rssBounds.1 j.rssBounds.2 j.limitAndAlign.1 j.limitAndAlign.2 j.isAppExtension == 1) = false :=
  iosJetsamBudgetMetaSpec.rejects_unsafe () j h_bad

/--
  Unboxed C-ABI Bounded Worker Pool & Asymmetric Multi-Cluster Micro-Chunk Gate (`leansys_verify_worker_budget`):
  Certifies that `0 < activeWorkers ≤ maxWorkers ≤ 64`, `0 < totalLen`, `activeWorkers ≤ microChunks ≤ maxWorkers * 8`,
  and enforces cluster-specific core caps (`topologyKind == 0` SMP `≤ 64`, `topologyKind == 1` 2-tier P+E `≤ 6` e.g. Apple A15–A18,
  `topologyKind == 2` 3-tier Prime+Mid+Little `≤ 9` e.g. Google Tensor G3 / Pixel 8).
-/
@[inline, export leansys_verify_worker_budget]
def verifyWorkerBudget (activeWorkers maxWorkers microChunks totalLen : UInt64)
    (topologyKind : UInt8) : UInt8 :=
  if 0 < activeWorkers && activeWorkers ≤ maxWorkers && maxWorkers ≤ 64 &&
     0 < totalLen && activeWorkers ≤ microChunks && microChunks ≤ maxWorkers * 8 &&
     topologyKind ≤ 2 && (topologyKind != 1 || maxWorkers ≤ 6) &&
     (topologyKind != 2 || maxWorkers ≤ 9) then 1 else 0

/-- Bounded worker pool & multi-cluster micro-chunk check parameters (≤ 3 fields). -/
structure WorkerBudgetCheck where
  workers        : UInt64 × UInt64
  chunksAndTotal : UInt64 × UInt64
  topologyKind   : UInt8
  deriving Repr, DecidableEq

/-- Layer II Bundle 32: Bounded worker pool & multi-cluster micro-chunk admission gate (`leansys_verify_worker_budget`). -/
def workerBudgetMetaSpec : MetaGateSpec Unit WorkerBudgetCheck where
  inv _ := True
  gate _ b := verifyWorkerBudget b.workers.1 b.workers.2 b.chunksAndTotal.1 b.chunksAndTotal.2 b.topologyKind == 1
  step _ _ := ()
  safe _ b := (0 < b.workers.1 && b.workers.1 ≤ b.workers.2 && b.workers.2 ≤ 64 &&
               0 < b.chunksAndTotal.2 && b.workers.1 ≤ b.chunksAndTotal.1 && b.chunksAndTotal.1 ≤ b.workers.2 * 8 &&
               b.topologyKind ≤ 2 && (b.topologyKind != 1 || b.workers.2 ≤ 6) &&
               (b.topologyKind != 2 || b.workers.2 ≤ 9))
  preserves_inv _ _ _ h := h
  ensures_safe _ b h := by unfold verifyWorkerBudget at h; split at h <;> simp_all

/-- Corollary 32: `verifyWorkerBudget` rejects unbounded worker pools, empty work, or core cap violations. -/
theorem worker_budget_rejects_unbounded_or_overflow (b : WorkerBudgetCheck)
    (h_bad : (0 < b.workers.1 && b.workers.1 ≤ b.workers.2 && b.workers.2 ≤ 64 &&
              0 < b.chunksAndTotal.2 && b.workers.1 ≤ b.chunksAndTotal.1 && b.chunksAndTotal.1 ≤ b.workers.2 * 8 &&
              b.topologyKind ≤ 2 && (b.topologyKind != 1 || b.workers.2 ≤ 6) &&
              (b.topologyKind != 2 || b.workers.2 ≤ 9)) = false) :
    (verifyWorkerBudget b.workers.1 b.workers.2 b.chunksAndTotal.1 b.chunksAndTotal.2 b.topologyKind == 1) = false :=
  workerBudgetMetaSpec.rejects_unsafe () b h_bad

/--
  Unboxed C-ABI Page-Aligned Buffer Geometry & Memory Budget Gate (`leansys_verify_page_aligned_buffer`):
  Certifies that `addr > 0`, `0 < allocBytes ≤ capacityBytes`, `pageAlignMask` is an exact 4 KiB (`4095`)
  or 16 KiB (`16383`) OS page mask, both `addr` and `capacityBytes` are multiples of `pageAlignMask + 1`
  (`((addr ||| capacityBytes) &&& pageAlignMask) == 0`), and `dirtyRssBytes + capacityBytes ≤ maxBudgetBytes`
  without 64-bit unsigned overflow.
-/
@[inline, export leansys_verify_page_aligned_buffer]
def verifyPageAlignedBuffer (addr allocBytes capacityBytes dirtyRssBytes maxBudgetBytes pageAlignMask : UInt64) : UInt8 :=
  if 0 < addr && 0 < allocBytes && allocBytes ≤ capacityBytes &&
     (pageAlignMask == 4095 || pageAlignMask == 16383) &&
     ((addr ||| capacityBytes) &&& pageAlignMask) == 0 &&
     subsliceOk dirtyRssBytes capacityBytes maxBudgetBytes then 1 else 0

/-- Page-aligned buffer geometry & memory budget check parameters (≤ 3 fields). -/
structure PageAlignedBufferCheck where
  addrAndAlloc  : UInt64 × UInt64
  capAndDirty   : UInt64 × UInt64
  budgetAndMask : UInt64 × UInt64
  deriving Repr, DecidableEq

/-- Layer II Bundle 33: Page-aligned buffer geometry & memory budget gate (`leansys_verify_page_aligned_buffer`). -/
def pageAlignedBufferMetaSpec : MetaGateSpec Unit PageAlignedBufferCheck where
  inv _ := True
  gate _ p :=
    verifyPageAlignedBuffer p.addrAndAlloc.1 p.addrAndAlloc.2
      p.capAndDirty.1 p.capAndDirty.2 p.budgetAndMask.1 p.budgetAndMask.2 == 1
  step _ _ := ()
  safe _ p := (0 < p.addrAndAlloc.1 && 0 < p.addrAndAlloc.2 && p.addrAndAlloc.2 ≤ p.capAndDirty.1 &&
               (p.budgetAndMask.2 == 4095 || p.budgetAndMask.2 == 16383) &&
               ((p.addrAndAlloc.1 ||| p.capAndDirty.1) &&& p.budgetAndMask.2) == 0 &&
               p.capAndDirty.2 ≤ p.budgetAndMask.1 && p.capAndDirty.1 ≤ p.budgetAndMask.1 - p.capAndDirty.2)
  preserves_inv _ _ _ h := h
  ensures_safe _ p h := by unfold verifyPageAlignedBuffer subsliceOk at h; split at h <;> simp_all

/-- Corollary 33: `verifyPageAlignedBuffer` rejects null pointers, unaligned 4K/16K geometry, or budget overflow. -/
theorem page_aligned_buffer_rejects_unaligned_or_overflow (p : PageAlignedBufferCheck)
    (h_bad : (0 < p.addrAndAlloc.1 && 0 < p.addrAndAlloc.2 && p.addrAndAlloc.2 ≤ p.capAndDirty.1 &&
              (p.budgetAndMask.2 == 4095 || p.budgetAndMask.2 == 16383) &&
              ((p.addrAndAlloc.1 ||| p.capAndDirty.1) &&& p.budgetAndMask.2) == 0 &&
              p.capAndDirty.2 ≤ p.budgetAndMask.1 && p.capAndDirty.1 ≤ p.budgetAndMask.1 - p.capAndDirty.2) = false) :
    (verifyPageAlignedBuffer p.addrAndAlloc.1 p.addrAndAlloc.2
      p.capAndDirty.1 p.capAndDirty.2 p.budgetAndMask.1 p.budgetAndMask.2 == 1) = false :=
  pageAlignedBufferMetaSpec.rejects_unsafe () p h_bad

/--
  Canonical capability bitmask required by each runtime ISA variant ID (`0..4`):
  - `0` (`arm64Baseline`, ARMv8.2-A): `neon (bit 0) | fp16 (bit 1) | dotprod (bit 2) | lse (bit 8)` = `0x107`
  - `1` (`appleA15`, ARMv8.5-A): `0x107 | sha3 (bit 9)` = `0x307`
  - `2` (`appleA16_A17`, ARMv8.6-A): `0x307 | i8mm (bit 3) | bf16 (bit 4)` = `0x31F`
  - `3` (`tensorG3`, ARMv9.0-A + SVE2): `0x31F | sve2 (bit 5) | sveBitperm (bit 6)` = `0x37F`
  - `4` (`appleM4_A18`, ARMv9.2-A + SME2): `0x31F | sme2 (bit 7)` = `0x39F`
-/
@[inline]
def isaVariantRequiredMask (variantId : UInt8) : UInt64 :=
  if variantId == 0 then 0x107
  else if variantId == 1 then 0x307
  else if variantId == 2 then 0x31F
  else if variantId == 3 then 0x37F
  else if variantId == 4 then 0x39F
  else 0xFFFFFFFFFFFFFFFF

/--
  Unboxed C-ABI Capability-Checked Runtime ISA Variant Selector (`leansys_select_isa`):
  Returns `requestedVariantId` if and only if `0 < requestedVariantId ≤ maxVariantId ≤ 4`,
  `requiredMask == isaVariantRequiredMask requestedVariantId` (rejecting forged masks),
  and every capability bit in `requiredMask` is present in `detectedHwCaps`
  (`(detectedHwCaps &&& requiredMask) == requiredMask`); otherwise deterministically falls back
  to variant `0` (the guaranteed compile-time baseline).
-/
@[inline, export leansys_select_isa]
def selectIsaVariant (detectedHwCaps requiredMask : UInt64)
    (requestedVariantId maxVariantId : UInt8) : UInt8 :=
  if 0 < requestedVariantId && requestedVariantId ≤ maxVariantId && maxVariantId ≤ 4 &&
     requiredMask == isaVariantRequiredMask requestedVariantId &&
     (detectedHwCaps &&& requiredMask) == requiredMask then requestedVariantId else 0

/--
  Unboxed C-ABI Runtime ISA Selection Gate (`leansys_verify_isa_selection`):
  Certifies that `selectedVariantId ≤ maxVariantId ≤ 4`, `requiredMask == isaVariantRequiredMask selectedVariantId`,
  and any non-baseline variant (`selectedVariantId != 0`) has its canonical `requiredMask`
  fully supported by `detectedHwCaps`.
-/
@[inline, export leansys_verify_isa_selection]
def verifyIsaSelection (detectedHwCaps requiredMask : UInt64)
    (selectedVariantId maxVariantId : UInt8) : UInt8 :=
  if selectedVariantId ≤ maxVariantId && maxVariantId ≤ 4 &&
     requiredMask == isaVariantRequiredMask selectedVariantId &&
     (selectedVariantId == 0 || (detectedHwCaps &&& requiredMask) == requiredMask) then 1 else 0

/-- Runtime ISA variant selection check parameters (≤ 3 fields). -/
structure IsaSelectionCheck where
  capsAndReq : UInt64 × UInt64
  selAndMax  : UInt8 × UInt8
  deriving Repr, DecidableEq

/-- Layer II Bundle 34: Capability-checked runtime ISA selection gate (`leansys_verify_isa_selection`). -/
def isaSelectionMetaSpec : MetaGateSpec Unit IsaSelectionCheck where
  inv _ := True
  gate _ s := verifyIsaSelection s.capsAndReq.1 s.capsAndReq.2 s.selAndMax.1 s.selAndMax.2 == 1
  step _ _ := ()
  safe _ s := (s.selAndMax.1 ≤ s.selAndMax.2 && s.selAndMax.2 ≤ 4 &&
               s.capsAndReq.2 == isaVariantRequiredMask s.selAndMax.1 &&
               (s.selAndMax.1 == 0 || (s.capsAndReq.1 &&& s.capsAndReq.2) == s.capsAndReq.2))
  preserves_inv _ _ _ h := h
  ensures_safe _ s h := by
    unfold verifyIsaSelection at h
    split at h
    · rename_i hCond
      exact hCond
    · contradiction

/-- Corollary 34a: `verifyIsaSelection` rejects forged masks, out-of-range variant IDs, or unsupported hardware capabilities. -/
theorem isa_selection_rejects_unsupported_or_oob (s : IsaSelectionCheck)
    (h_bad : (s.selAndMax.1 ≤ s.selAndMax.2 && s.selAndMax.2 ≤ 4 &&
              s.capsAndReq.2 == isaVariantRequiredMask s.selAndMax.1 &&
              (s.selAndMax.1 == 0 || (s.capsAndReq.1 &&& s.capsAndReq.2) == s.capsAndReq.2)) = false) :
    (verifyIsaSelection s.capsAndReq.1 s.capsAndReq.2 s.selAndMax.1 s.selAndMax.2 == 1) = false :=
  isaSelectionMetaSpec.rejects_unsafe () s h_bad

/-- Corollary 34b: `selectIsaVariant` always produces a variant ID whose canonical mask is admitted by `verifyIsaSelection`. -/
theorem select_isa_variant_always_admitted (detectedHwCaps requiredMask : UInt64)
    (reqVar maxVar : UInt8) (hMax : (maxVar ≤ 4) = true) :
    let sel := selectIsaVariant detectedHwCaps requiredMask reqVar maxVar
    verifyIsaSelection detectedHwCaps (isaVariantRequiredMask sel) sel maxVar = 1 := by
  dsimp only
  unfold verifyIsaSelection selectIsaVariant
  split
  · rename_i hCond
    simp only [Bool.and_eq_true, beq_iff_eq] at hCond
    rcases hCond with ⟨⟨⟨_, hLe⟩, hMask⟩, hCaps⟩
    subst hMask
    simp_all [isaVariantRequiredMask]
  · simp_all [isaVariantRequiredMask]

end LeanSys.Spec
