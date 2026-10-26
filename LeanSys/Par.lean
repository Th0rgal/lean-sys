/-
  LeanSys/Par.lean — Zero-Lock Multi-Threaded Chunk, Slice & DAG Wave Scheduler (`0 import Lean`, `0 sorryAx`).
  All parallel partitions and DAG waves are gated by `verifyParChunk`, `verifyArenaDisjoint`, and `verifyDagWaveStep`.
-/
import LeanSys.Spec
import LeanSys.Posix

namespace LeanSys.Par

open LeanSys.Spec
open LeanSys.Posix

/-- Certified half-open 1D index chunk `[startIdx, endIdx)`. -/
structure ChunkSpan where
  startIdx : Nat
  endIdx   : Nat
  deriving Repr, DecidableEq, Inhabited

/-- Base AArch64 architecture generation in the capability lattice. -/
inductive ArmBase where
  | v8_0 | v8_2 | v8_5 | v8_6 | v9_0 | v9_2
  deriving Repr, DecidableEq, Inhabited

def ArmBase.rank : ArmBase → Nat
  | .v8_0 => 0 | .v8_2 => 1 | .v8_5 => 2 | .v8_6 => 3 | .v9_0 => 4 | .v9_2 => 5

def ArmBase.ofRank : Nat → ArmBase
  | 0 => .v8_0 | 1 => .v8_2 | 2 => .v8_5 | 3 => .v8_6 | 4 => .v9_0 | _ => .v9_2

/-- Orthogonal capability lattice for vector, matrix, atomic, and crypto extensions (`IsaLevel`).
    Device presets (`appleA15`, `appleA16_A17`, `tensorG3`) are named values of this structure;
    codegen and runtime dispatch depend only on capability flags, never on device names. -/
structure IsaLevel where
  base       : ArmBase := .v8_0
  neon       : Bool    := true
  fp16       : Bool    := false
  dotprod    : Bool    := false
  i8mm       : Bool    := false
  bf16       : Bool    := false
  sve2       : Bool    := false
  sveBitperm : Bool    := false
  sme2       : Bool    := false
  lse        : Bool    := false
  sha3       : Bool    := false
  deriving Repr, DecidableEq, Inhabited

namespace IsaLevel

/-- Pointwise partial order on `IsaLevel`: `a.le b == true` iff every capability required by `a` is provided by `b`. -/
def le (a b : IsaLevel) : Bool :=
  decide (a.base.rank ≤ b.base.rank) &&
  (!a.neon || b.neon) && (!a.fp16 || b.fp16) && (!a.dotprod || b.dotprod) &&
  (!a.i8mm || b.i8mm) && (!a.bf16 || b.bf16) && (!a.sve2 || b.sve2) &&
  (!a.sveBitperm || b.sveBitperm) && (!a.sme2 || b.sme2) &&
  (!a.lse || b.lse) && (!a.sha3 || b.sha3)

/-- Greatest lower bound (intersection of capabilities) in the `IsaLevel` lattice. -/
def meet (a b : IsaLevel) : IsaLevel where
  base       := ArmBase.ofRank (Nat.min a.base.rank b.base.rank)
  neon       := a.neon && b.neon
  fp16       := a.fp16 && b.fp16
  dotprod    := a.dotprod && b.dotprod
  i8mm       := a.i8mm && b.i8mm
  bf16       := a.bf16 && b.bf16
  sve2       := a.sve2 && b.sve2
  sveBitperm := a.sveBitperm && b.sveBitperm
  sme2       := a.sme2 && b.sme2
  lse        := a.lse && b.lse
  sha3       := a.sha3 && b.sha3

/-- Least upper bound (union of capabilities) in the `IsaLevel` lattice. -/
def join (a b : IsaLevel) : IsaLevel where
  base       := ArmBase.ofRank (Nat.max a.base.rank b.base.rank)
  neon       := a.neon || b.neon
  fp16       := a.fp16 || b.fp16
  dotprod    := a.dotprod || b.dotprod
  i8mm       := a.i8mm || b.i8mm
  bf16       := a.bf16 || b.bf16
  sve2       := a.sve2 || b.sve2
  sveBitperm := a.sveBitperm || b.sveBitperm
  sme2       := a.sme2 || b.sme2
  lse        := a.lse || b.lse
  sha3       := a.sha3 || b.sha3

/-- Architectural well-formedness invariant (`sveBitperm → sve2`, `sve2 → base ≥ v9_0`, `sme2 → base ≥ v9_2`). -/
def wellFormed (a : IsaLevel) : Bool :=
  (!a.sveBitperm || a.sve2) &&
  (!a.sve2 || decide (4 ≤ a.base.rank)) &&
  (!a.sme2 || decide (5 ≤ a.base.rank))

/-- Canonical 64-bit hardware capability bitmask for `selectIsaVariant` / `verifyIsaSelection`. -/
def hwcapMask (a : IsaLevel) : UInt64 :=
  (if a.neon       then (1 : UInt64) <<< 0 else 0) |||
  (if a.fp16       then (1 : UInt64) <<< 1 else 0) |||
  (if a.dotprod    then (1 : UInt64) <<< 2 else 0) |||
  (if a.i8mm       then (1 : UInt64) <<< 3 else 0) |||
  (if a.bf16       then (1 : UInt64) <<< 4 else 0) |||
  (if a.sve2       then (1 : UInt64) <<< 5 else 0) |||
  (if a.sveBitperm then (1 : UInt64) <<< 6 else 0) |||
  (if a.sme2       then (1 : UInt64) <<< 7 else 0) |||
  (if a.lse        then (1 : UInt64) <<< 8 else 0) |||
  (if a.sha3       then (1 : UInt64) <<< 9 else 0)

theorem bool_imp_self (x : Bool) : (!x || x) = true := by cases x <;> rfl
theorem bool_and_imp_left (x y : Bool) : (!(x && y) || x) = true := by cases x <;> cases y <;> rfl
theorem bool_and_imp_right (x y : Bool) : (!(x && y) || y) = true := by cases x <;> cases y <;> rfl
theorem ArmBase.rank_le_refl (x : ArmBase) : decide (x.rank ≤ x.rank) = true := by cases x <;> rfl

theorem le_refl (a : IsaLevel) : a.le a = true := by
  unfold le
  rw [ArmBase.rank_le_refl]
  simp only [bool_imp_self, Bool.and_self]

theorem ArmBase.rank_ofRank_min_le_left (x y : ArmBase) :
    decide ((ArmBase.ofRank (Nat.min x.rank y.rank)).rank ≤ x.rank) = true := by
  cases x <;> cases y <;> rfl

theorem ArmBase.rank_ofRank_min_le_right (x y : ArmBase) :
    decide ((ArmBase.ofRank (Nat.min x.rank y.rank)).rank ≤ y.rank) = true := by
  cases x <;> cases y <;> rfl

theorem meet_le_left (a b : IsaLevel) : (a.meet b).le a = true := by
  unfold le meet
  rw [ArmBase.rank_ofRank_min_le_left]
  simp only [bool_and_imp_left, Bool.and_self]

theorem meet_le_right (a b : IsaLevel) : (a.meet b).le b = true := by
  unfold le meet
  rw [ArmBase.rank_ofRank_min_le_right]
  simp only [bool_and_imp_right, Bool.and_self]

/-- Portable ARMv8.2-A baseline (`+neon,+fp16,+dotprod,+lse`). -/
def arm64Baseline : IsaLevel :=
  { base := .v8_2, neon := true, fp16 := true, dotprod := true, lse := true }

/-- Apple A15 Bionic preset (iPhone 13 mini / 13 / 14, ARMv8.5-A). -/
def appleA15 : IsaLevel :=
  { base := .v8_5, neon := true, fp16 := true, dotprod := true, lse := true, sha3 := true }

/-- Apple A16 / A17 Pro preset (iPhone 14 Pro / 15 / 15 Pro, ARMv8.6-A + `i8mm` + `bf16`). -/
def appleA16_A17 : IsaLevel :=
  { base := .v8_6, neon := true, fp16 := true, dotprod := true, i8mm := true, bf16 := true, lse := true, sha3 := true }

/-- Google Tensor G3 preset (Pixel 8 / 8 Pro, ARMv9.0-A + `sve2` + `sve2-bitperm` + `i8mm` + `bf16`). -/
def tensorG3 : IsaLevel :=
  { base := .v9_0, neon := true, fp16 := true, dotprod := true, i8mm := true, bf16 := true,
    sve2 := true, sveBitperm := true, lse := true, sha3 := true }

/-- Apple M4 / A18 preset (ARMv9.2-A + `sme2`, represented in lattice; gated by toolchain support). -/
def appleM4_A18 : IsaLevel :=
  { base := .v9_2, neon := true, fp16 := true, dotprod := true, i8mm := true, bf16 := true,
    sme2 := true, lse := true, sha3 := true }

end IsaLevel

/-- A homogeneous cluster of CPU cores with relative per-core performance weight (`1000 = 1.0x` Little core). -/
structure CoreCluster where
  cores   : Nat
  relPerf : Nat := 1000
  deriving Repr, DecidableEq, Inhabited

/-- Multi-cluster CPU topology (`1` cluster = SMP, `2` = P+E Apple A15–A18, `3` = Prime+Mid+Little Tensor G3). -/
abbrev CoreTopology := List CoreCluster

namespace CoreTopology

def totalCores (t : CoreTopology) : Nat :=
  t.foldl (fun acc c => acc + c.cores) 0

def totalWeight (t : CoreTopology) : Nat :=
  t.foldl (fun acc c => acc + c.cores * c.relPerf) 0

/-- Classify topology into C-ABI `topologyKind` (`0 = SMP ≤ 64`, `1 = 2-tier 2P+4E ≤ 6`, `2 = 3-tier 1+4+4 ≤ 9`). -/
def topologyKind (t : CoreTopology) : UInt8 :=
  match t.length with
  | 0 | 1 => 0
  | 2 => if totalCores t ≤ 6 then 1 else 0
  | _ => if totalCores t ≤ 9 then 2 else 0

def uniformSmp (n : Nat) : CoreTopology :=
  [{ cores := n, relPerf := 1000 }]

/-- Apple A15–A18 6-core 2-tier topology (`2× Performance + 4× Efficiency`). -/
def appleA15 : CoreTopology :=
  [{ cores := 2, relPerf := 2600 }, { cores := 4, relPerf := 1000 }]

/-- Google Tensor G3 (Pixel 8) 9-core 3-tier topology (`1× Cortex-X3 + 4× Cortex-A715 + 4× Cortex-A510`). -/
def tensorG3 : CoreTopology :=
  [{ cores := 1, relPerf := 3100 }, { cores := 4, relPerf := 2000 }, { cores := 4, relPerf := 1000 }]

end CoreTopology

/-- Bounded worker pool & micro-chunk configuration parameterized by cluster topology. -/
structure WorkerBudget where
  maxWorkers       : Nat   := 6
  microChunkFactor : Nat   := 4
  minGrain         : Nat   := 64
  isMobileHetero   : Bool  := false
  topologyKind     : UInt8 := 0
  deriving Repr, DecidableEq, Inhabited

/-- Construct a `WorkerBudget` calibrated to a `CoreTopology` (`factor = 2` for SMP, `4` for 2-tier P+E, `6` for 3-tier Prime+Mid+Little). -/
def WorkerBudget.ofTopology (t : CoreTopology) (minGrain : Nat := 64) : WorkerBudget :=
  let kind := CoreTopology.topologyKind t
  let cores := Nat.max 1 (CoreTopology.totalCores t)
  let factor := if kind == 2 then 6 else if kind == 1 then 4 else 2
  { maxWorkers := cores, microChunkFactor := factor, minGrain := minGrain, isMobileHetero := kind > 0, topologyKind := kind }

/-- Closed-form remainder-balanced partition of `[0, totalLen)` into `k = min totalLen numChunks`
    disjoint chunks where chunk `i` has length `totalLen / k + (if i < totalLen % k then 1 else 0)`,
    certified by `verifyParChunk` and `verifyArenaDisjoint`. -/
def partitionRangeBalanced (totalLen minGrain numChunks : Nat) : Array ChunkSpan := Id.run do
  if totalLen == 0 then
    return #[]
  let maxByGrain := Nat.max 1 (totalLen / Nat.max 1 minGrain)
  let k := Nat.max 1 (Nat.min (Nat.min totalLen (Nat.max 1 numChunks)) maxByGrain)
  let q := totalLen / k
  let r := totalLen % k
  let mut chunks : Array ChunkSpan := Array.mkEmpty k
  let mut cur : Nat := 0
  for i in [0:k] do
    let step := q + (if i < r then 1 else 0)
    let next := cur + step
    if verifyParChunk cur.toUInt64 next.toUInt64 totalLen.toUInt64 minGrain.toUInt64 != 1 then
      return #[{ startIdx := 0, endIdx := totalLen }]
    if let some prev := chunks.back? then
      let lenA := (prev.endIdx - prev.startIdx).toUInt64
      if verifyArenaDisjoint prev.startIdx.toUInt64 lenA cur.toUInt64 step.toUInt64 totalLen.toUInt64 != 1 then
        return #[{ startIdx := 0, endIdx := totalLen }]
    chunks := chunks.push { startIdx := cur, endIdx := next }
    cur := next
  return chunks

/-- Partition `[0, totalLen)` into at most `maxWorkers` disjoint chunks of size `≥ minGrain`
    (except possibly the final tail chunk), certifying every chunk via `verifyParChunk`
    and every adjacent pair via `verifyArenaDisjoint`. -/
def partitionRange (totalLen minGrain maxWorkers : Nat) : Array ChunkSpan :=
  partitionRangeBalanced totalLen minGrain maxWorkers

/-- Execute `f` in parallel across certified disjoint `ChunkSpan` partitions of `[0, totalLen)`
    using `Task.spawn` (`prio := .dedicated`) and collect results in deterministic chunk order. -/
def parMapChunks [Inhabited α] (totalLen minGrain maxWorkers : Nat) (f : ChunkSpan → α) : Array α :=
  let chunks := partitionRange totalLen minGrain maxWorkers
  if chunks.size ≤ 1 then
    chunks.map f
  else
    let tasks : Array (Task α) := chunks.map fun c => Task.spawn (prio := .dedicated) fun _ => f c
    tasks.map Task.get

/-- Split a borrowed `ByteArray` into certified disjoint `ByteSlice` sub-views (`verifyArenaDisjoint == 1`),
    apply `mapSlice` in parallel across worker threads without copying payload bytes, and fold results
    in deterministic chunk order via `op`. -/
def parReduceSlices [Inhabited β] (buf : @& ByteArray) (minGrain maxWorkers : Nat)
    (init : β) (op : β → β → β) (mapSlice : ByteSlice → β) : β :=
  let totalLen := buf.size
  let partials := parMapChunks totalLen minGrain maxWorkers fun c =>
    let len := c.endIdx - c.startIdx
    if verifySliceBounds c.startIdx.toUInt64 len.toUInt64 totalLen.toUInt64 == 1 then
      mapSlice { ba := buf, off := c.startIdx, len := len }
    else
      init
  partials.foldl op init

/-- Execute a ready DAG wave of `items` (`inDegreeSum = 0`) across bounded parallel worker batches
    (`maxWorkers`), gated by `verifyDagWaveStep`, preserving exact deterministic index order. -/
def parMapWave [Inhabited α] (maxWorkers : Nat) (items : Array α) (taskFn : α → IO β) : IO (Array β) := do
  let total := items.size
  if total == 0 then
    return #[]
  let workers := Nat.max 1 (Nat.min maxWorkers total)
  let mut out : Array β := Array.mkEmpty total
  let mut completed : Nat := 0
  while completed < total do
    let waveSize := Nat.min workers (total - completed)
    let active := Nat.min workers waveSize
    if verifyDagWaveStep 0 waveSize.toUInt64 completed.toUInt64 total.toUInt64 active.toUInt64 workers.toUInt64 != 1 then
      throw (IO.userError "LeanSys.Par.parMapWave: verifyDagWaveStep rejected wave bounds")
    let mut tasks : Array (Task (Except IO.Error β)) := Array.mkEmpty waveSize
    for i in [0:waveSize] do
      let item := items[completed + i]!
      let t ← IO.asTask (prio := .dedicated) (taskFn item)
      tasks := tasks.push t
    for t in tasks do
      match t.get with
      | .ok v => out := out.push v
      | .error e => throw e
    completed := completed + waveSize
  return out

/-- Dynamic micro-chunk work stealing across a bounded worker pool (`budget.maxWorkers`),
    gated by `verifyWorkerBudget`. Decomposes `[0, totalLen)` into up to `maxWorkers * microChunkFactor`
    certified chunks pulled from a shared atomic `IO.Ref Nat` cursor so faster P-cores (e.g. Apple A15
    Avalanche) naturally process more chunks than E-cores (Blizzard) without barrier stragglers,
    and reassembles outputs in exact deterministic chunk index order. -/
def parMapMicroChunks [Inhabited α] (totalLen : Nat) (budget : WorkerBudget := {})
    (f : ChunkSpan → IO α) : IO (Array α) := do
  if totalLen == 0 then
    return #[]
  let kind : UInt8 := if budget.topologyKind > 0 && budget.topologyKind ≤ 2 then budget.topologyKind else if budget.isMobileHetero then 1 else 0
  let capW : Nat := if kind == 1 then 6 else if kind == 2 then 9 else 64
  let maxW := Nat.min capW (Nat.max 1 budget.maxWorkers)
  let factor := Nat.min 8 (Nat.max 1 budget.microChunkFactor)
  let targetChunks := Nat.max 1 (Nat.min totalLen (maxW * factor))
  let chunks := partitionRangeBalanced totalLen budget.minGrain targetChunks
  let nChunks := chunks.size
  if nChunks == 0 then
    return #[]
  let activeW := Nat.max 1 (Nat.min maxW nChunks)
  if verifyWorkerBudget activeW.toUInt64 maxW.toUInt64 (Nat.max activeW nChunks).toUInt64 totalLen.toUInt64 kind != 1 then
    throw (IO.userError "LeanSys.Par.parMapMicroChunks: verifyWorkerBudget rejected worker/chunk bounds")
  if activeW == 1 then
    chunks.mapM f
  else
    let cursorRef ← IO.mkRef (0 : Nat)
    let mut workers : Array (Task (Except IO.Error (Array (Nat × α)))) := Array.mkEmpty activeW
    for _ in [0:activeW] do
      let t ← IO.asTask (prio := .dedicated) do
        let mut localOut : Array (Nat × α) := #[]
        let mut keepGoing := true
        while keepGoing do
          let idx ← cursorRef.modifyGet fun c => (c, c + 1)
          if h : idx < chunks.size then
            let v ← f chunks[idx]
            localOut := localOut.push (idx, v)
          else
            keepGoing := false
        return localOut
      workers := workers.push t
    let mut ordered : Array α := Array.replicate nChunks default
    for w in workers do
      match w.get with
      | .error e => throw e
      | .ok pairs =>
        for (idx, v) in pairs do
          if idx < ordered.size then
            ordered := ordered.set! idx v
    return ordered

end LeanSys.Par
