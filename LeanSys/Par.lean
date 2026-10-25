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

/-- Bounded worker pool & micro-chunk configuration (calibrated for heterogeneous P/E cores such as Apple A15 2P+4E). -/
structure WorkerBudget where
  maxWorkers       : Nat  := 6
  microChunkFactor : Nat  := 4
  minGrain         : Nat  := 64
  isMobileHetero   : Bool := false
  deriving Repr, DecidableEq, Inhabited

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
  let maxW := Nat.min 64 (Nat.max 1 (if budget.isMobileHetero then Nat.min 6 budget.maxWorkers else budget.maxWorkers))
  let factor := Nat.min 8 (Nat.max 1 budget.microChunkFactor)
  let targetChunks := Nat.max 1 (Nat.min totalLen (maxW * factor))
  let chunks := partitionRangeBalanced totalLen budget.minGrain targetChunks
  let nChunks := chunks.size
  if nChunks == 0 then
    return #[]
  let activeW := Nat.max 1 (Nat.min maxW nChunks)
  let heteroFlag : UInt8 := if budget.isMobileHetero then 1 else 0
  if verifyWorkerBudget activeW.toUInt64 maxW.toUInt64 (Nat.max activeW nChunks).toUInt64 totalLen.toUInt64 heteroFlag != 1 then
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
