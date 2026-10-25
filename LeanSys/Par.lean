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

/-- Partition `[0, totalLen)` into at most `maxWorkers` disjoint chunks of size `≥ minGrain`
    (except possibly the final tail chunk), certifying every chunk via `verifyParChunk`
    and every adjacent pair via `verifyArenaDisjoint`. -/
def partitionRange (totalLen minGrain maxWorkers : Nat) : Array ChunkSpan := Id.run do
  if totalLen == 0 then
    return #[]
  let workers := Nat.max 1 maxWorkers
  let rawChunk := Nat.max 1 ((totalLen + workers - 1) / workers)
  let step := Nat.max minGrain rawChunk
  let mut chunks : Array ChunkSpan := #[]
  let mut cur : Nat := 0
  while cur < totalLen do
    let next := Nat.min totalLen (cur + step)
    if verifyParChunk cur.toUInt64 next.toUInt64 totalLen.toUInt64 minGrain.toUInt64 == 1 then
      if let some prev := chunks.back? then
        let lenA := (prev.endIdx - prev.startIdx).toUInt64
        let lenB := (next - cur).toUInt64
        if verifyArenaDisjoint prev.startIdx.toUInt64 lenA cur.toUInt64 lenB totalLen.toUInt64 == 1 then
          chunks := chunks.push { startIdx := cur, endIdx := next }
      else
        chunks := chunks.push { startIdx := cur, endIdx := next }
    cur := next
  return chunks

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

end LeanSys.Par
