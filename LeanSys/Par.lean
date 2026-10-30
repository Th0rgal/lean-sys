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
  avx2       : Bool    := false
  avx512f    : Bool    := false
  avx512bwVl : Bool    := false
  shaNi      : Bool    := false
  vpclmulqdq : Bool    := false
  avx512Full : Bool    := false
  deriving Repr, DecidableEq, Inhabited

namespace IsaLevel

/-- Pointwise partial order on `IsaLevel`: `a.le b == true` iff every capability required by `a` is provided by `b`. -/
def le (a b : IsaLevel) : Bool :=
  decide (a.base.rank ≤ b.base.rank) &&
  (!a.neon || b.neon) && (!a.fp16 || b.fp16) && (!a.dotprod || b.dotprod) &&
  (!a.i8mm || b.i8mm) && (!a.bf16 || b.bf16) && (!a.sve2 || b.sve2) &&
  (!a.sveBitperm || b.sveBitperm) && (!a.sme2 || b.sme2) &&
  (!a.lse || b.lse) && (!a.sha3 || b.sha3) &&
  (!a.avx2 || b.avx2) && (!a.avx512f || b.avx512f) && (!a.avx512bwVl || b.avx512bwVl) &&
  (!a.shaNi || b.shaNi) && (!a.vpclmulqdq || b.vpclmulqdq) && (!a.avx512Full || b.avx512Full)

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
  avx2       := a.avx2 && b.avx2
  avx512f    := a.avx512f && b.avx512f
  avx512bwVl := a.avx512bwVl && b.avx512bwVl
  shaNi      := a.shaNi && b.shaNi
  vpclmulqdq := a.vpclmulqdq && b.vpclmulqdq
  avx512Full := a.avx512Full && b.avx512Full

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
  avx2       := a.avx2 || b.avx2
  avx512f    := a.avx512f || b.avx512f
  avx512bwVl := a.avx512bwVl || b.avx512bwVl
  shaNi      := a.shaNi || b.shaNi
  vpclmulqdq := a.vpclmulqdq || b.vpclmulqdq
  avx512Full := a.avx512Full || b.avx512Full

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
  (if a.sha3       then (1 : UInt64) <<< 9 else 0) |||
  (if a.avx2       then (1 : UInt64) <<< 10 else 0) |||
  (if a.avx512f    then (1 : UInt64) <<< 11 else 0) |||
  (if a.avx512bwVl then (1 : UInt64) <<< 12 else 0) |||
  (if a.shaNi      then (1 : UInt64) <<< 13 else 0) |||
  (if a.vpclmulqdq then (1 : UInt64) <<< 14 else 0) |||
  (if a.avx512Full then (1 : UInt64) <<< 15 else 0)

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

theorem bool_wellFormed_meet_step (s1 v1 m1 r4_1 r5_1 s2 v2 m2 r4_2 r5_2 : Bool)
    (h1 : ((!s1 || v1) && (!v1 || r4_1) && (!m1 || r5_1)) = true)
    (h2 : ((!s2 || v2) && (!v2 || r4_2) && (!m2 || r5_2)) = true) :
    ((!(s1 && s2) || (v1 && v2)) &&
     (!(v1 && v2) || (r4_1 && r4_2)) &&
     (!(m1 && m2) || (r5_1 && r5_2))) = true := by
  cases s1 <;> cases v1 <;> cases m1 <;> cases r4_1 <;> cases r5_1 <;>
  cases s2 <;> cases v2 <;> cases m2 <;> cases r4_2 <;> cases r5_2 <;>
  revert h1 h2 <;> decide

theorem bool_wellFormed_join_step (s1 v1 m1 r4_1 r5_1 s2 v2 m2 r4_2 r5_2 : Bool)
    (h1 : ((!s1 || v1) && (!v1 || r4_1) && (!m1 || r5_1)) = true)
    (h2 : ((!s2 || v2) && (!v2 || r4_2) && (!m2 || r5_2)) = true) :
    ((!(s1 || s2) || (v1 || v2)) &&
     (!(v1 || v2) || (r4_1 || r4_2)) &&
     (!(m1 || m2) || (r5_1 || r5_2))) = true := by
  cases s1 <;> cases v1 <;> cases m1 <;> cases r4_1 <;> cases r5_1 <;>
  cases s2 <;> cases v2 <;> cases m2 <;> cases r4_2 <;> cases r5_2 <;>
  revert h1 h2 <;> decide

theorem ArmBase.min_rank_ge_4 (x y : ArmBase) :
    decide (4 ≤ (ArmBase.ofRank (Nat.min x.rank y.rank)).rank) =
    (decide (4 ≤ x.rank) && decide (4 ≤ y.rank)) := by
  cases x <;> cases y <;> rfl

theorem ArmBase.min_rank_ge_5 (x y : ArmBase) :
    decide (5 ≤ (ArmBase.ofRank (Nat.min x.rank y.rank)).rank) =
    (decide (5 ≤ x.rank) && decide (5 ≤ y.rank)) := by
  cases x <;> cases y <;> rfl

theorem ArmBase.max_rank_ge_4 (x y : ArmBase) :
    decide (4 ≤ (ArmBase.ofRank (Nat.max x.rank y.rank)).rank) =
    (decide (4 ≤ x.rank) || decide (4 ≤ y.rank)) := by
  cases x <;> cases y <;> rfl

theorem ArmBase.max_rank_ge_5 (x y : ArmBase) :
    decide (5 ≤ (ArmBase.ofRank (Nat.max x.rank y.rank)).rank) =
    (decide (5 ≤ x.rank) || decide (5 ≤ y.rank)) := by
  cases x <;> cases y <;> rfl

/-- `meet` preserves architectural well-formedness (`sveBitperm → sve2`, `sve2 → base ≥ v9_0`, `sme2 → base ≥ v9_2`). -/
theorem meet_wellFormed (a b : IsaLevel) (ha : a.wellFormed = true) (hb : b.wellFormed = true) :
    (a.meet b).wellFormed = true := by
  unfold wellFormed meet at *
  dsimp only
  rw [ArmBase.min_rank_ge_4, ArmBase.min_rank_ge_5]
  exact bool_wellFormed_meet_step
    a.sveBitperm a.sve2 a.sme2 (decide (4 ≤ a.base.rank)) (decide (5 ≤ a.base.rank))
    b.sveBitperm b.sve2 b.sme2 (decide (4 ≤ b.base.rank)) (decide (5 ≤ b.base.rank)) ha hb

/-- `join` preserves architectural well-formedness (`sveBitperm → sve2`, `sve2 → base ≥ v9_0`, `sme2 → base ≥ v9_2`). -/
theorem join_wellFormed (a b : IsaLevel) (ha : a.wellFormed = true) (hb : b.wellFormed = true) :
    (a.join b).wellFormed = true := by
  unfold wellFormed join at *
  dsimp only
  rw [ArmBase.max_rank_ge_4, ArmBase.max_rank_ge_5]
  exact bool_wellFormed_join_step
    a.sveBitperm a.sve2 a.sme2 (decide (4 ≤ a.base.rank)) (decide (5 ≤ a.base.rank))
    b.sveBitperm b.sve2 b.sme2 (decide (4 ≤ b.base.rank)) (decide (5 ≤ b.base.rank)) ha hb

/-- Construct a well-formed `IsaLevel` from Linux AArch64 `AT_HWCAP` (`hwcap`) and `AT_HWCAP2` (`hwcap2`) bitmasks:
    - `hwcap`: bit 1 (`ASIMD`/`neon`), bit 8 (`ATOMICS`/`lse`), bit 10 (`ASIMDHP`/`fp16`), bit 17 (`SHA3`), bit 20 (`ASIMDDP`/`dotprod`)
    - `hwcap2`: bit 1 (`SVE2`), bit 4 (`SVEBITPERM`), bit 13 (`I8MM`), bit 14 (`BF16`), bit 37 (`SME2`) -/
def ofLinuxHwcap (hwcap hwcap2 : UInt64) : IsaLevel :=
  let hasNeon    := (hwcap &&& ((1 : UInt64) <<< 1)) != 0
  let hasLse     := (hwcap &&& ((1 : UInt64) <<< 8)) != 0
  let hasFp16    := (hwcap &&& ((1 : UInt64) <<< 10)) != 0
  let hasSha3    := (hwcap &&& ((1 : UInt64) <<< 17)) != 0
  let hasDotprod := (hwcap &&& ((1 : UInt64) <<< 20)) != 0
  let hasSve2    := (hwcap2 &&& ((1 : UInt64) <<< 1)) != 0
  let hasBitperm := hasSve2 && ((hwcap2 &&& ((1 : UInt64) <<< 4)) != 0)
  let hasI8mm    := (hwcap2 &&& ((1 : UInt64) <<< 13)) != 0
  let hasBf16    := (hwcap2 &&& ((1 : UInt64) <<< 14)) != 0
  let hasSme2    := (hwcap2 &&& ((1 : UInt64) <<< 37)) != 0
  let base : ArmBase :=
    if hasSme2 then .v9_2
    else if hasSve2 then .v9_0
    else if hasI8mm || hasBf16 then .v8_6
    else if hasSha3 then .v8_5
    else if hasDotprod || hasLse || hasFp16 then .v8_2
    else .v8_0
  { base := base, neon := hasNeon, fp16 := hasFp16, dotprod := hasDotprod,
    i8mm := hasI8mm, bf16 := hasBf16, sve2 := hasSve2, sveBitperm := hasBitperm,
    sme2 := hasSme2, lse := hasLse, sha3 := hasSha3 }

theorem ofLinuxHwcap_wellFormed_aux (sme2 sve2 bitperm i8mm bf16 sha3 dp lse fp16 : Bool) :
    let b : ArmBase :=
      if sme2 then .v9_2
      else if sve2 then .v9_0
      else if i8mm || bf16 then .v8_6
      else if sha3 then .v8_5
      else if dp || lse || fp16 then .v8_2
      else .v8_0
    ((!(sve2 && bitperm) || sve2) && (!sve2 || decide (4 ≤ b.rank)) && (!sme2 || decide (5 ≤ b.rank))) = true := by
  cases sme2 <;> cases sve2 <;> cases bitperm <;>
  cases i8mm <;> cases bf16 <;> cases sha3 <;> cases dp <;> cases lse <;> cases fp16 <;> rfl

/-- `ofLinuxHwcap` always returns an architecturally well-formed `IsaLevel`. -/
theorem ofLinuxHwcap_wellFormed (hwcap hwcap2 : UInt64) :
    (ofLinuxHwcap hwcap hwcap2).wellFormed = true := by
  unfold ofLinuxHwcap wellFormed
  dsimp only
  exact ofLinuxHwcap_wellFormed_aux
    ((hwcap2 &&& ((1 : UInt64) <<< 37)) != 0)
    ((hwcap2 &&& ((1 : UInt64) <<< 1)) != 0)
    ((hwcap2 &&& ((1 : UInt64) <<< 4)) != 0)
    ((hwcap2 &&& ((1 : UInt64) <<< 13)) != 0)
    ((hwcap2 &&& ((1 : UInt64) <<< 14)) != 0)
    ((hwcap &&& ((1 : UInt64) <<< 17)) != 0)
    ((hwcap &&& ((1 : UInt64) <<< 20)) != 0)
    ((hwcap &&& ((1 : UInt64) <<< 8)) != 0)
    ((hwcap &&& ((1 : UInt64) <<< 10)) != 0)

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

/-- AMD Zen 4 x86_64 server preset (`AVX2` + `AVX-512F/BW/VL` + `SHA-NI` + `VPCLMULQDQ`, variant `5`). -/
def x86Zen4 : IsaLevel :=
  { neon := false, avx2 := true, avx512f := true, avx512bwVl := true, shaNi := true, vpclmulqdq := true }

/-- AMD Zen 5 x86_64 server preset (full-width 512-bit `AVX-512` + `SHA-NI` + `VPCLMULQDQ`, variant `6`). -/
def x86Zen5 : IsaLevel :=
  { neon := false, avx2 := true, avx512f := true, avx512bwVl := true, shaNi := true, vpclmulqdq := true, avx512Full := true }

/-- Construct an x86_64 `IsaLevel` from Linux `/proc/cpuinfo` feature flags (`avx2`, `avx512f`, `avx512bw`, `avx512vl`, `sha_ni`, `vpclmulqdq`, `zen5FullWidth`). -/
def ofX86CpuFeatures (avx2 avx512f avx512bw avx512vl shaNi vpclmulqdq zen5FullWidth : Bool) : IsaLevel :=
  let bwVl := avx512f && avx512bw && avx512vl
  { neon := false,
    avx2 := avx2,
    avx512f := avx512f,
    avx512bwVl := bwVl,
    shaNi := shaNi,
    vpclmulqdq := vpclmulqdq,
    avx512Full := bwVl && zen5FullWidth }

/-- All canonical `IsaLevel` presets satisfy `wellFormed`. -/
theorem presets_wellFormed :
    arm64Baseline.wellFormed = true ∧
    appleA15.wellFormed = true ∧
    appleA16_A17.wellFormed = true ∧
    tensorG3.wellFormed = true ∧
    appleM4_A18.wellFormed = true ∧
    x86Zen4.wellFormed = true ∧
    x86Zen5.wellFormed = true := by decide

/-- All canonical `IsaLevel` preset bitmasks match `isaVariantRequiredMask 0..6`. -/
theorem preset_masks_match_table :
    arm64Baseline.hwcapMask = isaVariantRequiredMask 0 ∧
    appleA15.hwcapMask = isaVariantRequiredMask 1 ∧
    appleA16_A17.hwcapMask = isaVariantRequiredMask 2 ∧
    tensorG3.hwcapMask = isaVariantRequiredMask 3 ∧
    appleM4_A18.hwcapMask = isaVariantRequiredMask 4 ∧
    x86Zen4.hwcapMask = isaVariantRequiredMask 5 ∧
    x86Zen5.hwcapMask = isaVariantRequiredMask 6 := by decide

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

def maxClusterPerf (t : CoreTopology) : Nat :=
  t.foldl (fun acc c => Nat.max acc c.relPerf) 1000

/-- Compute micro-chunk oversubscription factor (`2..8`) from cluster weight asymmetry
    (`maxClusterPerf` vs mean core weight `totalWeight / totalCores`) and tier count (`2` for SMP, `4` for A15, `6` for Tensor G3). -/
def weightedChunkFactor (t : CoreTopology) : Nat :=
  let cores := Nat.max 1 (totalCores t)
  let meanWeight := Nat.max 1 (totalWeight t / cores)
  let maxPerf := maxClusterPerf t
  let tierBonus := Nat.min 3 (t.length - 1)
  let raw := (maxPerf * 2 + meanWeight / 2) / meanWeight + tierBonus
  Nat.min 8 (Nat.max 2 raw)

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

/-- Bounded worker pool & micro-chunk configuration parameterized by cluster topology (`topologyKind`: `0 = SMP`, `1 = 2P+4E`, `2 = 1+4+4`). -/
structure WorkerBudget where
  maxWorkers       : Nat   := 6
  microChunkFactor : Nat   := 4
  minGrain         : Nat   := 64
  topologyKind     : UInt8 := 0
  deriving Repr, DecidableEq, Inhabited

/-- Derived predicate: true iff `topologyKind > 0` (asymmetric mobile multi-cluster topology). -/
@[inline]
def WorkerBudget.isMobileHetero (b : WorkerBudget) : Bool :=
  b.topologyKind > 0

/-- Construct a `WorkerBudget` calibrated to a `CoreTopology` via `CoreTopology.weightedChunkFactor` (`factor = 2` for SMP, `4` for 2-tier P+E, `6` for 3-tier Prime+Mid+Little). -/
def WorkerBudget.ofTopology (t : CoreTopology) (minGrain : Nat := 64) : WorkerBudget :=
  let kind := CoreTopology.topologyKind t
  let cores := Nat.max 1 (CoreTopology.totalCores t)
  let factor := CoreTopology.weightedChunkFactor t
  { maxWorkers := cores, microChunkFactor := factor, minGrain := minGrain, topologyKind := kind }

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
  let kind : UInt8 := if budget.topologyKind ≤ 2 then budget.topologyKind else 0
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
