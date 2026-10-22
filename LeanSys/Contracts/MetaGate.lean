/-
  LeanSys.Contracts.MetaGate: Universal Layer-0 MetaGate Specification Contract (`0 import Lean`, `0 sorryAx`)
-/

namespace LeanSys.Contracts

/-- Universal 4-property Meta-Gate specification bundle proving soundness, completeness,
    non-vacuity, and tightness across `lean-sys`, `turbo-lean`, `lean-native`, and `maxwell`. -/
structure MetaGateSpec (Input : Type) (Safe : Input → Prop) where
  gate       : Input → Bool
  sound      : ∀ x, gate x = true → Safe x
  complete   : ∀ x, Safe x → gate x = true
  posWitness : Input
  negWitness : Input
  nonVacuous : gate posWitness = true
  tight      : gate negWitness = false

theorem MetaGateSpec.iff_safe {Input : Type} {Safe : Input → Prop}
    (M : MetaGateSpec Input Safe) (x : Input) :
    M.gate x = true ↔ Safe x := ⟨M.sound x, M.complete x⟩

theorem MetaGateSpec.rejects_unsafe {Input : Type} {Safe : Input → Prop}
    (M : MetaGateSpec Input Safe) (x : Input) (h_unsafe : ¬ Safe x) :
    M.gate x = false :=
  Bool.eq_false_iff.mpr (fun h_ok => h_unsafe (M.sound x h_ok))

theorem MetaGateSpec.pos_ne_neg {Input : Type} {Safe : Input → Prop}
    (M : MetaGateSpec Input Safe) :
    M.posWitness ≠ M.negWitness :=
  fun h => by simpa [h, M.tight] using M.nonVacuous

end LeanSys.Contracts
