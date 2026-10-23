/-
  LeanSys.Gate: Unified Layer-0 Formal Gate & Speculative Execution Contract (`0 import Lean`, `0 sorryAx`)
  Re-exports `MetaGateSpec` (`LeanSys.Contracts.MetaGate`) and `SpeculativeGate` combinators
  (`LeanSys.Contracts.SpeculativeGate`), plus the canonical certificate admission gate predicate
  shared across `lean-sys`, `turbo-lean`, `lean-native`, and `maxwell`.
-/
import LeanSys.Contracts.MetaGate
import LeanSys.Contracts.SpeculativeGate

namespace LeanSys.Contracts

/-- Canonical 3-flag certificate admission predicate (`noSorryAx && statementPinned && certVerified`). -/
@[inline] def checkGateAdmit (noSorryAx statementPinned certVerified : UInt8) : Bool :=
  noSorryAx == 1 && statementPinned == 1 && certVerified == 1

theorem checkGateAdmit_sound (noSorryAx statementPinned certVerified : UInt8)
    (h : checkGateAdmit noSorryAx statementPinned certVerified = true) :
    noSorryAx == 1 ∧ statementPinned == 1 ∧ certVerified == 1 := by
  unfold checkGateAdmit at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

end LeanSys.Contracts
