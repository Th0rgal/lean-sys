/-
  LeanSys.Gate: Unified Layer-0 Formal Gate & Speculative Execution Contract (`0 import Lean`, `0 sorryAx`)
  Re-exports `MetaGateSpec` (`LeanSys.Contracts.MetaGate`) and `SpeculativeGate` combinators
  (`LeanSys.Contracts.SpeculativeGate`), plus the canonical certificate admission and counterexample
  triage gate predicates shared across `lean-sys`, `turbo-lean`, and `lean-native`.
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

/-- Canonical Layer-0 Counterexample Triage Input (`hasViolation`, `hasMissingHypHint`, `refDisagreesWithCandidate`, `triageClass`).
    `triageClass` encoding: `1 = SpecTooStrong`, `2 = ReferenceDiscrepancy`, `3 = CandidateBug`. -/
structure CounterexampleTriageInput where
  hasViolation              : Bool
  hasMissingHypHint         : Bool
  refDisagreesWithCandidate : Bool
  triageClass               : UInt8
  deriving Repr, DecidableEq, Inhabited

/-- Canonical Layer-0 Counterexample Triage Gate (`checkCounterexampleTriage`):
    - `1 = SpecTooStrong` when `hasMissingHypHint = true`
    - `2 = ReferenceDiscrepancy` when `hasMissingHypHint = false` and `refDisagreesWithCandidate = true`
    - `3 = CandidateBug` when `hasMissingHypHint = false` and `refDisagreesWithCandidate = false` -/
@[inline] def checkCounterexampleTriage (x : CounterexampleTriageInput) : Bool :=
  x.hasViolation &&
  ((x.hasMissingHypHint && x.triageClass == 1) ||
   (!x.hasMissingHypHint && x.refDisagreesWithCandidate && x.triageClass == 2) ||
   (!x.hasMissingHypHint && !x.refDisagreesWithCandidate && x.triageClass == 3))

theorem checkCounterexampleTriage_sound (x : CounterexampleTriageInput) :
    checkCounterexampleTriage x = true ↔
      (x.hasViolation = true ∧
       ((x.hasMissingHypHint = true ∧ x.triageClass == 1) ∨
        (x.hasMissingHypHint = false ∧ x.refDisagreesWithCandidate = true ∧ x.triageClass == 2) ∨
        (x.hasMissingHypHint = false ∧ x.refDisagreesWithCandidate = false ∧ x.triageClass == 3))) := by
  unfold checkCounterexampleTriage
  simp [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', and_assoc, or_assoc]

def counterexampleTriageContractMetaSpec : MetaGateSpec CounterexampleTriageInput
    (fun x => x.hasViolation = true ∧
      ((x.hasMissingHypHint = true ∧ x.triageClass == 1) ∨
       (x.hasMissingHypHint = false ∧ x.refDisagreesWithCandidate = true ∧ x.triageClass == 2) ∨
       (x.hasMissingHypHint = false ∧ x.refDisagreesWithCandidate = false ∧ x.triageClass == 3))) where
  gate := checkCounterexampleTriage
  sound x h := (checkCounterexampleTriage_sound x).mp h
  complete x h := (checkCounterexampleTriage_sound x).mpr h
  posWitness := ⟨true, true, false, 1⟩
  negWitness := ⟨true, true, false, 3⟩
  nonVacuous := rfl
  tight := rfl

end LeanSys.Contracts
