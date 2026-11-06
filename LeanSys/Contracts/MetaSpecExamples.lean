import LeanSys.Contracts.MetaSpec

namespace LeanSys.Contracts.Examples

structure Ledger where
  balance : Nat
  tag : Nat
  deriving DecidableEq

def credit (s : Ledger) (amount : Nat) : Ledger :=
  { s with balance := s.balance + amount }

def creditFrame : FrameInvariant Ledger Nat Nat where
  project := Ledger.tag
  step := credit
  preserved _ _ := rfl

def creditDelta : ExactDeltaSpec Ledger Nat Nat Nat where
  frame := creditFrame
  readWrite := Ledger.balance
  expectedWrite s amount := s.balance + amount
  delta_exact _ _ := rfl
  witnessState := ⟨4, 9⟩
  witnessOp := 3
  nonTrivialWrite := by decide

example : creditDelta.frame.step ≠ (fun s _ => s) :=
  creditDelta.refutes_noop_step _ (fun _ _ => rfl)

example (s : Ledger) (n : Nat) :
    (credit s n).tag = s.tag ∧ (credit s n).balance = s.balance + n :=
  creditDelta.frame_and_delta s n

def creditAccounting : AccountingBoundarySpec Ledger Nat where
  step := credit
  measure := Ledger.balance
  inflow _ n := n
  outflow _ _ := 0
  conserved _ _ := by simp [credit]

example (s : Ledger) (a b : Nat) :
    (creditAccounting.composeSeq creditAccounting rfl).measure
        (credit (credit s a) b) = s.balance + (a + b) := by
  have h := (creditAccounting.composeSeq creditAccounting rfl).conserved s (a, b)
  simpa [AccountingBoundarySpec.composeSeq, creditAccounting] using h

example (s : Ledger) (amounts : List Nat) :
    (amounts.foldl credit s).balance =
      s.balance + creditAccounting.totalInflow s amounts := by
  have hZero : ∀ st, creditAccounting.totalOutflow st amounts = 0 := by
    induction amounts with
    | nil => intro st; rfl
    | cons n ns ih => intro st; simpa [AccountingBoundarySpec.totalOutflow, creditAccounting] using ih (credit st n)
  have hCons := creditAccounting.conserved_list s amounts
  rw [hZero s, Nat.add_zero] at hCons
  exact hCons

theorem readBalance : ReadOnlyQuerySpec Ledger Unit Nat
    (fun s _ => (s.balance, s)) (fun s _ => s.balance) where
  frame_preserved _ _ := rfl
  value_exact _ _ := rfl

example (s : Ledger) : (s.balance, s) = (s.balance, s) :=
  readBalance.sound s ()

example : ¬ (∀ s : Ledger, (s.balance, credit s 1).2 = s) := by
  intro h
  have hBalance := congrArg Ledger.balance (h ⟨0, 0⟩)
  contradiction

def successorSpec : NonVacuousSpec Nat Nat (fun _ => True)
    (fun x y => y = x + 1) (fun x => x + 1) where
  sound _ _ := rfl
  okWitness := 0
  pre_inhabited := True.intro
  badOutputWitness := 0
  post_non_tautological := by decide

def successorTwice : NonVacuousSpec Nat Nat (fun _ => True)
    (fun x z => x + 1 = x + 1 ∧ z = (x + 1) + 1)
    (fun x => (x + 1) + 1) :=
  successorSpec.comp successorSpec (fun _ _ _ => True.intro) 0 (by decide)

example : (0 + 1) + 1 ≠ successorTwice.badOutputWitness :=
  successorTwice.step_ne_bad

example : ¬ Nonempty (NonVacuousSpec Nat Nat (fun _ => False)
    (fun x y => y = x + 1) (fun x => x + 1)) :=
  NonVacuousSpec.refutes_unsat_pre (fun _ h => h)

example : ¬ Nonempty (NonVacuousSpec Nat Nat (fun _ => True)
    (fun _ _ => True) id) :=
  NonVacuousSpec.refutes_taut_post (fun _ _ => True.intro)

def successorAlgorithm : MetaAlgorithmSpec Nat Nat where
  fast n := ⟨n + 1, 1⟩
  oracle n := n + 1
  stepBound _ := 1
  equiv _ := rfl
  bounded _ := Nat.le_refl _

example (n : Nat) :
    ((successorAlgorithm.compose successorAlgorithm).fast n).val = (n + 1) + 1 ∧
    ((successorAlgorithm.compose successorAlgorithm).fast n).steps ≤ 2 :=
  (successorAlgorithm.compose successorAlgorithm).sound_and_bounded n

def arithRefuter : WitnessRefuter Nat Nat (fun x y => y = x + 1) where
  reference x := x + 1
  mutant x := x + 2
  ref_sound _ := rfl
  killWitness := 0
  mutant_refuted := by decide

def fieldRefuter : WitnessRefuter Nat Nat (fun x y => y = x + 1) where
  reference x := x + 1
  mutant := id
  ref_sound _ := rfl
  killWitness := 0
  mutant_refuted := by decide

def orderRefuter : WitnessRefuter Nat Nat (fun x y => y = x + 1) where
  reference x := x + 1
  mutant x := (x + 1) * 2
  ref_sound _ := rfl
  killWitness := 1
  mutant_refuted := by decide

def successorMutants : MutantKillBundle Nat Nat (fun x y => y = x + 1) where
  reference x := x + 1
  arithMutant := arithRefuter
  fieldMutant := fieldRefuter
  orderMutant := orderRefuter

example : ¬ (∀ x, arithRefuter.mutant x = x + 1) :=
  arithRefuter.mutant_not_globally_valid

example : orderRefuter.mutant 1 ≠ successorMutants.reference 1 :=
  (successorMutants.toMatrix.entry_refuted ("order", orderRefuter) (by simp [MutantKillBundle.toMatrix, successorMutants])).2

def checkedSuccessor (n : Nat) : Option Nat :=
  if n = 0 then none else some (n + 1)

def successorPartition : OutcomePartition Nat (Option Nat) checkedSuccessor (fun n => n = 0) :=
  OutcomePartition.ofErrIff checkedSuccessor (fun n => n = 0)
    (fun n => by by_cases h : n = 0 <;> simp [checkedSuccessor, h, OutcomeClassifier.isErr])
    1 0 rfl rfl

example : successorPartition.toMetaGateSpec.gate 1 = true ∧
    successorPartition.toMetaGateSpec.gate 0 = false :=
  ⟨rfl, rfl⟩

example : successorPartition.okWitness ≠ successorPartition.errWitness :=
  successorPartition.ok_ne_err

example : ¬ (∀ n, OutcomeClassifier.isErr (none : Option Nat) = true ↔ n = 0) := by
  intro h
  have : (1 : Nat) = 0 := (h 1).mp rfl
  contradiction

example : ¬ (∀ n, OutcomeClassifier.isErr (some (n + 1)) = true ↔ n = 0) := by
  intro h
  have := (h 0).mpr rfl
  contradiction

theorem maxOrder : OrderIndependence Nat Nat max where
  idempotent s x := by omega
  commutative s x y := by omega

example (s : Nat) : [2, 5, 2].foldl max s = [5, 2].foldl max s :=
  maxOrder.foldl_eraseDup_of_sub _ _ (by simp) (by simp) s

example (s : Nat × Nat) :
    [2, 5].foldl (fun p x => (max p.1 x, max p.2 x)) s =
      [5, 2].foldl (fun p x => (max p.1 x, max p.2 x)) s :=
  (maxOrder.prod maxOrder).swap_pair s 2 5

example : ¬ OrderIndependence Nat Nat (fun s x => s + x) := by
  intro h
  have := h.idempotent 0 1
  contradiction

example : ¬ OrderIndependence Nat Nat (fun _ x => x) := by
  intro h
  have := h.commutative 0 1 2
  contradiction

def incompleteSuite : FiniteMutantScopeBoundary Nat (fun n => n ≤ 1) (fun n => n = 0) where
  killedSuite := [2, 3]
  all_killed n h := by simp at h; rcases h with rfl | rfl <;> decide
  unmodeledBugMutant := 1
  survives_spec := by decide
  violates_adequacy := by decide

theorem incompleteSuite_does_not_prove_completeness :
    (∀ m, m ∈ incompleteSuite.killedSuite → ¬ (m ≤ 1)) ∧ ¬ (∀ n : Nat, n ≤ 1 → n = 0) :=
  incompleteSuite.finite_kills_do_not_prove_completeness

def balancePositiveHypothesisMinimal :
    HypothesisMinimalWitness Ledger Ledger
      (fun s => 0 < s.balance) (fun _ => True)
      (fun _ out => 2 ≤ out.balance) (fun s => credit s 1) where
  dropWitness := ⟨0, 0⟩
  kept_holds := True.intro
  dropped_fails := by decide
  post_fails := by decide

theorem cannot_drop_positive_balance_hypothesis :
    ¬ (∀ s : Ledger, True → 2 ≤ (credit s 1).balance) :=
  balancePositiveHypothesisMinimal.cannot_drop_hypothesis

def deltaIndependentOfFrame :
    ClauseIndependenceWitness (Ledger → Nat → Ledger)
      (fun impl => ∀ s n, (impl s n).balance = s.balance + n)
      (fun impl => ∀ s n, (impl s n).tag = s.tag) where
  separatingMutant s _ := s
  others_satisfied _ _ := rfl
  target_violated h := by
    have := h ⟨0, 0⟩ 1
    contradiction

theorem frame_does_not_entail_delta :
    ¬ (∀ impl : Ledger → Nat → Ledger,
        (∀ s n, (impl s n).tag = s.tag) →
        (∀ s n, (impl s n).balance = s.balance + n)) :=
  deltaIndependentOfFrame.not_entailed

def creditJointSpecs :
    JointSatisfiableSpec (Ledger → Nat → Ledger)
      [(fun impl => ∀ s n, (impl s n).tag = s.tag),
       (fun impl => ∀ s n, (impl s n).balance = s.balance + n)] where
  witness := credit
  all_hold S hMem := by
    simp at hMem
    rcases hMem with rfl | rfl
    · intro _ _; rfl
    · intro _ _; rfl

theorem credit_frame_and_delta_not_contradictory :
    ¬ (∀ impl : Ledger → Nat → Ledger,
        (∀ s n, (impl s n).tag = s.tag) →
        ¬ (∀ s n, (impl s n).balance = s.balance + n)) :=
  creditJointSpecs.no_pairwise_contradiction List.mem_cons_self (List.mem_cons_of_mem _ List.mem_cons_self)

end LeanSys.Contracts.Examples
