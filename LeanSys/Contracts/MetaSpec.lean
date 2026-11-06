import LeanSys.Contracts.MetaGate

namespace LeanSys.Contracts

structure Costed (α : Type) where
  val   : α
  steps : Nat
  deriving Repr, DecidableEq, BEq, Inhabited

structure MetaAlgorithmSpec (Input Output : Type) where
  fast      : Input → Costed Output
  oracle    : Input → Output
  stepBound : Input → Nat
  equiv     : ∀ x, (fast x).val = oracle x
  bounded   : ∀ x, (fast x).steps ≤ stepBound x

theorem MetaAlgorithmSpec.sound_and_bounded {Input Output : Type}
    (A : MetaAlgorithmSpec Input Output) (x : Input) :
    (A.fast x).val = A.oracle x ∧ (A.fast x).steps ≤ A.stepBound x :=
  ⟨A.equiv x, A.bounded x⟩

def MetaAlgorithmSpec.compose {A B C : Type}
    (A₁ : MetaAlgorithmSpec A B) (A₂ : MetaAlgorithmSpec B C) :
    MetaAlgorithmSpec A C where
  fast x :=
    let r₁ := A₁.fast x
    let r₂ := A₂.fast r₁.val
    { val := r₂.val, steps := r₁.steps + r₂.steps }
  oracle x := A₂.oracle (A₁.oracle x)
  stepBound x := A₁.stepBound x + A₂.stepBound (A₁.oracle x)
  equiv x := by
    dsimp only
    rw [A₂.equiv, A₁.equiv]
  bounded x := by
    dsimp only
    have h₁ := A₁.bounded x
    have h₂ := A₂.bounded (A₁.fast x).val
    rw [A₁.equiv x] at h₂ ⊢
    omega

theorem MetaAlgorithmSpec.compose_equiv {A B C : Type}
    (A₁ : MetaAlgorithmSpec A B) (A₂ : MetaAlgorithmSpec B C) (x : A) :
    ((A₁.compose A₂).fast x).val = A₂.oracle (A₁.oracle x) :=
  (A₁.compose A₂).equiv x

theorem MetaAlgorithmSpec.compose_bounded {A B C : Type}
    (A₁ : MetaAlgorithmSpec A B) (A₂ : MetaAlgorithmSpec B C) (x : A) :
    ((A₁.compose A₂).fast x).steps ≤ A₁.stepBound x + A₂.stepBound (A₁.oracle x) :=
  (A₁.compose A₂).bounded x

def SatisfiablePrecondition {Input : Type} (Pre : Input → Prop) : Prop :=
  ∃ w₀ : Input, Pre w₀

structure NonVacuousSpec (Input Output : Type)
    (Pre : Input → Prop) (Post : Input → Output → Prop) (step : Input → Output) where
  sound                 : ∀ x, Pre x → Post x (step x)
  okWitness             : Input
  pre_inhabited         : Pre okWitness
  badOutputWitness      : Output
  post_non_tautological : ¬ Post okWitness badOutputWitness

theorem NonVacuousSpec.satisfiablePre {Input Output : Type}
    {Pre : Input → Prop} {Post : Input → Output → Prop} {step : Input → Output}
    (S : NonVacuousSpec Input Output Pre Post step) :
    SatisfiablePrecondition Pre :=
  ⟨S.okWitness, S.pre_inhabited⟩

theorem NonVacuousSpec.ok_post {Input Output : Type}
    {Pre : Input → Prop} {Post : Input → Output → Prop} {step : Input → Output}
    (S : NonVacuousSpec Input Output Pre Post step) :
    Post S.okWitness (step S.okWitness) :=
  S.sound S.okWitness S.pre_inhabited

theorem NonVacuousSpec.step_ne_bad {Input Output : Type}
    {Pre : Input → Prop} {Post : Input → Output → Prop} {step : Input → Output}
    (S : NonVacuousSpec Input Output Pre Post step) :
    step S.okWitness ≠ S.badOutputWitness := by
  intro h
  have hPost := S.sound S.okWitness S.pre_inhabited
  rw [h] at hPost
  exact S.post_non_tautological hPost

theorem NonVacuousSpec.refutes_unsat_pre {Input Output : Type}
    {Pre : Input → Prop} {Post : Input → Output → Prop} {step : Input → Output}
    (hUnsat : ∀ x, ¬ Pre x) :
    ¬ Nonempty (NonVacuousSpec Input Output Pre Post step) :=
  fun ⟨S⟩ => hUnsat S.okWitness S.pre_inhabited

theorem NonVacuousSpec.refutes_taut_post {Input Output : Type}
    {Pre : Input → Prop} {Post : Input → Output → Prop} {step : Input → Output}
    (hTaut : ∀ x y, Post x y) :
    ¬ Nonempty (NonVacuousSpec Input Output Pre Post step) :=
  fun ⟨S⟩ => S.post_non_tautological (hTaut S.okWitness S.badOutputWitness)

def NonVacuousSpec.comp {A B C : Type}
    {Pre₁ : A → Prop} {Post₁ : A → B → Prop} {f : A → B}
    {Pre₂ : B → Prop} {Post₂ : B → C → Prop} {g : B → C}
    (S₁ : NonVacuousSpec A B Pre₁ Post₁ f)
    (S₂ : NonVacuousSpec B C Pre₂ Post₂ g)
    (hBridge : ∀ x, Pre₁ x → Post₁ x (f x) → Pre₂ (f x))
    (badOut : C)
    (hBad : ¬ (Post₁ S₁.okWitness (f S₁.okWitness) ∧ Post₂ (f S₁.okWitness) badOut)) :
    NonVacuousSpec A C Pre₁
      (fun x z => Post₁ x (f x) ∧ Post₂ (f x) z)
      (fun x => g (f x)) where
  sound x hx :=
    let hp₁ := S₁.sound x hx
    ⟨hp₁, S₂.sound (f x) (hBridge x hx hp₁)⟩
  okWitness := S₁.okWitness
  pre_inhabited := S₁.pre_inhabited
  badOutputWitness := badOut
  post_non_tautological := hBad

theorem NonVacuousSpec.comp_step_ne_bad {A B C : Type}
    {Pre₁ : A → Prop} {Post₁ : A → B → Prop} {f : A → B}
    {Pre₂ : B → Prop} {Post₂ : B → C → Prop} {g : B → C}
    (S₁ : NonVacuousSpec A B Pre₁ Post₁ f)
    (S₂ : NonVacuousSpec B C Pre₂ Post₂ g)
    (hBridge : ∀ x, Pre₁ x → Post₁ x (f x) → Pre₂ (f x))
    (badOut : C)
    (hBad : ¬ (Post₁ S₁.okWitness (f S₁.okWitness) ∧ Post₂ (f S₁.okWitness) badOut)) :
    g (f S₁.okWitness) ≠ badOut :=
  (S₁.comp S₂ hBridge badOut hBad).step_ne_bad

def NonVacuousSpec.weakenPre {Input Output : Type}
    {Pre₁ Pre₂ : Input → Prop} {Post : Input → Output → Prop} {step : Input → Output}
    (S : NonVacuousSpec Input Output Pre₁ Post step)
    (hWeaken : ∀ x, Pre₁ x → Pre₂ x)
    (hSound₂ : ∀ x, Pre₂ x → Post x (step x)) :
    NonVacuousSpec Input Output Pre₂ Post step where
  sound := hSound₂
  okWitness := S.okWitness
  pre_inhabited := hWeaken S.okWitness S.pre_inhabited
  badOutputWitness := S.badOutputWitness
  post_non_tautological := S.post_non_tautological

def NonVacuousSpec.strengthenPost {Input Output : Type}
    {Pre : Input → Prop} {Post₁ Post₂ : Input → Output → Prop} {step : Input → Output}
    (S : NonVacuousSpec Input Output Pre Post₁ step)
    (hImp : ∀ x y, Pre x → Post₁ x y → Post₂ x y)
    (badOut : Output)
    (hBad₂ : ¬ Post₂ S.okWitness badOut) :
    NonVacuousSpec Input Output Pre Post₂ step where
  sound x hx := hImp x (step x) hx (S.sound x hx)
  okWitness := S.okWitness
  pre_inhabited := S.pre_inhabited
  badOutputWitness := badOut
  post_non_tautological := hBad₂

structure ReadOnlyQuerySpec (State Input Output : Type)
    (query : State → Input → Output × State)
    (expected : State → Input → Output) where
  frame_preserved : ∀ s x, (query s x).2 = s
  value_exact     : ∀ s x, (query s x).1 = expected s x

theorem ReadOnlyQuerySpec.sound {State Input Output : Type}
    {query : State → Input → Output × State}
    {expected : State → Input → Output}
    (Q : ReadOnlyQuerySpec State Input Output query expected)
    (s : State) (x : Input) :
    query s x = (expected s x, s) :=
  Prod.ext (Q.value_exact s x) (Q.frame_preserved s x)

structure FrameInvariant (State Op : Type) (Proj : Type) where
  project   : State → Proj
  step      : State → Op → State
  preserved : ∀ (s : State) (op : Op), project (step s op) = project s

theorem FrameInvariant.preserved_list {State Op Proj : Type}
    (F : FrameInvariant State Op Proj) (s : State) (ops : List Op) :
    F.project (ops.foldl F.step s) = F.project s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op rest ih => simpa [List.foldl, F.preserved s op] using ih (F.step s op)

def FrameInvariant.pair {State Op Proj₁ Proj₂ : Type}
    (F₁ : FrameInvariant State Op Proj₁)
    (F₂ : FrameInvariant State Op Proj₂)
    (hStep : F₁.step = F₂.step) :
    FrameInvariant State Op (Proj₁ × Proj₂) where
  project s := (F₁.project s, F₂.project s)
  step := F₁.step
  preserved s op := by
    apply Prod.ext
    · exact F₁.preserved s op
    · rw [hStep]
      exact F₂.preserved s op

theorem FrameInvariant.pair_preserved {State Op Proj₁ Proj₂ : Type}
    (F₁ : FrameInvariant State Op Proj₁)
    (F₂ : FrameInvariant State Op Proj₂)
    (hStep : F₁.step = F₂.step) (s : State) (op : Op) :
    (F₁.pair F₂ hStep).project (F₁.step s op) = (F₁.project s, F₂.project s) :=
  (F₁.pair F₂ hStep).preserved s op

def FrameInvariant.mapProj {State Op Proj₁ Proj₂ : Type}
    (F : FrameInvariant State Op Proj₁) (g : Proj₁ → Proj₂) :
    FrameInvariant State Op Proj₂ where
  project s := g (F.project s)
  step := F.step
  preserved s op := congrArg g (F.preserved s op)

theorem FrameInvariant.mapProj_preserved {State Op Proj₁ Proj₂ : Type}
    (F : FrameInvariant State Op Proj₁) (g : Proj₁ → Proj₂) (s : State) (op : Op) :
    g (F.project (F.step s op)) = g (F.project s) :=
  (F.mapProj g).preserved s op

structure ExactDeltaSpec (State Op FrameProj WriteProj : Type) where
  frame           : FrameInvariant State Op FrameProj
  readWrite       : State → WriteProj
  expectedWrite   : State → Op → WriteProj
  delta_exact     : ∀ (s : State) (op : Op),
    readWrite (frame.step s op) = expectedWrite s op
  witnessState    : State
  witnessOp       : Op
  nonTrivialWrite : readWrite (frame.step witnessState witnessOp) ≠ readWrite witnessState

theorem ExactDeltaSpec.witness_step_ne_id {State Op FrameProj WriteProj : Type}
    (E : ExactDeltaSpec State Op FrameProj WriteProj) :
    E.frame.step E.witnessState E.witnessOp ≠ E.witnessState :=
  fun hEq => E.nonTrivialWrite (congrArg E.readWrite hEq)

theorem ExactDeltaSpec.witness_expected_ne_prior {State Op FrameProj WriteProj : Type}
    (E : ExactDeltaSpec State Op FrameProj WriteProj) :
    E.expectedWrite E.witnessState E.witnessOp ≠ E.readWrite E.witnessState := by
  rw [← E.delta_exact E.witnessState E.witnessOp]
  exact E.nonTrivialWrite

theorem ExactDeltaSpec.frame_and_delta {State Op FrameProj WriteProj : Type}
    (E : ExactDeltaSpec State Op FrameProj WriteProj) (s : State) (op : Op) :
    E.frame.project (E.frame.step s op) = E.frame.project s ∧
      E.readWrite (E.frame.step s op) = E.expectedWrite s op :=
  ⟨E.frame.preserved s op, E.delta_exact s op⟩

theorem ExactDeltaSpec.refutes_noop_step {State Op FrameProj WriteProj : Type}
    (step : State → Op → State) (hNoop : ∀ s op, step s op = s)
    (E : ExactDeltaSpec State Op FrameProj WriteProj) :
    E.frame.step ≠ step := by
  intro hEq
  apply E.witness_step_ne_id
  rw [hEq]
  exact hNoop E.witnessState E.witnessOp

structure WitnessRefuter (Input Output : Type) (Valid : Input → Output → Prop) where
  reference      : Input → Output
  mutant         : Input → Output
  ref_sound      : ∀ x, Valid x (reference x)
  killWitness    : Input
  mutant_refuted : ¬ Valid killWitness (mutant killWitness)

theorem WitnessRefuter.mutant_ne_reference {Input Output : Type}
    {Valid : Input → Output → Prop} (W : WitnessRefuter Input Output Valid) :
    W.mutant W.killWitness ≠ W.reference W.killWitness := by
  intro h
  have hValid := W.ref_sound W.killWitness
  rw [← h] at hValid
  exact W.mutant_refuted hValid

theorem WitnessRefuter.mutant_not_globally_valid {Input Output : Type}
    {Valid : Input → Output → Prop} (W : WitnessRefuter Input Output Valid) :
    ¬ (∀ x, Valid x (W.mutant x)) :=
  fun hAll => W.mutant_refuted (hAll W.killWitness)

def WitnessRefuter.mapValid {Input Output : Type}
    {Valid₁ Valid₂ : Input → Output → Prop}
    (W : WitnessRefuter Input Output Valid₁)
    (hRef₂ : ∀ x, Valid₂ x (W.reference x))
    (hImp : ∀ y, Valid₂ W.killWitness y → Valid₁ W.killWitness y) :
    WitnessRefuter Input Output Valid₂ where
  reference := W.reference
  mutant := W.mutant
  ref_sound := hRef₂
  killWitness := W.killWitness
  mutant_refuted h := W.mutant_refuted (hImp (W.mutant W.killWitness) h)

theorem WitnessRefuter.mapValid_refutes {Input Output : Type}
    {Valid₁ Valid₂ : Input → Output → Prop}
    (W : WitnessRefuter Input Output Valid₁)
    (hRef₂ : ∀ x, Valid₂ x (W.reference x))
    (hImp : ∀ y, Valid₂ W.killWitness y → Valid₁ W.killWitness y) :
    ¬ Valid₂ W.killWitness (W.mutant W.killWitness) :=
  (W.mapValid hRef₂ hImp).mutant_refuted

structure MutantKillBundle (Input Output : Type) (Valid : Input → Output → Prop) where
  reference    : Input → Output
  arithMutant  : WitnessRefuter Input Output Valid
  fieldMutant  : WitnessRefuter Input Output Valid
  orderMutant  : WitnessRefuter Input Output Valid
  arith_ref_eq : arithMutant.reference = reference := by rfl
  field_ref_eq : fieldMutant.reference = reference := by rfl
  order_ref_eq : orderMutant.reference = reference := by rfl

theorem MutantKillBundle.ref_sound {Input Output : Type} {Valid : Input → Output → Prop}
    (B : MutantKillBundle Input Output Valid) (x : Input) :
    Valid x (B.reference x) := by
  rw [← B.arith_ref_eq]
  exact B.arithMutant.ref_sound x

theorem MutantKillBundle.all_mutants_refuted {Input Output : Type} {Valid : Input → Output → Prop}
    (B : MutantKillBundle Input Output Valid) :
    ¬ Valid B.arithMutant.killWitness (B.arithMutant.mutant B.arithMutant.killWitness) ∧
    ¬ Valid B.fieldMutant.killWitness (B.fieldMutant.mutant B.fieldMutant.killWitness) ∧
    ¬ Valid B.orderMutant.killWitness (B.orderMutant.mutant B.orderMutant.killWitness) :=
  ⟨B.arithMutant.mutant_refuted, B.fieldMutant.mutant_refuted, B.orderMutant.mutant_refuted⟩

theorem MutantKillBundle.all_mutants_ne_reference {Input Output : Type} {Valid : Input → Output → Prop}
    (B : MutantKillBundle Input Output Valid) :
    B.arithMutant.mutant B.arithMutant.killWitness ≠ B.reference B.arithMutant.killWitness ∧
    B.fieldMutant.mutant B.fieldMutant.killWitness ≠ B.reference B.fieldMutant.killWitness ∧
    B.orderMutant.mutant B.orderMutant.killWitness ≠ B.reference B.orderMutant.killWitness := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← B.arith_ref_eq]; exact B.arithMutant.mutant_ne_reference
  · rw [← B.field_ref_eq]; exact B.fieldMutant.mutant_ne_reference
  · rw [← B.order_ref_eq]; exact B.orderMutant.mutant_ne_reference

structure MutantKillMatrix (Input Output : Type) (Valid : Input → Output → Prop) where
  reference : Input → Output
  ref_sound : ∀ x, Valid x (reference x)
  entries   : List (String × WitnessRefuter Input Output Valid)
  shared_ref : ∀ p, p ∈ entries → p.2.reference = reference

theorem MutantKillMatrix.entry_refuted {Input Output : Type} {Valid : Input → Output → Prop}
    (M : MutantKillMatrix Input Output Valid) (p : String × WitnessRefuter Input Output Valid)
    (hMem : p ∈ M.entries) :
    ¬ Valid p.2.killWitness (p.2.mutant p.2.killWitness) ∧
      p.2.mutant p.2.killWitness ≠ M.reference p.2.killWitness := by
  refine ⟨p.2.mutant_refuted, ?_⟩
  rw [← M.shared_ref p hMem]
  exact p.2.mutant_ne_reference

def MutantKillBundle.toMatrix {Input Output : Type} {Valid : Input → Output → Prop}
    (B : MutantKillBundle Input Output Valid) :
    MutantKillMatrix Input Output Valid where
  reference := B.reference
  ref_sound := B.ref_sound
  entries := [("arith", B.arithMutant), ("field", B.fieldMutant), ("order", B.orderMutant)]
  shared_ref p hMem := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl
    · exact B.arith_ref_eq
    · exact B.field_ref_eq
    · exact B.order_ref_eq

class OutcomeClassifier (Out : Type) where
  isOk        : Out → Bool
  isErr       : Out → Bool
  isErr_eq_not_isOk : ∀ r, isErr r = !isOk r

theorem OutcomeClassifier.isOk_iff_not_isErr {Out : Type} [OutcomeClassifier Out] (r : Out) :
    OutcomeClassifier.isOk r = true ↔ OutcomeClassifier.isErr r = false := by
  rw [OutcomeClassifier.isErr_eq_not_isOk]
  cases OutcomeClassifier.isOk r <;> simp

theorem OutcomeClassifier.not_ok_and_err {Out : Type} [OutcomeClassifier Out] (r : Out) :
    ¬ (OutcomeClassifier.isOk r = true ∧ OutcomeClassifier.isErr r = true) := by
  rintro ⟨hOk, hErr⟩
  rw [OutcomeClassifier.isErr_eq_not_isOk, hOk] at hErr
  contradiction

instance {α : Type} : OutcomeClassifier (Option α) where
  isOk := Option.isSome
  isErr := Option.isNone
  isErr_eq_not_isOk
    | some _ => rfl
    | none => rfl

instance {ε α : Type} : OutcomeClassifier (Except ε α) where
  isOk
    | .ok _ => true
    | .error _ => false
  isErr
    | .ok _ => false
    | .error _ => true
  isErr_eq_not_isOk
    | .ok _ => rfl
    | .error _ => rfl

instance : OutcomeClassifier Bool where
  isOk b := b
  isErr b := !b
  isErr_eq_not_isOk _ := rfl

structure OutcomePartition (Input Out : Type) [OutcomeClassifier Out]
    (op : Input → Out) (ErrCond : Input → Prop) where
  err_iff          : ∀ s, OutcomeClassifier.isErr (op s) = true ↔ ErrCond s
  ok_iff           : ∀ s, OutcomeClassifier.isOk (op s) = true ↔ ¬ ErrCond s
  okWitness        : Input
  errWitness       : Input
  okWitness_valid  : OutcomeClassifier.isOk (op okWitness) = true
  errWitness_valid : OutcomeClassifier.isErr (op errWitness) = true

def OutcomePartition.ofErrIff {Input Out : Type} [OutcomeClassifier Out]
    (op : Input → Out) (ErrCond : Input → Prop)
    (hErrIff : ∀ s, OutcomeClassifier.isErr (op s) = true ↔ ErrCond s)
    (okW errW : Input)
    (hOkW : OutcomeClassifier.isOk (op okW) = true)
    (hErrW : OutcomeClassifier.isErr (op errW) = true) :
    OutcomePartition Input Out op ErrCond where
  err_iff := hErrIff
  ok_iff s := by
    rw [OutcomeClassifier.isOk_iff_not_isErr, ← Bool.not_eq_true (OutcomeClassifier.isErr (op s)), hErrIff]
  okWitness := okW
  errWitness := errW
  okWitness_valid := hOkW
  errWitness_valid := hErrW

theorem OutcomePartition.ok_ne_err {Input Out : Type} [OutcomeClassifier Out]
    {op : Input → Out} {ErrCond : Input → Prop}
    (P : OutcomePartition Input Out op ErrCond) :
    P.okWitness ≠ P.errWitness := by
  intro hEq
  have hNotErr := (P.ok_iff P.okWitness).mp P.okWitness_valid
  rw [hEq] at hNotErr
  exact hNotErr ((P.err_iff P.errWitness).mp P.errWitness_valid)

theorem OutcomePartition.no_over_revert {Input Out : Type} [OutcomeClassifier Out]
    {op : Input → Out} {ErrCond : Input → Prop}
    (P : OutcomePartition Input Out op ErrCond) (s : Input) (hNoErr : ¬ ErrCond s) :
    OutcomeClassifier.isOk (op s) = true :=
  (P.ok_iff s).mpr hNoErr

theorem OutcomePartition.no_under_revert {Input Out : Type} [OutcomeClassifier Out]
    {op : Input → Out} {ErrCond : Input → Prop}
    (P : OutcomePartition Input Out op ErrCond) (s : Input) (hErr : ErrCond s) :
    OutcomeClassifier.isErr (op s) = true :=
  (P.err_iff s).mpr hErr

def OutcomePartition.toMetaGateSpec {Input Out : Type} [OutcomeClassifier Out]
    {op : Input → Out} {ErrCond : Input → Prop}
    (P : OutcomePartition Input Out op ErrCond) :
    MetaGateSpec Input (fun s => ¬ ErrCond s) where
  gate s := OutcomeClassifier.isOk (op s)
  sound s h := (P.ok_iff s).mp h
  complete s h := (P.ok_iff s).mpr h
  posWitness := P.okWitness
  negWitness := P.errWitness
  nonVacuous := P.okWitness_valid
  tight := by
    have hErr := P.errWitness_valid
    rw [OutcomeClassifier.isErr_eq_not_isOk] at hErr
    cases hOk : OutcomeClassifier.isOk (op P.errWitness) <;> simp_all

structure AccountingBoundarySpec (State Op : Type) where
  step      : State → Op → State
  measure   : State → Nat
  inflow    : State → Op → Nat
  outflow   : State → Op → Nat
  conserved : ∀ (s : State) (op : Op),
    measure (step s op) + outflow s op = measure s + inflow s op

theorem AccountingBoundarySpec.supply_neutral_when_balanced {State Op : Type}
    (A : AccountingBoundarySpec State Op) (s : State) (op : Op)
    (hBal : A.inflow s op = A.outflow s op) :
    A.measure (A.step s op) = A.measure s := by
  have h := A.conserved s op
  omega

def AccountingBoundarySpec.totalInflow {State Op : Type}
    (A : AccountingBoundarySpec State Op) : State → List Op → Nat
  | _, [] => 0
  | s, op :: ops => A.inflow s op + A.totalInflow (A.step s op) ops

def AccountingBoundarySpec.totalOutflow {State Op : Type}
    (A : AccountingBoundarySpec State Op) : State → List Op → Nat
  | _, [] => 0
  | s, op :: ops => A.outflow s op + A.totalOutflow (A.step s op) ops

theorem AccountingBoundarySpec.conserved_list {State Op : Type}
    (A : AccountingBoundarySpec State Op) (s : State) (ops : List Op) :
    A.measure (ops.foldl A.step s) + A.totalOutflow s ops =
      A.measure s + A.totalInflow s ops := by
  induction ops generalizing s with
  | nil => simp [totalOutflow, totalInflow]
  | cons op rest ih =>
    simp only [List.foldl, totalOutflow, totalInflow]
    have hStep := A.conserved s op
    have hRest := ih (A.step s op)
    omega

def AccountingBoundarySpec.composeSeq {State Op₁ Op₂ : Type}
    (A₁ : AccountingBoundarySpec State Op₁)
    (A₂ : AccountingBoundarySpec State Op₂)
    (hMeas : A₁.measure = A₂.measure) :
    AccountingBoundarySpec State (Op₁ × Op₂) where
  step s p := A₂.step (A₁.step s p.1) p.2
  measure := A₁.measure
  inflow s p := A₁.inflow s p.1 + A₂.inflow (A₁.step s p.1) p.2
  outflow s p := A₁.outflow s p.1 + A₂.outflow (A₁.step s p.1) p.2
  conserved s p := by
    have h₁ := A₁.conserved s p.1
    have h₂ := A₂.conserved (A₁.step s p.1) p.2
    rw [← hMeas] at h₂
    omega

theorem AccountingBoundarySpec.composeSeq_conserved {State Op₁ Op₂ : Type}
    (A₁ : AccountingBoundarySpec State Op₁)
    (A₂ : AccountingBoundarySpec State Op₂)
    (hMeas : A₁.measure = A₂.measure) (s : State) (p : Op₁ × Op₂) :
    A₁.measure (A₂.step (A₁.step s p.1) p.2) +
        (A₁.outflow s p.1 + A₂.outflow (A₁.step s p.1) p.2) =
      A₁.measure s + (A₁.inflow s p.1 + A₂.inflow (A₁.step s p.1) p.2) :=
  (A₁.composeSeq A₂ hMeas).conserved s p

structure OrderIndependence (State Elem : Type) (f : State → Elem → State) where
  idempotent  : ∀ (s : State) (x : Elem), f (f s x) x = f s x
  commutative : ∀ (s : State) (x y : Elem), f (f s x) y = f (f s y) x

theorem OrderIndependence.swap_pair {State Elem : Type} {f : State → Elem → State}
    (O : OrderIndependence State Elem f) (s : State) (x y : Elem) :
    [x, y].foldl f s = [y, x].foldl f s :=
  O.commutative s x y

theorem OrderIndependence.dedup_pair {State Elem : Type} {f : State → Elem → State}
    (O : OrderIndependence State Elem f) (s : State) (x : Elem) :
    [x, x].foldl f s = [x].foldl f s :=
  O.idempotent s x

theorem OrderIndependence.foldl_comm_single {State Elem : Type} {f : State → Elem → State}
    (O : OrderIndependence State Elem f) (s : State) (x : Elem) (xs : List Elem) :
    xs.foldl f (f s x) = f (xs.foldl f s) x := by
  induction xs generalizing s with
  | nil => rfl
  | cons y ys ih =>
    dsimp [List.foldl]
    rw [O.commutative s x y]
    exact ih (f s y)

theorem OrderIndependence.foldl_swap_adjacent {State Elem : Type} {f : State → Elem → State}
    (O : OrderIndependence State Elem f) (s : State) (pre suf : List Elem) (x y : Elem) :
    (pre ++ x :: y :: suf).foldl f s = (pre ++ y :: x :: suf).foldl f s := by
  simp only [List.foldl_append, List.foldl]
  rw [O.commutative (pre.foldl f s) x y]

theorem OrderIndependence.foldl_dup_mem {State Elem : Type} {f : State → Elem → State}
    (O : OrderIndependence State Elem f) (s : State) (x : Elem) (xs : List Elem)
    (hMem : x ∈ xs) :
    xs.foldl f (f s x) = xs.foldl f s := by
  induction xs generalizing s with
  | nil => cases hMem
  | cons y ys ih =>
    rcases List.mem_cons.mp hMem with rfl | hTail
    · simp only [List.foldl, O.idempotent s x]
    · simp only [List.foldl]
      rw [O.commutative s x y]
      exact ih (f s y) hTail

theorem OrderIndependence.foldl_perm {State Elem : Type} {f : State → Elem → State}
    (O : OrderIndependence State Elem f) {xs ys : List Elem}
    (hPerm : List.Perm xs ys) (s : State) :
    xs.foldl f s = ys.foldl f s := by
  induction hPerm generalizing s with
  | nil => rfl
  | cons x _ ih => exact ih (f s x)
  | swap x y l =>
    simp only [List.foldl]
    rw [O.commutative s y x]
  | trans _ _ ih₁ ih₂ => exact (ih₁ s).trans (ih₂ s)

theorem OrderIndependence.foldl_eraseDup_of_sub {State Elem : Type} [DecidableEq Elem]
    {f : State → Elem → State}
    (O : OrderIndependence State Elem f) (xs ys : List Elem)
    (hSub₁ : ∀ x, x ∈ xs → x ∈ ys)
    (hSub₂ : ∀ x, x ∈ ys → x ∈ xs)
    (s : State) :
    xs.foldl f s = ys.foldl f s := by
  have hAbsorb : ∀ (as bs : List Elem) (st : State),
      (∀ a, a ∈ as → a ∈ bs) → (bs ++ as).foldl f st = bs.foldl f st := by
    intro as bs st hIn
    induction as generalizing bs st with
    | nil => simp
    | cons a rest ih =>
      have hEq : bs ++ a :: rest = (bs ++ [a]) ++ rest := by simp
      rw [hEq, List.foldl_append]
      have hMem : a ∈ bs := hIn a List.mem_cons_self
      have hStep : (bs ++ [a]).foldl f st = bs.foldl f st := by
        rw [List.foldl_append, List.foldl, List.foldl, ← O.foldl_comm_single st a bs]
        exact O.foldl_dup_mem st a bs hMem
      rw [hStep, ← List.foldl_append]
      exact ih bs st (fun z hz => hIn z (List.mem_cons_of_mem _ hz))
  have hL := hAbsorb ys xs s hSub₂
  have hR := hAbsorb xs ys s hSub₁
  have hPerm : List.Perm (xs ++ ys) (ys ++ xs) := List.perm_append_comm
  calc
    xs.foldl f s = (xs ++ ys).foldl f s := hL.symm
    _ = (ys ++ xs).foldl f s := O.foldl_perm hPerm s
    _ = ys.foldl f s := hR

theorem OrderIndependence.prod {S₁ S₂ Elem : Type}
    {f₁ : S₁ → Elem → S₁} {f₂ : S₂ → Elem → S₂}
    (O₁ : OrderIndependence S₁ Elem f₁)
    (O₂ : OrderIndependence S₂ Elem f₂) :
    OrderIndependence (S₁ × S₂) Elem (fun p x => (f₁ p.1 x, f₂ p.2 x)) where
  idempotent p x := Prod.ext (O₁.idempotent p.1 x) (O₂.idempotent p.2 x)
  commutative p x y := Prod.ext (O₁.commutative p.1 x y) (O₂.commutative p.2 x y)

theorem OrderIndependence.prod_swap_pair {S₁ S₂ Elem : Type}
    {f₁ : S₁ → Elem → S₁} {f₂ : S₂ → Elem → S₂}
    (O₁ : OrderIndependence S₁ Elem f₁)
    (O₂ : OrderIndependence S₂ Elem f₂)
    (p : S₁ × S₂) (x y : Elem) :
    [x, y].foldl (fun q z => (f₁ q.1 z, f₂ q.2 z)) p =
      [y, x].foldl (fun q z => (f₁ q.1 z, f₂ q.2 z)) p :=
  (O₁.prod O₂).swap_pair p x y

structure FiniteMutantScopeBoundary (Impl : Type) (Spec TrueAdequacy : Impl → Prop) where
  killedSuite        : List Impl
  all_killed         : ∀ m, m ∈ killedSuite → ¬ Spec m
  unmodeledBugMutant : Impl
  survives_spec      : Spec unmodeledBugMutant
  violates_adequacy  : ¬ TrueAdequacy unmodeledBugMutant

theorem FiniteMutantScopeBoundary.finite_kills_do_not_prove_completeness
    {Impl : Type} {Spec TrueAdequacy : Impl → Prop}
    (B : FiniteMutantScopeBoundary Impl Spec TrueAdequacy) :
    (∀ m, m ∈ B.killedSuite → ¬ Spec m) ∧ ¬ (∀ impl, Spec impl → TrueAdequacy impl) :=
  ⟨B.all_killed, fun hComplete => B.violates_adequacy (hComplete B.unmodeledBugMutant B.survives_spec)⟩

structure HypothesisMinimalWitness (Input Output : Type)
    (DroppedPre KeptPre : Input → Prop)
    (Post : Input → Output → Prop)
    (step : Input → Output) where
  dropWitness   : Input
  kept_holds    : KeptPre dropWitness
  dropped_fails : ¬ DroppedPre dropWitness
  post_fails    : ¬ Post dropWitness (step dropWitness)

theorem HypothesisMinimalWitness.cannot_drop_hypothesis {Input Output : Type}
    {DroppedPre KeptPre : Input → Prop} {Post : Input → Output → Prop} {step : Input → Output}
    (W : HypothesisMinimalWitness Input Output DroppedPre KeptPre Post step) :
    ¬ (∀ x, KeptPre x → Post x (step x)) :=
  fun hTooWeak => W.post_fails (hTooWeak W.dropWitness W.kept_holds)

structure ClauseIndependenceWitness (Impl : Type)
    (TargetClause OtherClauses : Impl → Prop) where
  separatingMutant : Impl
  others_satisfied : OtherClauses separatingMutant
  target_violated  : ¬ TargetClause separatingMutant

theorem ClauseIndependenceWitness.not_entailed {Impl : Type}
    {TargetClause OtherClauses : Impl → Prop}
    (W : ClauseIndependenceWitness Impl TargetClause OtherClauses) :
    ¬ (∀ impl, OtherClauses impl → TargetClause impl) :=
  fun hRedundant => W.target_violated (hRedundant W.separatingMutant W.others_satisfied)

structure JointSatisfiableSpec (Impl : Type) (Specs : List (Impl → Prop)) where
  witness  : Impl
  all_hold : ∀ S, S ∈ Specs → S witness

theorem JointSatisfiableSpec.no_pairwise_contradiction {Impl : Type}
    {Specs : List (Impl → Prop)}
    (J : JointSatisfiableSpec Impl Specs)
    {S₁ S₂ : Impl → Prop}
    (h₁ : S₁ ∈ Specs) (h₂ : S₂ ∈ Specs) :
    ¬ (∀ impl, S₁ impl → ¬ S₂ impl) :=
  fun hContra => hContra J.witness (J.all_hold S₁ h₁) (J.all_hold S₂ h₂)

end LeanSys.Contracts
