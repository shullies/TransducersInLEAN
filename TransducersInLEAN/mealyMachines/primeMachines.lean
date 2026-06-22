import TransducersInLEAN.mealyMachines.mealyMachines

section
open MealyMachine

def nextState {α σ β}
  (MM : MealyMachine α σ β) (a : α) : σ → σ :=
fun s =>
  match MM.step s a with
  | (_, s') => s'

def ReversibleMealyMachine {α σ β}
  (MM : MealyMachine α σ β) : Prop :=
  ∀ a : α,
    Function.Bijective (nextState MM a)

def FlipFlopMachine {α σ β}
  (MM : MealyMachine α σ β) : Prop :=
  ∀ a : α,
    nextState MM a = id ∨
    ∃ s₀ : σ,
      nextState MM a = fun _ => s₀

def PrimeMachine {α σ β}
  (MM : MealyMachine α σ β) : Prop :=
  ReversibleMealyMachine MM ∨ FlipFlopMachine MM

def PrimeSequentialFunction {α β} (f : List α → List β) : Prop :=
  ∃ (states : Type), ∃ (mealymachine : MealyMachine α states β) , PrimeMachine mealymachine ∧ mealymachine.eval = f

def ForwardMachine {α β σ} (γ : Type)
  (MM : MealyMachine α σ β)
  [Fintype γ] :
  MealyMachine (γ × α) σ (γ × β) :=
  letI : Fintype σ := MM.statesFin
  letI : Fintype α := MM.alphaFin
  letI : Fintype β := MM.betaFin
  letI : Fintype (γ × α) := inferInstance
  letI : Fintype (γ × β) := inferInstance
  let stepFunction (s : σ) (input : γ × α) : (γ × β) × σ :=
    let (g, a) := input
    let (b, s') := MM.step s a
    ((g, b), s')
  {
    step := stepFunction,
    start := MM.start,
    alphaFin := inferInstance,
    betaFin := inferInstance,
    statesFin := MM.statesFin
  }

theorem ForwardMachine_evalFrom
  {α β σ} (γ : Type)
  (MM : MealyMachine α σ β)
  [Fintype γ]
  (word : List (γ × α)) :
  ∀ s : σ,
    let (i₁, i₂) := word.unzip
    let (l₁, l₂) := List.unzip ((ForwardMachine γ MM).evalFrom s word)
    l₁ = i₁ ∧ l₂ = MM.evalFrom s i₂ := by
  induction word with
  | nil =>
    intro s
    simp only [evalFrom, List.unzip, List.unzip_nil]
    trivial
  | cons head tail ih =>
    intro s
    simp only [evalFrom, List.unzip]
    simp only [ForwardMachine]
    specialize ih (MM.4 s head.2).2
    simp only [ForwardMachine] at ih
    obtain ⟨ih₁, ih₂⟩ := ih
    constructor
    · rw [ih₁]
    · rw [ih₂]

theorem ForwardMachine_is_prime_if_MM_is_prime {α β σ γ}
(MM : MealyMachine α σ β) [Fintype γ] (hMM : PrimeMachine MM) :
  PrimeMachine (ForwardMachine γ MM) := by
  cases hMM with
    | inl hRev =>
    left
    intro letter
    specialize hRev letter.2
    obtain ⟨hInj,hSur⟩ := hRev
    constructor
    · intro s₁ s₂ h
      apply hInj h
    · intro s₁
      specialize hSur s₁
      obtain ⟨prevState, pSur⟩ := hSur
      use prevState
      use pSur
    | inr hFlip =>
    right
    intro letter
    cases hFlip letter.2 with
      | inl h =>
      left
      apply h
      | inr h =>
      right
      obtain ⟨ state, proof ⟩ := h
      use state
      apply proof
end

theorem single_State_MM_is_prime {α β} (MM : MealyMachine α Unit β) :
  (PrimeMachine MM) := by
  unfold PrimeMachine
  right
  unfold FlipFlopMachine
  intro a
  right
  use ()

def dupMachine α [Fintype α] :
  MealyMachine α Unit (α × α) :=
  have stepfn (_state : Unit) (letter : α ) := ((letter,letter) , ())
  {
    start := ()
    step := stepfn
  }

theorem dupMachine_is_prime {α} [Fintype α] :
  (PrimeMachine (dupMachine α)) := by
  apply single_State_MM_is_prime

theorem dupMachine_eval {α} (word : List α) [Fintype α] :
  (dupMachine α).eval word = List.zip word word := by
  rw [dupMachine]
  induction word with
  | nil => trivial
  | cons h t ih =>
  dsimp
  simp [MealyMachine.eval,MealyMachine.evalFrom]
  rw [← MealyMachine.eval]
  exact ih


noncomputable def type0_homomorphic_mealy_machine {α : Type u} {σ : Type v} {β : Type w}
  (MM : MealyMachine α σ β) : MealyMachine α (Fin (@Fintype.card σ MM.statesFin)) β :=
  -- Use @ to explicitly pass the bundled instance to equivFin
  let e := @Fintype.equivFin σ MM.statesFin
  { alphaFin := MM.alphaFin
    betaFin := MM.betaFin
    statesFin := inferInstance -- Lean natively knows Fin n is finite
    step := fun (s : Fin (@Fintype.card σ MM.statesFin)) (a : α) =>
      let old_s := e.symm s
      let (b, next_s) := MM.step old_s a
      (b, e next_s)
    start := e MM.start }

lemma evalFrom_homomorphic {α : Type u} {σ : Type v} {β : Type w}
  (MM : MealyMachine α σ β) (s : σ) (l : List α) :
  MealyMachine.evalFrom (@Fintype.equivFin σ MM.statesFin s) (type0_homomorphic_mealy_machine MM) l = MealyMachine.evalFrom s MM l := by
  induction l generalizing s with
  | nil =>
    rfl
  | cons h t ih =>
    dsimp [MealyMachine.evalFrom, type0_homomorphic_mealy_machine]
    rw [Equiv.symm_apply_apply]
    rw [← type0_homomorphic_mealy_machine]
    simp [ih]

theorem eval_identical {α : Type u} {σ : Type v} {β : Type w}
  (MM : MealyMachine α σ β) (l : List α) :
  (type0_homomorphic_mealy_machine MM).eval l = MM.eval l := by
  dsimp [MealyMachine.eval, type0_homomorphic_mealy_machine]
  rw [← type0_homomorphic_mealy_machine,evalFrom_homomorphic]

lemma nextState_homomorphic_comp {α σ β} (MM : MealyMachine α σ β) (a : α) :
  nextState (type0_homomorphic_mealy_machine MM) a =
    (@Fintype.equivFin σ MM.statesFin) ∘ (nextState MM a) ∘ (@Fintype.equivFin σ MM.statesFin).symm := by
  ext s
  dsimp [nextState, type0_homomorphic_mealy_machine]

lemma reversible_homomorphic {α σ β} (MM : MealyMachine α σ β)
  (h : ReversibleMealyMachine MM) : ReversibleMealyMachine (type0_homomorphic_mealy_machine MM) := by
  intro a
  rw [nextState_homomorphic_comp]
  exact Function.Bijective.comp (@Fintype.equivFin σ MM.statesFin).bijective
    (Function.Bijective.comp (h a) (Equiv.symm (@Fintype.equivFin σ MM.statesFin)).bijective)

lemma flipflop_homomorphic {α σ β} (MM : MealyMachine α σ β)
  (h : FlipFlopMachine MM) : FlipFlopMachine (type0_homomorphic_mealy_machine MM) := by
  intro a
  rcases h a with h_id | h_const
  · left
    rw [nextState_homomorphic_comp, h_id]
    ext s
    dsimp
    simp only [Equiv.apply_symm_apply (@Fintype.equivFin σ MM.statesFin) s]
  · right
    rcases h_const with ⟨s₀, hs₀⟩
    use (@Fintype.equivFin σ MM.statesFin) s₀
    rw [nextState_homomorphic_comp, hs₀]
    ext s
    dsimp

theorem prime_homomorphic {α σ β} (MM : MealyMachine α σ β)
  (h : PrimeMachine MM) : PrimeMachine (type0_homomorphic_mealy_machine MM) := by
  rcases h with h_rev | h_ff
  · left
    exact reversible_homomorphic MM h_rev
  · right
    exact flipflop_homomorphic MM h_ff

theorem primeSeqeuntial_of_primeMM {α σ β} (MM : MealyMachine α σ β) (h : PrimeMachine MM) :
  PrimeSequentialFunction MM.eval := by
  unfold PrimeSequentialFunction
  use (Fin (@Fintype.card σ MM.statesFin))
  use type0_homomorphic_mealy_machine MM
  constructor
  · apply prime_homomorphic
    exact h
  · funext l
    apply eval_identical

def copy_machine {α σ β : Type} (MM : MealyMachine α σ β) : MealyMachine α σ (α × β) :=
  have _afin := MM.alphaFin
  have _bfin := MM.betaFin
  have _sfin := MM.statesFin
  {
    start := MM.start
    step := fun s letter =>
      let (out, next_state) := MM.step s letter
      ((letter, out), next_state)
  }

lemma nextState_copy_machine_eq {α σ β} (MM : MealyMachine α σ β) (a : α) :
    nextState (copy_machine MM) a = nextState MM a := by
  ext s
  dsimp [nextState, copy_machine]

theorem copy_machine_reversible {α σ β} (MM : MealyMachine α σ β)
    (h : ReversibleMealyMachine MM) : ReversibleMealyMachine (copy_machine MM) := by
  intro a
  rw [nextState_copy_machine_eq]
  exact h a

theorem copy_machine_flipflop {α σ β} (MM : MealyMachine α σ β)
    (h : FlipFlopMachine MM) : FlipFlopMachine (copy_machine MM) := by
  intro a
  rw [nextState_copy_machine_eq]
  exact h a

theorem copy_machine_prime {α σ β} (MM : MealyMachine α σ β)
    (h : PrimeMachine MM) : PrimeMachine (copy_machine MM) := by
  rcases h with hR | hF
  · left
    exact copy_machine_reversible MM hR
  · right
    exact copy_machine_flipflop MM hF
