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
  ∃ (states : Type*), ∃ (mealymachine : MealyMachine α states β) , PrimeMachine mealymachine ∧ mealymachine.eval = f

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
