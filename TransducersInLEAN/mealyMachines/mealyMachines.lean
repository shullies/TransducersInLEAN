import Mathlib.Computability.Language
import Mathlib.Computability.DFA

#check List.reverseRecOn
#check DFA.evalFrom

universe u v w

structure MealyMachine (α : Type u) (σ : Type v) (β : Type w) where
  [alphaFin : Fintype α]
  [betaFin : Fintype β]
  [statesFin : Fintype σ]
  step : σ → α → β × σ
  start : σ

namespace MealyMachine

def evalFrom {α σ β} (s : σ) (m : MealyMachine α σ β) (l : List α) : List β :=
  match l with
  | [] => []
  | List.cons h t =>
    let ( outLetter , stateNew ) := m.step s h
    List.cons outLetter ( evalFrom stateNew m t )

def evalstate {α σ β} (s : σ) (m : MealyMachine α σ β) (l : List α) : σ :=
  match l with
  | [] => s
  | List.cons h t =>
    let ( _outLetter , stateNew ) := m.step s h
    evalstate stateNew m t

def eval {α σ β} (m : MealyMachine α σ β) (l : List α) : List β :=
  evalFrom m.start m l

structure finiteDFA (α β) where
  [alphaFin : Fintype α]
  [statesFin : Fintype β]
  automata : DFA α β

def regularLanguage {α} (l : Language α) : Prop :=
  ∃ (states : Type), ∃ (dfa : finiteDFA α states) ,  dfa.automata.accepts = l

def sequentialFunction {α β} (f : List α → List β) : Prop :=
  ∃ (states : Type), ∃ (mealymachine : MealyMachine α states β) , mealymachine.eval = f

def regularContinuous {α β} (f : List α → List β) : Prop :=
  ∀ (l : Language β), regularLanguage l → regularLanguage (f⁻¹'l)


def MealyComposeAutomata {α β statesM statesA} (MM : MealyMachine α statesM β) (dfa : DFA β statesA) :
  DFA α (statesM × statesA) :=
  have transitionFunction (startState : statesM × statesA) (letter : α) : statesM × statesA :=
    let ⟨mealyState,automataState⟩ := startState
    let ⟨letter',mealyState'⟩ := MM.step mealyState letter
    let automataState' := dfa.step automataState letter'
    ⟨mealyState',automataState'⟩
  have startState : statesM × statesA :=
    ⟨MM.start, dfa.start⟩
  have acceptState : Set (statesM × statesA) :=
    {s| s.2 ∈ dfa.accept}
  {
    step := transitionFunction
    start := startState
    accept := acceptState
  }

def MealyComposeFiniteAutomata {α β statesM statesA} (MM : MealyMachine α statesM β)
(dfa : finiteDFA β statesA) : finiteDFA α (statesM × statesA) :=
  letI : Fintype statesM := MM.statesFin
  letI : Fintype statesA := dfa.statesFin
  letI : Fintype α := MM.alphaFin
  { automata := MealyComposeAutomata MM dfa.automata}

theorem MCFA_state_transition {α β statesM statesA} (MM : MealyMachine α statesM β)
(dfa : finiteDFA β statesA) (word : List α) :
  ∀ (s : statesM × statesA), (MealyComposeFiniteAutomata MM dfa).automata.evalFrom s word =
  ⟨ MM.evalstate s.1  word, dfa.automata.evalFrom s.2 (MM.evalFrom s.1 word) ⟩ := by
    rw [MealyComposeFiniteAutomata,MealyComposeAutomata]
    dsimp
    induction word with
    | nil =>
    intro s
    rw [evalstate]
    simp only [DFA.evalFrom,evalFrom,List.foldl]
    | cons head tail ih =>
    intro s
    simp only [DFA.evalFrom,evalFrom,evalstate]
    simp only [DFA.evalFrom] at ih
    rw [List.foldl]
    dsimp
    rw [ih ((MM.4 s.1 head).2, dfa.automata.step s.2 (MM.4 s.1 head).1)]

theorem MCFA_state_transition_eq {α β statesM statesA} (MM : MealyMachine α statesM β)
(dfa : finiteDFA β statesA) (word : List α) (s : statesM × statesA) :
(MealyComposeFiniteAutomata MM dfa).automata.evalFrom s word =
⟨ MM.evalstate s.1  word, dfa.automata.evalFrom s.2 (MM.evalFrom s.1 word) ⟩ := by
  apply MCFA_state_transition


theorem sequential_implies_continuous {α β} (f : List α → List β) :
  sequentialFunction f → regularContinuous f := by
  intro seq
  simp only [regularContinuous]
  simp only [sequentialFunction] at seq
  obtain ⟨statesM , MM , MMeqf⟩ := seq
  intro l regl
  simp only [regularLanguage]
  simp only [regularLanguage] at regl
  obtain ⟨ statesA , A , Aeql ⟩ := regl
  use statesM × statesA
  /- -/
  refine ⟨?_, ?_⟩
  · exact MealyComposeFiniteAutomata MM A
  · ext word
    constructor
    · intro MCFAaccept
      change f (word) ∈ l
      simp only [DFA.accepts,DFA.acceptsFrom] at MCFAaccept
      set M := (MM.MealyComposeFiniteAutomata A).automata with hM
      change M.evalFrom M.start word ∈ M.accept at MCFAaccept
      rw [MCFA_state_transition_eq MM A word M.start] at MCFAaccept
      change A.automata.evalFrom A.automata.start (MM.eval word) ∈ A.automata.accept at MCFAaccept
      rw [MMeqf] at MCFAaccept
      rw [← Aeql]
      exact MCFAaccept
    /- -/
    · intro fpreimage
      change (MealyComposeFiniteAutomata MM A).automata.accepts word
      change f (word) ∈ l at fpreimage
      rw [← Aeql] at fpreimage
      simp only [DFA.accepts,DFA.acceptsFrom]
      set M := (MM.MealyComposeFiniteAutomata A).automata with hM
      change M.evalFrom M.start word ∈ M.accept
      rw [MCFA_state_transition_eq MM A word M.start]
      change A.automata.evalFrom A.automata.start (MM.eval word) ∈ A.automata.accept
      rw [MMeqf]
      exact fpreimage

def MealyComposeMealyMachine {α β γ statesM₁ statesM₂} (MM₁ : MealyMachine α statesM₁ β)
 (MM₂ : MealyMachine β statesM₂ γ) : MealyMachine α (statesM₁ × statesM₂) γ :=
  letI : Fintype statesM₁ := MM₁.statesFin
  letI : Fintype statesM₂ := MM₂.statesFin
  letI : Fintype α := MM₁.alphaFin
  letI : Fintype γ := MM₂.betaFin
  let startState : statesM₁ × statesM₂ := (MM₁.start, MM₂.start)
  have transitionFunction (startState : statesM₁ × statesM₂) (letter : α)
  : γ × (statesM₁ × statesM₂) :=
    let ⟨mealyState₁,mealyState₂⟩ := startState
    let ⟨letter',mealyState₁'⟩ := MM₁.step mealyState₁ letter
    let ⟨letter'',mealyState₂'⟩ := MM₂.step mealyState₂ letter'
    ⟨letter'' , ⟨mealyState₁', mealyState₂'⟩⟩
  {
    step := transitionFunction
    start := startState
  }

theorem MCMM_evalFrom {α β γ statesM₁ statesM₂} (MM₁ : MealyMachine α statesM₁ β)
 (MM₂ : MealyMachine β statesM₂ γ) (word : List α) :
  ∀ (s : statesM₁ × statesM₂), (MealyComposeMealyMachine MM₁ MM₂).evalFrom s word =
  MM₂.evalFrom s.2 (MM₁.evalFrom s.1 word) := by
    rw [MealyComposeMealyMachine]
    dsimp
    induction word with
    | nil =>
    intro s
    simp only [evalFrom]
    | cons head tail ih =>
    intro s
    simp only [evalFrom]
    rw [ih ((MM₁.4 s.1 head).2, (MM₂.4 s.2 (MM₁.4 s.1 head).1).2)]

theorem MCMM_evalFrom_eq {α β γ statesM₁ statesM₂} (MM₁ : MealyMachine α statesM₁ β)
 (MM₂ : MealyMachine β statesM₂ γ) (word : List α) (s : statesM₁ × statesM₂) :
(MealyComposeMealyMachine MM₁ MM₂).evalFrom s word =
  MM₂.evalFrom s.2 (MM₁.evalFrom s.1 word) := by
  apply MCMM_evalFrom

theorem composition_of_sequential_is_sequential {α β γ} (f : List α → List β) (g : List β → List γ) :
  sequentialFunction f → sequentialFunction g → sequentialFunction (g ∘ f) := by
  intro seqf seqg
  simp only [sequentialFunction] at seqf seqg
  obtain ⟨statesM₁ , MM₁ , MM₁eqf⟩ := seqf
  obtain ⟨statesM₂ , MM₂ , MM₂eqg⟩ := seqg
  use statesM₁ × statesM₂
  refine ⟨?_, ?_⟩
  · exact MealyComposeMealyMachine  MM₁ MM₂
  · set M := MealyComposeMealyMachine  MM₁ MM₂ with hM
    change M.evalFrom M.start = (g ∘ f)
    ext word i output
    constructor
    · intro comp
      rw [MCMM_evalFrom_eq MM₁ MM₂ word M.start] at comp
      have : MM₂.evalFrom M.start.2 (MM₁.evalFrom M.start.1 word) = g (f word) := by
        rw [← MM₁eqf]
        rw [← MM₂eqg]
        rfl
      rw [this] at comp
      exact comp
    · intro comp
      rw [MCMM_evalFrom_eq MM₁ MM₂ word M.start]
      have : MM₂.evalFrom M.start.2 (MM₁.evalFrom M.start.1 word) = g (f word) := by
        rw [← MM₁eqf]
        rw [← MM₂eqg]
        rfl
      rw [this]
      exact comp

end MealyMachine

open Sum

def mapCaux {α β : Type*} (currList : List α)
    (f : List α → List β)
    (input : List (α ⊕ Unit)) : List (β ⊕ Unit) :=
  match input with
  | [] => (f currList).map inl
  | h :: t =>
    match h with
    | inr () => (f currList).map inl ++ [inr ()] ++ mapCaux [] f t
    | inl a  => mapCaux (currList ++ [a]) f t

def mapC {α β : Type*}
    (f : List α → List β) :
    List (α ⊕ Unit) → List (β ⊕ Unit) :=
  mapCaux [] f

lemma mapCaux_opens {α β : Type*}
    (f : List α → List β)
    (held : List α)
    (l : List α)
    (t : List (α ⊕ Unit)) :
  mapCaux held f (l.map inl ++ [inr ()] ++ t) =
    (f (held ++ l)).map inl ++ [inr ()] ++ mapC f t := by
  induction l generalizing held with
  | nil =>
    dsimp [mapCaux, mapC]
    simp
  | cons head tail ih =>
    change
      mapCaux (held ++ [head]) f (tail.map inl ++ [inr ()] ++ t) = _
    rw [ih (held ++ [head])]
    simp

lemma mapCaux_pure_inl {α β : Type*}
    (currList : List α)
    (f : List α → List β)
    (L : List α) :
    mapCaux currList f (L.map inl) =
      (f (currList ++ L)).map inl := by
  induction L generalizing currList with
  | nil =>
    simp [mapCaux]
  | cons h t ih =>
    simp [mapCaux]
    rw [ih (currList ++ [h])]
    simp

lemma mapC_no_restart {α β : Type*}
    (f : List α → List β)
    (l : List α) :
    mapC f (l.map inl) = (f l).map inl := by
  dsimp [mapC]
  rw [mapCaux_pure_inl [] f l]
  simp

lemma distribution_of_mapCaux
    {α β γ : Type*}
    (f : List β → List γ)
    (g : List α → List β)
    (held : List α) :
  mapCaux held (f ∘ g) =
    (mapC f) ∘ (mapCaux held g) := by
  apply funext
  intro input
  induction input generalizing held with
  | nil =>
      simp only [mapCaux, Function.comp_apply]
      rw [← mapC_no_restart]
  | cons h t ih =>
      cases h with
      | inl a =>
          simp only [mapCaux, Function.comp_apply]
          apply ih
      | inr u =>
          simp only [mapC, mapCaux, Function.comp_apply]
          rw [mapCaux_opens]
          simp
          apply ih

theorem distribution_of_map
    {α β γ : Type*}
    (f : List β → List γ)
    (g : List α → List β) :
  mapC (f ∘ g) = mapC f ∘ mapC g := by
  nth_rw 1 [mapC]
  nth_rw 2 [mapC]
  apply distribution_of_mapCaux

