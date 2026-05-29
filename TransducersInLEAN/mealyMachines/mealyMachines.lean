import Mathlib.Computability.Language
import Mathlib.Computability.DFA


universe u v w

structure MealyMachine (α : Type u) (σ : Type v) (β : Type w) where
  [alphaFin : Fintype α]
  [betaFin : Fintype β]
  [statesFin : Fintype σ]
  step : σ → α → β × σ
  start : σ

namespace MealyMachine

def evalFrom { α σ β } ( s : σ )  (m : MealyMachine α σ β) (l : List α) : List β :=
  match l with
  | [] => []
  | List.cons h t =>
    let ( outLetter , stateNew ) := m.step s h
    List.cons outLetter ( evalFrom stateNew m t )


def eval { α σ β } (m : MealyMachine α σ β) (l : List α ) : List β :=
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
  · letI : Fintype statesM := MM.statesFin
    letI : Fintype statesA := A.statesFin
    letI : Fintype α := MM.alphaFin
    refine ⟨?_⟩

    have transitionFunction (startState : statesM × statesA) (letter : α) : statesM × statesA :=
      let ⟨mealyState,automataState⟩ := startState
      let ⟨letter',mealyState'⟩ := MM.step mealyState letter
      let automataState' := A.automata.step automataState letter'
      ⟨mealyState',automataState'⟩

    have startState : statesM × statesA :=
      ⟨MM.start, A.automata.start⟩

    have acceptState : Set (statesM × statesA) :=
      {s| s.2 ∈ A.automata.accept}
    exact {
      step := transitionFunction
      start := startState
      accept := acceptState
    }
  
  · sorry
