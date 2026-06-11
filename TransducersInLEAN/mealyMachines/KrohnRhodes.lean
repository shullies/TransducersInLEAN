import TransducersInLEAN.mealyMachines.primeMachines
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Submonoid.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Basic
import Mathlib.Order.RelClasses



open MealyMachine

universe u

inductive ListOfListFunctions : Type u → Type u → Type (u + 1) where
  | nil (α : Type u) : ListOfListFunctions α α
  | cons {α β γ : Type u} (f : List α → List β) (rest : ListOfListFunctions β γ) : ListOfListFunctions α γ

namespace ListOfListFunctions

def eval {α β} : ListOfListFunctions α β → (List α → List β)
  | nil _ => id
  | cons f rest => eval rest ∘ f

def all {α β : Type u}
    (p : (X : Type u) → (Y : Type u) → (List X → List Y) → Prop) : ListOfListFunctions α β → Prop
  | .nil _ => True
  | @cons α' β' _ f rest => (p α' β' f) ∧ all p rest

end ListOfListFunctions

def isListOfPrimeFunction {α β : Type u} (l : ListOfListFunctions α β) : Prop :=
  l.all (fun α β f => PrimeSequentialFunction f)

def KrohnRhodesTheorem {α β : Type u} (f : List α → List β ) :
  sequentialFunction f → ∃ (l : ListOfListFunctions α β), isListOfPrimeFunction l ∧ l.eval = f := by
  sorry

def prefAux {M} [Monoid M] : M → List M → List M
| _acc, [] => []
| acc, x :: xs =>
  let acc' := acc * x
  acc' :: prefAux acc' xs

def pref [Monoid M] : List M → List M :=
  prefAux 1

def CorrectPrefSubG {M} [Monoid M]
    (G : Set M) (f : List M → List M) : Prop :=
  ∀ l,
    (∀ x, x ∈ l → x = 1 ∨ x ∈ G) →
    f l = pref l

def CompositionOfPrimes {α β} (f : List α →  List β) : Prop :=
  ∃ (l: ListOfListFunctions α β), isListOfPrimeFunction l ∧ l.eval = f

instance fintypeGen (M : Type) (G : Set M) [Monoid M] [Fintype M] : Fintype (Submonoid.closure G) := sorry

instance fintypeSubset (M : Type) (G : Set M)  [Fintype M] : Fintype G := sorry

def unitMachine {M} [Fintype M] : MealyMachine M Unit M :=
{ start := (),
  step := fun state input => (input, state) }

theorem unitMachine_is_primeSequential {M : Type} [Fintype M] :
  PrimeSequentialFunction (unitMachine (M := M)).eval := by
  rw [PrimeSequentialFunction]
  use Unit, (unitMachine (M := M))
  constructor
  · rw [PrimeMachine]
    right
    rw [FlipFlopMachine]
    intro a
    left
    trivial
  · trivial

def revMachine {M}
  [Monoid M] [DecidableEq M] [Fintype M]
  (G : Set M) [DecidablePred (· ∈ G)] :
  MealyMachine M (Submonoid.closure G) M :=
{
    step := fun state input =>
      if h : input = 1 ∨ (input ∈ G)  then
        have h_next : state.1 * input ∈ Submonoid.closure (G : Set M) := by
          rcases h with h1 | hG
          · rw [h1, mul_one]
            exact state.2
          · exact Submonoid.mul_mem _ state.2 (Submonoid.subset_closure hG)
        let nextState : Submonoid.closure (G : Set M) := ⟨state.1 * input, h_next⟩
        (nextState, nextState)
      else
        (state, state)
    start := ⟨1, Submonoid.one_mem _⟩
}

theorem f_is_bijective
    {M : Type*} [Monoid M] [Fintype M]
    (G : Set M)
    (h_equalsm :
      ∀ g ∈ G,
        (fun x ↦ x * g) '' (Submonoid.closure G : Set M)
          = (Submonoid.closure G : Set M))
    (g : M) (hg : g ∈ G) :
    Function.Bijective
      (fun (x : Submonoid.closure G) ↦
        (⟨(x : M) * g, Submonoid.mul_mem (Submonoid.closure G) x.2 (Submonoid.subset_closure hg)⟩ : Submonoid.closure G)) := by
  rw [← Finite.surjective_iff_bijective]
  intro y
  have hy_mem : (y : M) ∈ (Submonoid.closure G : Set M) := y.2
  have h_surj := h_equalsm g hg
  have hy_in_image : (y : M) ∈ (fun x ↦ x * g) '' (Submonoid.closure G : Set M) := by
    rw [h_surj]
    exact hy_mem
  rcases hy_in_image with ⟨x_val, hx_mem, hx_eq⟩
  use ⟨x_val, hx_mem⟩
  ext
  exact hx_eq

theorem f_is_surjective
    {M : Type*} [Monoid M] [Fintype M]
    (G : Set M)
    (h_equalsm :
      ∀ g ∈ G,
        (fun x ↦ x * g) '' (Submonoid.closure G : Set M)
          = (Submonoid.closure G : Set M))
    (g : M) (hg : g ∈ G) :
    Function.Surjective
      (fun (x : Submonoid.closure G) ↦
        (⟨(x : M) * g, Submonoid.mul_mem (Submonoid.closure G) x.2 (Submonoid.subset_closure hg)⟩ : Submonoid.closure G)) := by
  intro y
  have hy_mem : (y : M) ∈ (Submonoid.closure G : Set M) := y.2
  have h_surj := h_equalsm g hg
  have hy_in_image : (y : M) ∈ (fun x ↦ x * g) '' (Submonoid.closure G : Set M) := by
    rw [h_surj]
    exact hy_mem
  rcases hy_in_image with ⟨x_val, hx_mem, hx_eq⟩
  use ⟨x_val, hx_mem⟩
  ext
  exact hx_eq

theorem f_is_injective
    {M : Type*} [Monoid M] [Fintype M]
    (G : Set M)
    (h_equalsm :
      ∀ g ∈ G,
        (fun x ↦ x * g) '' (Submonoid.closure G : Set M)
          = (Submonoid.closure G : Set M))
    (g : M) (hg : g ∈ G) :
    Function.Injective
      (fun (x : Submonoid.closure G) ↦
        (⟨(x : M) * g, Submonoid.mul_mem (Submonoid.closure G) x.2 (Submonoid.subset_closure hg)⟩ : Submonoid.closure G)) := by
  exact (f_is_bijective G h_equalsm g hg).injective


theorem revMachine_is_primeSequential {M} [Monoid M] [DecidableEq M] [Fintype M] (G : Set M)
  (h_equalsm : ∀ g ∈ G, (fun x ↦ x * g) '' ↑(Submonoid.closure G) = ↑(Submonoid.closure G)):
  CompositionOfPrimes (revMachine (M:=M) G.toFinset).eval := by
  rw [CompositionOfPrimes]
  use ListOfListFunctions.cons (revMachine (M := M) G.toFinset).eval (ListOfListFunctions.nil M)
  have h_set_eq : ↑G.toFinset = (G : Set M) := Set.ext (by simp)
  constructor
  · rw [isListOfPrimeFunction]
    simp only [ListOfListFunctions.all]
    constructor
    · rw [PrimeSequentialFunction]
      use ((Submonoid.closure (G.toFinset : Set M)))
      use (revMachine (M := M) G.toFinset)
      constructor
      · rw [PrimeMachine]
        left
        rw [ReversibleMealyMachine]
        intro a
        by_cases h : (a = 1) ∨ (a ∈ G)
        · rw [revMachine]
          constructor
          · intro x y gxisgy
            simp [nextState,h,revMachine] at gxisgy
            rcases h with a1|aing
            · simp [a1,mul_one,mul_one] at gxisgy
              exact gxisgy
            · apply f_is_injective
              simp [h_set_eq]
              intro x xinG
              exact h_equalsm x xinG
              simp
              exact gxisgy
              rw [h_set_eq]
              exact aing
          · intro x
            rcases h with h1 | hinG
            · use x
              simp [h1,nextState]
            · rw [← h_set_eq] at h_equalsm
              rw [← h_set_eq] at hinG
              obtain h' := (f_is_surjective G.toFinset h_equalsm a hinG)
              obtain ⟨ b , hb ⟩ := h' x
              use b
              simp [nextState]
              rw [dif_pos]
              simp [hb]
              right
              exact hinG
        · constructor
          · intro x y gxisgy
            simp [nextState,h,revMachine] at gxisgy
            exact gxisgy
          · intro a
            use a
            simp [nextState,h,revMachine]
      · trivial
    · trivial
  · simp only [ListOfListFunctions.eval]
    trivial




lemma CorrectPrefSubG_ConstructableAux {M} [Monoid M] [DecidableEq M] [Fintype M] ( G : Set M ) (m n : Nat)
  (hn : Fintype.card ↥(Submonoid.closure G) ≤ n) (hm : Fintype.card ↥G ≤ m) :
  ∃ (f : List M → List M), CorrectPrefSubG G f ∧ CompositionOfPrimes f := by
  induction n with
  |zero =>
  absurd hn
  push Not
  have : 1 ∈ Submonoid.closure G := by
    exact (Submonoid.closure G).one_mem
  have h : (Submonoid.closure G : Set M).Nonempty :=
    ⟨1, this⟩
  exact Fintype.card_pos (α := Submonoid.closure G)
  |succ n =>
  induction m with
    |zero =>
    rw [Nat.le_zero, Fintype.card_eq_zero_iff] at hm
    use unitMachine.eval
    constructor
    · rw [CorrectPrefSubG]
      intro l lis1
      have h : ∀ x ∈ l , x = 1 := by
        intro x xinl
        cases lis1 x xinl with
        | inl xis1 =>
        exact xis1
        | inr xinG =>
          have : G.Nonempty := ⟨x, xinG⟩
          absurd hm
          push Not
          exact (Set.nonempty_coe_sort (s := G)).mpr this
      induction l with
      | nil => trivial
      | cons head tail ih =>
      have his1 : head = 1 := by
        apply h head
        simp
      rw [eval,evalFrom,pref,prefAux,his1]
      simp
      constructor
      · trivial
      · apply ih
        intro x xinl
        apply lis1
        exact List.mem_cons_of_mem head xinl
        intro x xinl
        apply h
        exact List.mem_cons_of_mem head xinl
    · rw [CompositionOfPrimes]
      use ListOfListFunctions.cons unitMachine.eval (ListOfListFunctions.nil M)
      simp only [ListOfListFunctions.eval]
      constructor
      · rw [isListOfPrimeFunction,ListOfListFunctions.all]
        simp only [ListOfListFunctions.all]
        constructor
        · apply unitMachine_is_primeSequential
        · trivial
      ·trivial
    | succ m =>
    by_cases h : ∃ g ∈ G, (fun x => x * g) '' (Submonoid.closure G : Set M) ⊂ (Submonoid.closure G : Set M)
    · sorry
    · have h_subset : ∀ g ∈ G,  (fun x ↦ x * g) '' ↑(Submonoid.closure G) ⊆ (Submonoid.closure G) := by
        intro g ginG x
        simp
        intro x_1 x_1inG' x_1gx
        rw [← x_1gx]
        apply Submonoid.mul_mem
        exact x_1inG'
        apply Submonoid.mem_closure_of_mem
        exact ginG

      have h_equalsm : ∀ g ∈ G,  (fun x ↦ x * g) '' ↑(Submonoid.closure G) = (Submonoid.closure G) := by
        intro g ginG
        rcases Set.eq_or_ssubset_of_subset (h_subset g ginG) with h' | h'
        · exact h'
        · push Not at h
          absurd (h g ginG)
          exact h'

      use (revMachine (M := M) G.toFinset).eval
      constructor
      · rw [CorrectPrefSubG]
        intro l xinGor1
        rw [eval, pref]
        have hypothesis : ∀ (state : _) ,evalFrom state (revMachine (M := M) G.toFinset) l = prefAux state.val l := by
          induction l with
          | nil =>
          intro state
          trivial
          | cons head tail ih =>
          intro state
          simp only [evalFrom,prefAux]
          simp
          constructor
          · rw [revMachine]
            specialize xinGor1 head
            simp at xinGor1
            simp [xinGor1]
          · have : ((revMachine ↑G.toFinset).4 state head).2 = ↑state * head := by
              rw [revMachine]
              specialize xinGor1 head
              simp at xinGor1
              simp [xinGor1]
            rw [← this]
            apply ih
            intro x xintail
            simp [xinGor1,xintail]
        apply hypothesis
      · apply revMachine_is_primeSequential
        exact h_equalsm




--close MealyMachine
