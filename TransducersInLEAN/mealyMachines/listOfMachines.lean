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
  | cons {α β γ : Type u} (f : List α → List β) (rest : ListOfListFunctions β γ) :
  ListOfListFunctions α γ

namespace ListOfListFunctions

def eval {α β} : ListOfListFunctions α β → (List α → List β)
  | nil _ => id
  | cons f rest => eval rest ∘ f

def all {α β : Type u}
    (p : (X : Type u) → (Y : Type u) → (List X → List Y) → Prop) : ListOfListFunctions α β → Prop
  | .nil _ => True
  | @cons α' β' _ f rest => (p α' β' f) ∧ all p rest

def concat {α β γ}
    (l1 : ListOfListFunctions α β)
    (l2 : ListOfListFunctions β γ) :
    ListOfListFunctions α γ :=
  match l1 with
  | ListOfListFunctions.nil _ =>
      l2
  | ListOfListFunctions.cons f rest =>
      ListOfListFunctions.cons f (concat rest l2)

theorem concat_eval {α β γ}
    (l1 : ListOfListFunctions α β)
    (l2 : ListOfListFunctions β γ) :
    l2.eval ∘ l1.eval = (concat l1 l2).eval := by
  induction l1 with
  | nil =>
      rfl
  | @cons α β δ f rest ih =>
    simp only [ListOfListFunctions.eval, concat]
    change (l2.eval ∘ rest.eval) ∘ f = (concat rest l2).eval ∘ f
    rw [ih l2]

theorem concat_all {α β γ}
    (p : (X : Type u) → (Y : Type u) → (List X → List Y) → Prop)
    (l1 : ListOfListFunctions α β)
    (l2 : ListOfListFunctions β γ) :
    all p (concat l1 l2) ↔ all p l1 ∧ all p l2 := by
  induction l1 with
  | nil =>
    simp [concat, all]
  | @cons α β δ f rest ih =>
    simp only [concat, all, ih, and_assoc]

end ListOfListFunctions

def isListOfPrimeFunction {α β : Type u} (l : ListOfListFunctions α β) : Prop :=
  l.all (fun _α _β f => PrimeSequentialFunction f)

def CompositionOfPrimes {α β} (f : List α → List β) : Prop :=
  ∃ (l: ListOfListFunctions α β), isListOfPrimeFunction l ∧ l.eval = f
