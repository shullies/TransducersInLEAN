import TransducersInLEAN.mealyMachines.listOfMachines
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Submonoid.Basic
import Mathlib.Algebra.Group.WithOne.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Basic
import Mathlib.Order.RelClasses
import Mathlib.Data.Set.Card
import Mathlib.Algebra.Group.Subsemigroup.Basic
import Mathlib.Data.Fintype.Basic

-- lemma prefSemiAux_eq_evalFrom (M : MealyMachine α σ β) (inputs : List α) (acc : MealySubsemigroup M) (q : σ) :
--   (prefSemiAux acc (inputs.map (inputToSemigroupElem M))).map (fun e => (e.val q).1) =
--   MealyMachine.evalFrom (acc.val q).2 M inputs := by
--   induction inputs generalizing acc q with
--   | nil => rfl
--   | cons x xs ih =>
--     dsimp [prefSemiAux, List.map, MealyMachine.evalFrom, inputToSemigroupElem, inputToTrans]
--     rw [ih (acc * inputToSemigroupElem M x)]
--     rfl

-- theorem prefSemi_eq_evalFrom (M : MealyMachine α σ β) (q : σ) (inputs : List α) :
--   (prefSemi (inputs.map (inputToSemigroupElem M))).map (fun e => (e.val q).1) =
--   MealyMachine.evalFrom q M inputs := by
--   cases inputs with
--   | nil => rfl
--   | cons x xs =>
--     dsimp [prefSemi, List.map, MealyMachine.evalFrom, inputToSemigroupElem, inputToTrans]
--     rw [prefSemiAux_eq_evalFrom]
--     rfl

open MealyMachine

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


instance fintypeGen (M : Type) (G : Set M) [Monoid M] [Fintype M] : Fintype (Submonoid.closure G) := sorry

instance fintypeGenS (M : Type) (G : Set M) [Semigroup M] [Fintype M] : Fintype (Subsemigroup.closure G) := sorry

instance fintypeSubset (M : Type) (G : Set M) [Fintype M] : Fintype G := sorry

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


def one_out_machine {M} [Monoid M] [Fintype M] : MealyMachine M Unit M :=
{ start := (),
  step := fun _state _input => (1, ()) }

theorem one_out_machine_is_prime {M : Type} [Fintype M] [Monoid M] :
  PrimeMachine (one_out_machine (M := M)) := by
  simp [single_State_MM_is_prime]



-- def revMachine {M}
--   [Monoid M] [DecidableEq M] [Fintype M]
--   (G : Set M) [DecidablePred (· ∈ G)] :
--   MealyMachine M (Submonoid.closure G) M :=
-- {
--     step := fun state input =>
--       if h : input = 1 ∨ (input ∈ G)  then
--         have h_next : state.1 * input ∈ Submonoid.closure (G : Set M) := by
--           rcases h with h1 | hG
--           · rw [h1, mul_one]
--             exact state.2
--           · exact Submonoid.mul_mem _ state.2 (Submonoid.subset_closure hG)
--         let nextState : Submonoid.closure (G : Set M) := ⟨state.1 * input, h_next⟩
--         (nextState, nextState)
--       else
--         (state, state)
--     start := ⟨1, Submonoid.one_mem _⟩
-- }

-- theorem f_is_bijective
--     {M : Type*} [Monoid M] [Fintype M]
--     (G : Set M)
--     (h_equalsm :
--       ∀ g ∈ G,
--         (fun x ↦ x * g) '' (Submonoid.closure G : Set M)
--           = (Submonoid.closure G : Set M))
--     (g : M) (hg : g ∈ G) :
--     Function.Bijective
--       (fun (x : Submonoid.closure G) ↦
--         (⟨(x : M) * g, Submonoid.mul_mem (Submonoid.closure G) x.2 (Submonoid.subset_closure hg)⟩ : Submonoid.closure G)) := by
--   rw [← Finite.surjective_iff_bijective]
--   intro y
--   have hy_mem : (y : M) ∈ (Submonoid.closure G : Set M) := y.2
--   have h_surj := h_equalsm g hg
--   have hy_in_image : (y : M) ∈ (fun x ↦ x * g) '' (Submonoid.closure G : Set M) := by
--     rw [h_surj]
--     exact hy_mem
--   rcases hy_in_image with ⟨x_val, hx_mem, hx_eq⟩
--   use ⟨x_val, hx_mem⟩
--   ext
--   exact hx_eq

-- theorem revMachine_is_primeSequential {M} [Monoid M] [DecidableEq M] [Fintype M] (G : Set M)
--   (h_equalsm : ∀ g ∈ G, (fun x ↦ x * g) '' ↑(Submonoid.closure G) = ↑(Submonoid.closure G)):
--   CompositionOfPrimes (revMachine (M:=M) G.toFinset).eval := by
--   rw [CompositionOfPrimes]
--   use ListOfListFunctions.cons (revMachine (M := M) G.toFinset).eval (ListOfListFunctions.nil M)
--   have h_set_eq : ↑G.toFinset = (G : Set M) := Set.ext (by simp)
--   constructor
--   · rw [isListOfPrimeFunction]
--     simp only [ListOfListFunctions.all]
--     constructor
--     · rw [PrimeSequentialFunction]
--       use ((Submonoid.closure (G.toFinset : Set M)))
--       use (revMachine (M := M) G.toFinset)
--       constructor
--       · rw [PrimeMachine]
--         left
--         rw [ReversibleMealyMachine]
--         intro a
--         by_cases h : (a = 1) ∨ (a ∈ G)
--         · rw [revMachine]
--           constructor
--           · intro x y gxisgy
--             simp [nextState,h,revMachine] at gxisgy
--             rcases h with a1|aing
--             · simp [a1,mul_one,mul_one] at gxisgy
--               exact gxisgy
--             · apply f_is_injective
--               simp [h_set_eq]
--               intro x xinG
--               exact h_equalsm x xinG
--               simp
--               exact gxisgy
--               rw [h_set_eq]
--               exact aing
--           · intro x
--             rcases h with h1 | hinG
--             · use x
--               simp [h1,nextState]
--             · rw [← h_set_eq] at h_equalsm
--               rw [← h_set_eq] at hinG
--               obtain h' := (f_is_surjective G.toFinset h_equalsm a hinG)
--               obtain ⟨ b , hb ⟩ := h' x
--               use b
--               simp [nextState]
--               rw [dif_pos]
--               simp [hb]
--               right
--               exact hinG
--         · constructor
--           · intro x y gxisgy
--             simp [nextState,h,revMachine] at gxisgy
--             exact gxisgy
--           · intro a
--             use a
--             simp [nextState,h,revMachine]
--       · trivial
--     · trivial
--   · simp only [ListOfListFunctions.eval]
--     trivial

-- theorem custom_induction
-- {M} {P : Set M → Prop} [Monoid M] [DecidableEq M] [Fintype M]
-- (step : ∀ (G : Set M), (∀ (G' : Set M), ((Submonoid.closure G' : Set M).ncard < (Submonoid.closure G : Set M).ncard) ∨ (((Submonoid.closure G' : Set M).ncard = (Submonoid.closure G : Set M).ncard) ∧ G'.ncard < G.ncard) → P G') → P G )
-- (basecase : P ∅) :
-- ∀ (G : Set M) , P G := by sorry

theorem induction_theorem
{M} {P : Set M → Prop} [Monoid M] [DecidableEq M] [Fintype M]
(step : ∀ (G : Set M), (∀ (G' : Set M), (((Subsemigroup.closure G' : Set M).ncard, G'.ncard) < ((Subsemigroup.closure G : Set M).ncard , G.ncard)) → P G') → P G )
:
∀ (G : Set M) , P G := by
  have wf : WellFounded (fun G' G : Set M =>
      ((((Subsemigroup.closure G' : Set M).ncard, G'.ncard) : ℕ × ℕ)
        < ((Subsemigroup.closure G : Set M).ncard, G.ncard))) :=
    @InvImage.wf (Set M) (ℕ × ℕ) (· < ·)
      (fun G => (((Subsemigroup.closure G : Set M).ncard, G.ncard) : ℕ × ℕ))
      IsWellFounded.wf
  intro G
  induction G using wf.induction with
  | _ G ih => exact step G ih


-- lemma CorrectPrefSubG_ConstructableAux {M : Type} [Monoid M] [DecidableEq M] [Fintype M] ( G : Set M ) (m n : Nat)
--   (hn : Fintype.card ↥(Submonoid.closure G) ≤ n) (hm : Fintype.card ↥G ≤ m) :
--   ∃ (f : List M → List M), CorrectPrefSubG G f ∧ CompositionOfPrimes f := by
--   induction n generalizing G m with
--   |zero =>
--   absurd hn
--   push Not
--   have : 1 ∈ Submonoid.closure G := by
--     exact (Submonoid.closure G).one_mem
--   have h : (Submonoid.closure G : Set M).Nonempty :=
--     ⟨1, this⟩
--   exact Fintype.card_pos (α := Submonoid.closure G)
--   |succ n ih' =>
--   induction m generalizing G with
--     |zero =>
--     rw [Nat.le_zero, Fintype.card_eq_zero_iff] at hm
--     use unitMachine.eval
--     constructor
--     · rw [CorrectPrefSubG]
--       intro l lis1
--       have h : ∀ x ∈ l , x = 1 := by
--         intro x xinl
--         cases lis1 x xinl with
--         | inl xis1 =>
--         exact xis1
--         | inr xinG =>
--           have : G.Nonempty := ⟨x, xinG⟩
--           absurd hm
--           push Not
--           exact (Set.nonempty_coe_sort (s := G)).mpr this
--       induction l with
--       | nil => trivial
--       | cons head tail ih =>
--       have his1 : head = 1 := by
--         apply h head
--         simp
--       rw [eval,evalFrom,pref,prefAux,his1]
--       simp
--       constructor
--       · trivial
--       · apply ih
--         intro x xinl
--         apply lis1
--         exact List.mem_cons_of_mem head xinl
--         intro x xinl
--         apply h
--         exact List.mem_cons_of_mem head xinl
--     · rw [CompositionOfPrimes]
--       use ListOfListFunctions.cons unitMachine.eval (ListOfListFunctions.nil M)
--       simp only [ListOfListFunctions.eval]
--       constructor
--       · rw [isListOfPrimeFunction,ListOfListFunctions.all]
--         simp only [ListOfListFunctions.all]
--         constructor
--         · apply unitMachine_is_primeSequential
--         · trivial
--       ·trivial
--     | succ m ih =>
--     by_cases h : ∃ g ∈ G, (fun x => x * g) '' (Submonoid.closure G : Set M) ⊂ (Submonoid.closure G : Set M)
--     · sorry
--     · have h_subset : ∀ g ∈ G,  (fun x ↦ x * g) '' ↑(Submonoid.closure G) ⊆ (Submonoid.closure G) := by
--         intro g ginG x
--         simp
--         intro x_1 x_1inG' x_1gx
--         rw [← x_1gx]
--         apply Submonoid.mul_mem
--         exact x_1inG'
--         apply Submonoid.mem_closure_of_mem
--         exact ginG

--       have h_equalsm : ∀ g ∈ G,  (fun x ↦ x * g) '' ↑(Submonoid.closure G) = (Submonoid.closure G) := by
--         intro g ginG
--         rcases Set.eq_or_ssubset_of_subset (h_subset g ginG) with h' | h'
--         · exact h'
--         · push Not at h
--           absurd (h g ginG)
--           exact h'

--       use (revMachine (M := M) G.toFinset).eval
--       constructor
--       · rw [CorrectPrefSubG]
--         intro l xinGor1
--         rw [eval, pref]
--         have hypothesis : ∀ (state : _) ,evalFrom state (revMachine (M := M) G.toFinset) l = prefAux state.val l := by
--           induction l with
--           | nil =>
--           intro state
--           trivial
--           | cons head tail ih =>
--           intro state
--           simp only [evalFrom,prefAux]
--           simp
--           constructor
--           · rw [revMachine]
--             specialize xinGor1 head
--             simp at xinGor1
--             simp [xinGor1]
--           · have : ((revMachine ↑G.toFinset).4 state head).2 = ↑state * head := by
--               rw [revMachine]
--               specialize xinGor1 head
--               simp at xinGor1
--               simp [xinGor1]
--             rw [← this]
--             apply ih
--             intro x xintail
--             simp [xinGor1,xintail]
--         apply hypothesis
--       · apply revMachine_is_primeSequential
--         exact h_equalsm


lemma CorrectPrefSubG_ConstructableAux {M : Type} [Monoid M] [DecidableEq M] [Fintype M] ( G : Set M ) (m n : Nat)
  (hn : Fintype.card ↥(Subsemigroup.closure G) ≤ n) (hm : Fintype.card ↥G ≤ m) :
  ∃ (f : List M → List M), CorrectPrefSubG G f ∧ CompositionOfPrimes f := by
  induction n generalizing G m with
  |zero =>
  have h : Fintype.card ↥(Subsemigroup.closure G) = 0 := Nat.eq_zero_of_le_zero hn
  have hempty : IsEmpty ↥(Subsemigroup.closure G) :=  Fintype.card_eq_zero_iff.mp h
  have gempty : IsEmpty G := ⟨fun g =>
    hempty.false ⟨g, Subsemigroup.subset_closure g.prop⟩⟩
  use one_out_machine.eval
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
        exfalso
        obtain ⟨g, hg⟩ := this
        exact gempty.false ⟨g, hg⟩
    induction l with
    | nil => trivial
    | cons h t ih =>
      simp [one_out_machine,eval,pref,prefAux,h,evalFrom]
      rw [← eval , ← one_out_machine , ← pref]
      apply ih
      intro x xint
      simp [xint,h]
      intro x xint
      simp [xint,h]
  · apply prime_machine_eval_is_composition_of_primes
    apply one_out_machine_is_prime
  |succ n ih' =>
  induction m generalizing G with
    | zero =>
    rw [Nat.le_zero, Fintype.card_eq_zero_iff] at hm
    use one_out_machine.eval
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
      | cons h t ih =>
        simp [one_out_machine,eval,pref,prefAux,h,evalFrom]
        rw [← eval , ← one_out_machine , ← pref]
        apply ih
        intro x xint
        simp [xint,h]
        intro x xint
        simp [xint,h]
    · apply prime_machine_eval_is_composition_of_primes
      apply one_out_machine_is_prime
    | succ m ih =>
    by_cases h : ∃ g ∈ G, (fun x => x * g) '' (Subsemigroup.closure G : Set M) ⊂ (Subsemigroup.closure G : Set M)
    · sorry
    ·
      have h_subset : ∀ g ∈ G,  (fun x ↦ x * g) '' ↑(Subsemigroup.closure G) ⊆ (Subsemigroup.closure G) := by
        intro g ginG x
        simp
        intro x_1 x_1inG' x_1gx
        rw [← x_1gx]
        apply Subsemigroup.mul_mem
        exact x_1inG'
        apply Subsemigroup.mem_closure_of_mem
        exact ginG

      have h_equalsm : ∀ g ∈ G,  (fun x ↦ x * g) '' ↑(Subsemigroup.closure G) = (Subsemigroup.closure G) := by
        intro g ginG
        rcases Set.eq_or_ssubset_of_subset (h_subset g ginG) with h' | h'
        · exact h'
        · push Not at h
          absurd (h g ginG)
          exact h'

      sorry

def prefSemiAux {M} [Semigroup M] (currMul : M) (input_list : List M) : List M :=
match input_list with
| [] => []
| x :: xs =>
  let acc' := currMul * x
  acc' :: prefSemiAux acc' xs

def prefSemi {M} [Semigroup M] : List M → List M
| [] => []
| x :: xs => x :: prefSemiAux x xs

def CorrectPrefSubG_S {M} [Semigroup M]
    (G : Set M) (f : List M → List M) : Prop :=
  ∀ l,
    (∀ x, x ∈ l → x ∈ G) →
    f l = prefSemi l

def TransType (σ β : Type _) : Type _ := σ → β × σ

def inputToTrans (M : MealyMachine α σ β) (a : α) : TransType σ β :=
  fun s => M.step s a

instance (σ β : Type _) : Semigroup (TransType σ β) where
  mul f g := fun s =>
    let (b1, s') := f s
    let (b2, s'') := g s'
    (b2, s'')

  mul_assoc f g h := by
    funext s
    dsimp [Mul.mul]
    rcases f s with ⟨b1, s1⟩
    rcases g s1 with ⟨b2, s2⟩
    rcases h s2 with ⟨b3, s3⟩
    rfl

section Closure
variable {α : Type u} {σ : Type v} {β : Type w}
variable (M : MealyMachine α σ β)

def mealyGenerators : Set (TransType σ β) :=
  Set.range (fun a => inputToTrans M a)

def MealySubsemigroup : Subsemigroup (TransType σ β) :=
  Subsemigroup.closure (mealyGenerators M)

def TransitionClosureSet : Type _ := MealySubsemigroup M

def inputToSemigroupElem (M : MealyMachine α σ β) (a : α) : MealySubsemigroup M :=
  have h : inputToTrans M a ∈ mealyGenerators M := by
    exact Set.mem_range_self a
  ⟨inputToTrans M a, Subsemigroup.subset_closure h⟩

end Closure

lemma TransType.mul_snd (f g : TransType σ β) (s : σ) :
  ((f * g) s).2 = (g (f s).2).2 := by
  rfl

lemma TransType.mul_fst (f g : TransType σ β) (s : σ) :
  ((f * g) s).1 = (g (f s).2).1 := by
  rfl

lemma prefSemiAux_eq_evalFrom (M : MealyMachine α σ β) (inputs : List α)
  (acc : MealySubsemigroup M) (q : σ) :
  (prefSemiAux acc (inputs.map (inputToSemigroupElem M))).map (fun e => (e.val q).1) =
  MealyMachine.evalFrom (acc.val q).2 M inputs := by
  induction inputs generalizing acc with
  | nil =>
  trivial
  | cons h t ih =>
  simp [evalFrom,prefSemiAux]
  constructor
  · simp [inputToSemigroupElem]
    unfold inputToTrans
    simp [TransType.mul_fst]
  · have h1 : (M.4 (acc.val q).2 h).2 = ((acc * inputToSemigroupElem M h).val q).2 := by
      simp [inputToSemigroupElem,inputToTrans,TransType.mul_snd]
    rw [h1]
    unfold List.unattach
    simp only [List.map_map]
    apply ih

lemma prefSemiAux_eq_eval (M : MealyMachine α σ β) (inputs : List α) :
  (prefSemi (inputs.map (inputToSemigroupElem M))).map (fun e => (e.val M.start).1) =
  M.eval inputs := by
  match inputs with
  | [] =>
  trivial
  | h :: t =>
  simp [prefSemi]
  simp [MealyMachine.eval,evalFrom]
  constructor
  · simp [inputToSemigroupElem]
    unfold inputToTrans
    simp [TransType.mul_snd, TransType.mul_fst]
  · unfold List.unattach
    simp only [List.map_map]
    apply prefSemiAux_eq_evalFrom

theorem compositionOfPrimes_sandwich {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    (g1 : A → B) (g2 : B → C) (f' : List B → List B)
    (h : CompositionOfPrimes f') :
    CompositionOfPrimes (fun l => List.map g2 (f' (List.map g1 l))) := by
  obtain ⟨l', hl'⟩ := h
  refine ⟨ListOfListFunctions.cons (List.map g1)
      (ListOfListFunctions.concat l'
        (ListOfListFunctions.cons (List.map g2) (ListOfListFunctions.nil C))), ?_, ?_⟩
  · refine ⟨primeSeq_map g1, ?_⟩
    rw [ListOfListFunctions.concat_all]
    exact ⟨hl'.1, primeSeq_map g2, trivial⟩
  · funext l
    simp only [ListOfListFunctions.eval, Function.comp]
    rw [← ListOfListFunctions.concat_eval]
    simp only [ListOfListFunctions.eval, Function.comp, id, ← hl'.2]

theorem prefAux_map_coe {M} [Semigroup M] (acc : M) (l : List M) :
    prefAux (acc : WithOne M) (List.map WithOne.coe l)
      = List.map WithOne.coe (prefSemiAux acc l) := by
  induction l generalizing acc <;> simp +decide [ *, prefAux, prefSemiAux ];
  rename_i k hk ih; exact ih _;
theorem pref_map_coe {M} [Semigroup M] (l : List M) :
    pref (List.map WithOne.coe l) = List.map WithOne.coe (prefSemi l) := by
  induction' l with x l ih;
  · rfl;
  · convert congr_arg ( fun l => WithOne.coe x :: l ) ( prefAux_map_coe x l ) using 1

instance instFintypeWithOne {M : Type*} [Fintype M] : Fintype (WithOne M) :=
  inferInstanceAs (Fintype (Option M))


lemma CorrectPrefSubG_ConstructableAux_S {M} [Semigroup M] [DecidableEq M] [Fintype M]
    ( G : Set M ) (m n : Nat)
    (hn : Fintype.card (Subsemigroup.closure G) ≤ n) (hm : Fintype.card ↥G ≤ m) :
    ∃ (f : List M → List M), CorrectPrefSubG_S G f ∧ CompositionOfPrimes f := by
  classical
  rcases isEmpty_or_nonempty M with hM | hM
  · -- `M` is empty: the only valid input list is `[]`.
    refine ⟨id, ?_, ⟨ListOfListFunctions.nil M, trivial, rfl⟩⟩
    intro l _
    cases l with
    | nil => rfl
    | cons x xs => exact (IsEmpty.false x).elim
  · -- `M` is nonempty: adjoin a unit and use the monoid construction.
    obtain ⟨d⟩ := hM
    let extract : WithOne M → M := fun x => WithOne.recOneCoe d id x
    let G' : Set (WithOne M) := WithOne.coe '' G
    obtain ⟨f', hcorrect, hcomp⟩ := CorrectPrefSubG_ConstructableAux G'
        _ _ (le_refl _) (le_refl _)
    refine ⟨fun l => List.map extract (f' (List.map WithOne.coe l)), ?_, ?_⟩
    · intro l hl
      have hpred : ∀ x, x ∈ List.map WithOne.coe l → x = 1 ∨ x ∈ G' := by
        intro x hx
        rcases List.mem_map.1 hx with ⟨a, ha, rfl⟩
        exact Or.inr ⟨a, hl a ha, rfl⟩
      have hf := hcorrect (List.map WithOne.coe l) hpred
      show List.map extract (f' (List.map WithOne.coe l)) = prefSemi l
      rw [hf, pref_map_coe, List.map_map]
      have hid : extract ∘ WithOne.coe = id := by funext a; rfl
      rw [hid, List.map_id]
    · exact compositionOfPrimes_sandwich WithOne.coe extract f' hcomp


lemma existsPrimeList_for_MM {α σ β : Type} (M : MealyMachine α σ β) :
    ∃ (l : ListOfListFunctions α β), isListOfPrimeFunction l ∧ l.eval = M.eval := by
  haveI : Fintype α := M.alphaFin
  haveI : Fintype β := M.betaFin
  haveI : Fintype σ := M.statesFin
  haveI : Finite (TransType σ β) := inferInstanceAs (Finite (σ → β × σ))
  haveI : Fintype (TransType σ β) := Fintype.ofFinite _
  haveI : DecidableEq (TransType σ β) := Classical.decEq _
  haveI : Fintype ↥(MealySubsemigroup M) := Fintype.ofFinite _
  haveI : DecidableEq ↥(MealySubsemigroup M) := Subtype.instDecidableEq
  let G : Set ↥(MealySubsemigroup M) := Set.range (inputToSemigroupElem M)
  obtain ⟨f', hcorr, hcomp⟩ :=
    CorrectPrefSubG_ConstructableAux_S G _ _ (Nat.le_refl _) (Nat.le_refl _)
  have hkey : M.eval = (fun l => List.map (fun e : ↥(MealySubsemigroup M) => (e.val M.start).1)
      (f' (List.map (inputToSemigroupElem M) l))) := by
    funext l
    have hmem : ∀ x, x ∈ List.map (inputToSemigroupElem M) l → x ∈ G := by
      intro x hx
      rcases List.mem_map.1 hx with ⟨a, _, rfl⟩
      exact Set.mem_range_self a
    rw [hcorr (List.map (inputToSemigroupElem M) l) hmem]
    exact (prefSemiAux_eq_eval M l).symm
  rw [hkey]
  exact compositionOfPrimes_sandwich (inputToSemigroupElem M)
      (fun e : ↥(MealySubsemigroup M) => (e.val M.start).1) f' hcomp

theorem KrohnRhodesTheorem {α β : Type} (f : List α → List β) :
  sequentialFunction f → ∃ (l : ListOfListFunctions α β), isListOfPrimeFunction l ∧ l.eval = f := by
  intro  s
  unfold sequentialFunction at s
  obtain ⟨ states , M , valuation ⟩ := s
  obtain ⟨ l , pl ⟩ := existsPrimeList_for_MM M
  use l
  rw [← valuation]
  exact pl
--close MealyMachine

