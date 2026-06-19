import TransducersInLEAN.mealyMachines.listOfMachines
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Data.List.OfFn

open MealyMachine

def s0 {α σ β} (MM : MealyMachine α σ β) (word : List (α ⊕ Unit)) (i : Fin word.length) : α ⊕ Unit  :=
  word[i]

noncomputable def s1 {α σ β} (MM : MealyMachine α σ β) (h : ReversibleMealyMachine MM) (word : List (α ⊕ Unit)) (i : Fin word.length) : Equiv.Perm σ :=
  match word[i] with
  | .inl a => Equiv.ofBijective (nextState MM a) (h a)
  | .inr () => 1

def prefixProduct {k : ℕ} [Mul S] [One S] (f : Fin k → S) (i : ℕ) (hi : i < k) :=
  match i with
  | .zero => f ⟨0, by omega⟩
  | .succ x =>  f ⟨x.succ, hi⟩ * prefixProduct f x (by omega)

noncomputable def s2 {α σ β} (MM : MealyMachine α σ β) (h : ReversibleMealyMachine MM) (word : List (α ⊕ Unit)) (i : Fin word.length) : Equiv.Perm σ :=
  prefixProduct (s1 MM h word) i (by omega)

def prevUnit (word : List (α ⊕ Unit)) (i : ℕ) (hi : i < word.length) : Option (Fin word.length) :=
  match word[i] with
  | .inr () => some ⟨i, hi⟩
  | _ =>
    match i with
    | .zero => none
    | .succ x => prevUnit word x (by omega)

noncomputable def s3 {α σ β} (MM : MealyMachine α σ β) (h : ReversibleMealyMachine MM) (word : List (α ⊕ Unit)) (i : Fin word.length) : Equiv.Perm σ :=
  match (prevUnit word i.1 (by omega)) with
  | none => 1
  | some i => s2 MM h word i

noncomputable def s4 {α σ β} (MM : MealyMachine α σ β) (h : ReversibleMealyMachine MM) (word : List (α ⊕ Unit)) (i : Fin word.length) : Equiv.Perm σ :=
  (s2 MM h word i) * (s3 MM h word i)⁻¹

def infixProduct {k : ℕ} {S : Type*} [Mul S] [One S] (f : Fin k → S) (i : ℕ) (j : ℕ) (hi : i < k) (hj : j < k) : S :=
  if _h : j ≤ i then 1 else
  match j, hj with
  | .zero, _ => 1
  | .succ x, hj' =>  f ⟨x.succ, hj'⟩ * (infixProduct f i x hi (by omega))
termination_by j
decreasing_by omega

noncomputable def s4' {α σ β} (MM : MealyMachine α σ β) (h : ReversibleMealyMachine MM) (word : List (α ⊕ Unit)) (i : Fin word.length) : Equiv.Perm σ :=
  match (prevUnit word i.1 (by omega)) with
  | none => (s2 MM h word i)
  | some i' => infixProduct (s1 MM h word) i'.1 i.1 i'.2 i.2

noncomputable def s5  {α σ β} (MM : MealyMachine α σ β) (h : ReversibleMealyMachine MM) (word : List (α ⊕ Unit)) (i : Fin word.length) : Equiv.Perm σ :=
  if h' : i.val = 0 then 1 else
  s4' MM h word ⟨ i - 1 , by omega ⟩

noncomputable def s6 {α σ β} (MM : MealyMachine α σ β) (h : ReversibleMealyMachine MM) (word : List (α ⊕ Unit)) (i : Fin word.length) : β ⊕ Unit :=
  match (s0 MM word i) with
  | .inl a => Sum.inl (MM.step ((s5 MM h word i) MM.start) a).1
  | .inr () => Sum.inr ()

-- aristotle generated
lemma prevUnit_le {α} (word : List (α ⊕ Unit)) (i : ℕ) (hi : i < word.length) (j : Fin word.length)
    (hj : prevUnit word i hi = some j) : j.1 ≤ i := by
      induction' i with i ih generalizing j;
      · unfold prevUnit at hj;
        cases h : word[0] <;> aesop;
      · unfold prevUnit at hj;
        cases h' : word[i + 1] <;> simp_all +decide;
        · exact Nat.le_succ_of_le ( ih ( Nat.lt_of_succ_lt hi ) );
        · exact hj ▸ Nat.le_refl _

-- aristotle generated
lemma prefixProduct_eq_infix_mul {G : Type*} [Monoid G] {k : ℕ} (f : Fin k → G) (i j : ℕ)
    (hi : i < k) (hj : j < k) (hij : i ≤ j) :
    prefixProduct f j hj = infixProduct f i j hi hj * prefixProduct f i hi := by
      induction' j with j ih generalizing i;
      · unfold prefixProduct infixProduct; aesop;
      · unfold infixProduct;
        split_ifs <;> simp_all +decide;
        · grind +qlia;
        · rw [ mul_assoc, ← ih i hi ( by linarith ) ( by linarith ), ← prefixProduct ]

-- aristotle generated
lemma prefixProduct_mul_inv {G : Type*} [Group G] {k : ℕ} (f : Fin k → G) (i j : ℕ)
    (hi : i < k) (hj : j < k) (hij : i ≤ j) :
    prefixProduct f j hj * (prefixProduct f i hi)⁻¹ = infixProduct f i j hi hj := by
  rw [prefixProduct_eq_infix_mul f i j hi hj hij]
  group

-- aristotle generated
theorem s4_eq_s4' {α σ β} (MM : MealyMachine α σ β) (h : ReversibleMealyMachine MM)
  (word : List (α ⊕ Unit)) (i : Fin word.length) :
    s4 MM h word i = s4' MM h word i := by
  unfold s4 s4' s3
  cases h' : prevUnit word i (by omega) with
  | none =>
      simp +decide
  | some j =>
      dsimp
      exact prefixProduct_mul_inv _ _ _ _ _ (prevUnit_le _ _ _ _ h')

def WordOf {α γ} (word : List (α ⊕ Unit))
    (f : (word : List (α ⊕ Unit)) → Fin word.length → γ) :
    List γ :=
  List.ofFn (fun i => f word i)

theorem s0_eq_word {α σ β : Type*} (MM : MealyMachine α σ β) (word : List (α ⊕ Unit)) :
  WordOf word (s0 MM) = word := by
  rw [WordOf]
  induction word with
  | nil =>
  trivial
  | cons h t ih =>
  rw [List.ofFn_succ]
  simp [s0]

noncomputable def s0_to_s1MM {α σ β : Type*} [DecidableEq σ] (MM : MealyMachine α σ β) (h : ReversibleMealyMachine MM) :
  MealyMachine (α ⊕ Unit) Unit (Equiv.Perm σ) :=
  have : Fintype α := MM.alphaFin
  have : Fintype σ := MM.statesFin

    let stepfn (_s : Unit) (inp : α ⊕ Unit) : (Equiv.Perm σ) × Unit :=
    match inp with
    | .inl a => (Equiv.ofBijective (nextState MM a) (h a), ())
    | .inr _ => (1, ())
  {
    alphaFin := inferInstance
    betaFin := inferInstance
    statesFin := inferInstance
    step := stepfn
    start := ()
  }

theorem s0_to_s1MM_eq {α σ β : Type*} [DecidableEq σ] (MM : MealyMachine α σ β)
  (h : ReversibleMealyMachine MM) (word : List (α ⊕ Unit)) :
  (s0_to_s1MM MM h).eval (WordOf word (s0 MM)) = (WordOf word (s1 MM h)) := by
  rw [ s0_to_s1MM ,WordOf , WordOf , eval]
  dsimp
  induction word with
  | nil =>
  simp [s0,s1,evalFrom]
  | cons x xs ih =>
  rw [List.ofFn_succ , List.ofFn_succ]
  rw [s0,s1]
  dsimp
  match x with
  | .inl a =>
  rw [evalFrom]
  simp
  apply ih
  | .inr a =>
  rw [evalFrom]
  simp
  apply ih

-- aristotle generated
/-
Index-wise characterisation of `evalFrom`: the `i`-th output letter is obtained
by stepping the machine from the state reached after consuming the first `i`
input letters, on the `i`-th input letter.
-/
lemma evalFrom_eq_ofFn {α σ β} (M : MealyMachine α σ β) (s : σ) (L : List α) :
    M.evalFrom s L = List.ofFn (fun i : Fin L.length =>
      (M.step (M.evalstate s (L.take i.1)) (L[i.1])).1) := by
        induction' L with a L ih generalizing s;
        · rfl;
        · simp +decide [ List.ofFn_succ, evalFrom, evalstate ];
          exact ih _

/-- Specialisation of `evalFrom_eq_ofFn` to `eval`. -/
lemma eval_eq_ofFn {α σ β} (M : MealyMachine α σ β) (L : List α) :
    M.eval L = List.ofFn (fun i : Fin L.length =>
      (M.step (M.evalstate M.start (L.take i.1)) (L[i.1])).1) := by
  rw [eval, evalFrom_eq_ofFn]

/-
`evalstate` over a concatenation runs the two pieces in sequence.
-/
lemma evalstate_append {α σ β} (M : MealyMachine α σ β) (s : σ) (l₁ l₂ : List α) :
    M.evalstate s (l₁ ++ l₂) = M.evalstate (M.evalstate s l₁) l₂ := by
      induction' l₁ with a l₁ ih generalizing s <;> simp +decide [ *, evalstate ]

noncomputable def s1_to_s2MM {α σ β : Type*} [DecidableEq σ] (MM : MealyMachine α σ β) (h : ReversibleMealyMachine MM) :
  MealyMachine (Equiv.Perm σ) (Equiv.Perm σ) (Equiv.Perm σ) :=
  have stepfn (state : Equiv.Perm σ) (input : Equiv.Perm σ) :=
  ⟨ input * state  , input * state ⟩
  have : Fintype σ := MM.statesFin
  {
    step := stepfn
    start := 1
  }

-- Aristotle generated
/-
The accumulator machine's state after consuming `L` is the reverse product of `L`
times the initial state.
-/
lemma s1_to_s2MM_evalstate {α σ β : Type*} [DecidableEq σ] (MM : MealyMachine α σ β)
    (h : ReversibleMealyMachine MM) (s : Equiv.Perm σ) (L : List (Equiv.Perm σ)) :
    (s1_to_s2MM MM h).evalstate s L = L.reverse.prod * s := by
      induction' L with a L ih generalizing s;
      · simp +decide [ evalstate ];
      · convert ih ( a * s ) using 1;
        simp +decide [ mul_assoc, List.reverse_cons ]

/-
`prefixProduct f i` is the product of `f 0, …, f i` in reverse order.
-/
lemma prefixProduct_eq_take_reverse_prod {G : Type*} [Monoid G] {k : ℕ} (f : Fin k → G)
    (i : ℕ) (hi : i < k) :
    prefixProduct f i hi = ((List.ofFn f).take (i + 1)).reverse.prod := by
      induction' i with i ih;
      · rcases k with ( _ | _ | k ) <;> simp_all +decide [ List.take ];
        · contradiction;
        · rfl;
        · rfl;
      · simp +decide [ List.take_add_one, ih ( Nat.lt_of_succ_lt hi ), prefixProduct ];
        grind +splitIndPred

-- aristotle filled the proof
theorem s1_to_s2MM_eq {α σ β : Type*} [DecidableEq σ] (MM : MealyMachine α σ β)
  (h : ReversibleMealyMachine MM) (word : List (α ⊕ Unit)) :
  (s1_to_s2MM MM h).eval (WordOf word (s1 MM h)) = (WordOf word (s2 MM h)) := by
    convert eval_eq_ofFn ( s1_to_s2MM MM h ) ( WordOf word ( s1 MM h ) ) using 2;
    refine' List.ext_getElem _ _ <;> simp +decide [ WordOf ];
    intro i hi₁ ; rw [ s1_to_s2MM_evalstate ] ; simp +decide [ s1_to_s2MM ] ;
    rw [ s2, prefixProduct_eq_take_reverse_prod ];
    rw [ List.take_add_one, List.reverse_append, List.prod_append ] ; aesop

noncomputable def s0_s2_to_s3MM  {α σ β : Type*} [DecidableEq σ] (MM : MealyMachine α σ β) (h : ReversibleMealyMachine MM) :
  MealyMachine ((α ⊕ Unit) × (Equiv.Perm σ)) (Equiv.Perm σ) (Equiv.Perm σ) :=
  have : Fintype σ := MM.statesFin
  have : Fintype α := MM.alphaFin
  have stepfn  (state : Equiv.Perm σ) (input : ((α ⊕ Unit) × (Equiv.Perm σ))) :=
  match input.1 with
  | .inr _ => ⟨ input.2 , input.2 ⟩
  | .inl _ => ⟨ state , state ⟩
  {
    step := stepfn
    start := 1
  }

/-
At a non-unit (`inl`) position `i ≥ 1`, `s3` is unchanged from position `i-1`.
-/
lemma s3_inl_succ {α σ β : Type*} (MM : MealyMachine α σ β)
    (h : ReversibleMealyMachine MM) (word : List (α ⊕ Unit)) (i : ℕ)
    (hi : i + 1 < word.length) (a : α) (ha : word[i + 1] = Sum.inl a) :
    s3 MM h word ⟨i + 1, hi⟩ = s3 MM h word ⟨i, by omega⟩ := by
      unfold s3;
      rw [ prevUnit, ha ]

noncomputable def s0_times_s2 {α σ β} (MM : MealyMachine α σ β) (h : ReversibleMealyMachine MM)
    (word : List (α ⊕ Unit)) ( i: Fin word.length) :  (α ⊕ Unit) × Equiv.Perm σ :=
 ⟨s0 MM word i , s2 MM h word i⟩

/-
State of the hold-last machine after consuming the first `i` inputs: it is `1`
if `i = 0`, and otherwise `s3` evaluated at position `i-1`.
-/
lemma s0_s2_to_s3MM_evalstate {α σ β : Type*} [DecidableEq σ] (MM : MealyMachine α σ β)
    (h : ReversibleMealyMachine MM) (word : List (α ⊕ Unit)) (i : ℕ) (hi : i ≤ word.length) :
    (s0_s2_to_s3MM MM h).evalstate 1 ((WordOf word (s0_times_s2 MM h)).take i) =
      if h0 : i = 0 then 1 else s3 MM h word ⟨i - 1, by omega⟩ := by
        induction' i with i ih;
        · rfl;
        · rw [ List.take_add_one ];
          convert congr_arg ( fun x => ( s0_s2_to_s3MM MM h ).step x ( s0_times_s2 MM h word ⟨ i, by omega ⟩ ) |>.2 ) ( ih ( by omega ) ) using 1;
          · rw [ evalstate_append ];
            simp +decide [ WordOf ];
            split_ifs <;> simp_all +decide [ Nat.lt_of_succ_le ];
            rfl;
          · · cases' i with n <;> simp +decide [ s0_s2_to_s3MM, s0_times_s2 ];
              · unfold s3; cases h : word[0] <;> simp_all +decide [ s0, s2 ] ;
                · unfold prevUnit; aesop;
                · unfold prevUnit; aesop;
              · cases h' : word[n + 1] <;> simp +decide [ h', s0, s3 ];
                · rw [ prevUnit ]
                  aesop
                · rw [ prevUnit ] ; aesop

theorem s0_s2_to_s3MM_eq {α σ β : Type*} [DecidableEq σ] (MM : MealyMachine α σ β)
(h : ReversibleMealyMachine MM) (word : List (α ⊕ Unit)) :
  (s0_s2_to_s3MM MM h).eval (WordOf word (s0_times_s2 MM h)) = (WordOf word (s3 MM h)) := by
    refine' List.ext_getElem _ _ <;> simp +decide [ WordOf, eval_eq_ofFn ];
    intro i hi₁;
    convert congr_arg ( fun x => ( s0_s2_to_s3MM MM h ).step x ( s0_times_s2 MM h word ⟨ i, by omega ⟩ ) |>.1 ) ( s0_s2_to_s3MM_evalstate MM h word i ( by omega ) ) using 1;
    unfold s0_s2_to_s3MM s0_times_s2; cases h : word[i] <;> simp_all +decide [ s0, s2 ] ;
    · induction' i with i ih;
      · unfold s3; unfold prevUnit; aesop;
      · exact s3_inl_succ MM _ _ _ _ _ h;
    · unfold s3; unfold prevUnit; aesop;

noncomputable def s2_s3_to_s4MM {α σ β : Type*} [DecidableEq σ] (MM : MealyMachine α σ β) (h : ReversibleMealyMachine MM) :
  MealyMachine ((Equiv.Perm σ) × (Equiv.Perm σ)) Unit (Equiv.Perm σ) :=
  have : Fintype σ := MM.statesFin
  have : Fintype α := MM.alphaFin
  have stepfn  (_state : Unit) (input : ((Equiv.Perm σ) × (Equiv.Perm σ))) :=
    ⟨ input.1 * input.2⁻¹, ()⟩
  {
    step := stepfn
    start := ()
  }

noncomputable def s2_times_s3 {α σ β} (MM : MealyMachine α σ β) (h : ReversibleMealyMachine MM)
  (word : List (α ⊕ Unit)) (i: Fin word.length) :  (Equiv.Perm σ) × (Equiv.Perm σ) :=
 ⟨s2 MM h word i , s3 MM h word i⟩

theorem s2_s3_to_s4MM_eq {α σ β : Type*} [DecidableEq σ] (MM : MealyMachine α σ β)
  (h : ReversibleMealyMachine MM) (word : List (α ⊕ Unit)) :
  (s2_s3_to_s4MM MM h).eval (WordOf word (s2_times_s3 MM h)) = (WordOf word (s4 MM h)) := by
    rw [ eval_eq_ofFn, WordOf, WordOf ];
    unfold s4; aesop;

noncomputable def s4_to_s5MM {α σ β : Type*} [DecidableEq σ] (MM : MealyMachine α σ β):
  MealyMachine (Equiv.Perm σ) (Equiv.Perm σ) (Equiv.Perm σ) :=
  have : Fintype σ := MM.statesFin
  have stepfn (state : Equiv.Perm σ) (input : (Equiv.Perm σ)) :=
  ⟨ state ,input ⟩
  {
    step := stepfn
    start := 1
  }

/-
The delay machine's state after consuming `L` is the last letter of `L`
(or the initial state `s` if `L` is empty).
-/
lemma s4_to_s5MM_evalstate {α σ β : Type*} [DecidableEq σ] (MM : MealyMachine α σ β)
    (s : Equiv.Perm σ) (L : List (Equiv.Perm σ)) :
    (s4_to_s5MM MM).evalstate s L = L.getLastD s := by
      induction' L with a L ih generalizing s;
      · rfl;
      · cases L <;> aesop

theorem s4_to_s5MM_eq {α σ β : Type*} [DecidableEq σ] (MM : MealyMachine α σ β)
  (h : ReversibleMealyMachine MM) (word : List (α ⊕ Unit)) :
  (s4_to_s5MM MM).eval (WordOf word (s4 MM h)) = (WordOf word (s5 MM h)) := by
    convert eval_eq_ofFn ( s4_to_s5MM MM ) ( WordOf word ( s4 MM h ) ) using 2;
    refine' List.ext_getElem _ _ <;> simp +decide [ WordOf, s4_to_s5MM ];
    intro i hi; induction' i with i ih <;> simp_all +decide [ evalstate_append, List.take_add_one ] ;
    · unfold s5; aesop;
    · split_ifs <;> simp_all +decide [ s5, s4_eq_s4' ];
      · unfold evalstate; aesop;
      · grind

noncomputable def s0_s5_to_s6MM {α σ β : Type*} [DecidableEq σ] (MM : MealyMachine α σ β):
  MealyMachine ((α ⊕ Unit) × (Equiv.Perm σ)) Unit (β ⊕ Unit) :=
  have : Fintype σ := MM.statesFin
  have : Fintype α := MM.alphaFin
  have : Fintype β := MM.betaFin
  have stepfn (_state : Unit) (input : (α ⊕ Unit) × (Equiv.Perm σ)) :=
    match input.1 with
    |.inr _a => ⟨ Sum.inr (), ()⟩
    |.inl a => ⟨ Sum.inl (MM.step (input.2 MM.start) a).1, ()⟩
  {
    step := stepfn
    start := ()
  }

noncomputable def s0_times_s5 {α σ β} (MM : MealyMachine α σ β) (h : ReversibleMealyMachine MM)
    (word : List (α ⊕ Unit)) (i: Fin word.length) :  (α ⊕ Unit) × (Equiv.Perm σ) :=
 ⟨s0 MM word i , s5 MM h word i⟩

theorem s0_s5_to_s6MM_eq {α σ β : Type*} [DecidableEq σ] (MM : MealyMachine α σ β)
  (h : ReversibleMealyMachine MM) (word : List (α ⊕ Unit)) :
  (s0_s5_to_s6MM MM).eval (WordOf word (s0_times_s5 MM h)) = (WordOf word (s6 MM h)) := by
    rw [ eval_eq_ofFn, WordOf, WordOf ];
    refine' List.ext_getElem _ _ <;> simp +decide;
    unfold s0_s5_to_s6MM s0_times_s5 s6;
    intro i h₁; rcases h : s0 MM word ⟨ i, h₁ ⟩ with ( _ | _ ) <;> simp +decide ;

lemma eval_length {α σ β} (M : MealyMachine α σ β) (L : List α) :
    (M.eval L).length = L.length := by
  rw [eval_eq_ofFn, List.length_ofFn]

lemma mapCaux_length {α β} (f : List α → List β) (hf : ∀ l, (f l).length = l.length)
    (held : List α) (input : List (α ⊕ Unit)) :
    (mapCaux held f input).length = held.length + input.length := by
  induction input generalizing held with
  | nil => simp [mapCaux, hf]
  | cons x t ih =>
    cases x with
    | inl a =>
      simp only [mapCaux]
      rw [ih (held ++ [a])]
      simp [List.length_append]
      omega
    | inr u =>
      obtain ⟨⟩ := u
      simp only [mapCaux, List.append_assoc, List.length_append, List.length_map,
        List.length_cons, List.length_nil]
      rw [ih []]
      simp [hf]
      omega

/-- `mapC` with a length-preserving `f` is length-preserving. -/
lemma mapC_length {α β} (f : List α → List β) (hf : ∀ l, (f l).length = l.length)
    (word : List (α ⊕ Unit)) :
    (mapC f word).length = word.length := by
  have := mapCaux_length f hf [] word
  simpa [mapC] using this

lemma evalFrom_append {α σ β} (M : MealyMachine α σ β) (s : σ) (l₁ l₂ : List α) :
    M.evalFrom s (l₁ ++ l₂) = M.evalFrom s l₁ ++ M.evalFrom (M.evalstate s l₁) l₂ := by
      induction' l₁ with a l₁ ih generalizing s;
      · rfl;
      · simp_all +decide [ evalFrom, evalstate ]

def simOut {α σ β} (MM : MealyMachine α σ β) (s : σ) : List (α ⊕ Unit) → List (β ⊕ Unit)
  | [] => []
  | Sum.inl a :: t => Sum.inl (MM.step s a).1 :: simOut MM (MM.step s a).2 t
  | Sum.inr () :: t => Sum.inr () :: simOut MM MM.start t

def stateFrom {α σ β} (MM : MealyMachine α σ β) (s : σ) (word : List (α ⊕ Unit)) : ℕ → σ
  | 0 => s
  | (i + 1) =>
    match word[i]? with
    | some (Sum.inl a) => (MM.step (stateFrom MM s word i) a).2
    | some (Sum.inr ()) => MM.start
    | none => stateFrom MM s word i

lemma mapCaux_eq_simOut {α σ β} (MM : MealyMachine α σ β) (held : List α)
    (input : List (α ⊕ Unit)) :
    mapCaux held MM.eval input =
      (MM.eval held).map Sum.inl ++ simOut MM (MM.evalstate MM.start held) input := by
        induction' input with x t ih generalizing held;
        · simp +decide [ mapCaux, simOut ];
        · cases x <;> simp +decide [ mapCaux, simOut ];
          · convert ih ( held ++ [ ‹_› ] ) using 1;
            simp +decide [ eval, evalFrom_append, evalstate_append ];
            simp +decide [ evalFrom, evalstate ];
          · convert ih [] using 1

lemma mapC_eq_simOut {α σ β} (MM : MealyMachine α σ β) (word : List (α ⊕ Unit)) :
    mapC MM.eval word = simOut MM MM.start word := by
      convert mapCaux_eq_simOut MM [] word using 1

lemma stateFrom_cons_inl {α σ β} (MM : MealyMachine α σ β) (s : σ) (a : α)
    (t : List (α ⊕ Unit)) (k : ℕ) :
    stateFrom MM s (Sum.inl a :: t) (k + 1) = stateFrom MM (MM.step s a).2 t k := by
      induction' k with k ih generalizing s <;> simp_all +decide [ stateFrom ]

lemma stateFrom_cons_inr {α σ β} (MM : MealyMachine α σ β) (s : σ)
    (t : List (α ⊕ Unit)) (k : ℕ) :
    stateFrom MM s (Sum.inr () :: t) (k + 1) = stateFrom MM MM.start t k := by
      induction' k with k ih generalizing s <;> simp_all +decide [ stateFrom ]

lemma simOut_eq_ofFn {α σ β} (MM : MealyMachine α σ β) (s : σ) (word : List (α ⊕ Unit)) :
    simOut MM s word = List.ofFn (fun i : Fin word.length =>
      match word[i] with
      | Sum.inl a => Sum.inl (MM.step (stateFrom MM s word i) a).1
      | Sum.inr () => Sum.inr ()) := by
        induction' word with x t ih generalizing s;
        · rfl;
        · rcases x with ( a | u );
          · rw [ List.ofFn_eq_map ];
            rw [ show List.finRange ( List.length ( Sum.inl a :: t ) ) = 0 :: List.map ( fun i : Fin ( List.length t ) => Fin.succ i ) ( List.finRange ( List.length t ) ) from ?_ ];
            · rw [ List.map_cons, List.map_map ];
              convert congr_arg ( fun x => Sum.inl ( MM.step s a ).1 :: x ) ( ih ( MM.step s a ).2 ) using 1;
              congr! 1;
              rw [ List.ofFn_eq_map ];
              congr! 2;
              exact stateFrom_cons_inl MM s a t _ ▸ rfl;
            · simp +decide [ List.finRange_succ ];
          · rw [ List.ofFn_succ, simOut ];
            congr;
            convert ih MM.start using 3;
            congr! 1;
            exact funext fun _ => congr_arg _ ( congr_arg ( fun x => MM.step x _ |>.1 ) ( stateFrom_cons_inr MM s t _ ) )

lemma s4'_zero {α σ β : Type*} (MM : MealyMachine α σ β)
    (h : ReversibleMealyMachine MM) (word : List (α ⊕ Unit)) (h0 : 0 < word.length) :
    s4' MM h word ⟨0, h0⟩ = s1 MM h word ⟨0, h0⟩ := by
      unfold s4';
      unfold prevUnit; cases h : word[0] <;> simp_all +decide [ s1, s2 ] ;
      · unfold prefixProduct s1; aesop;
      · unfold infixProduct; aesop;

lemma s4'_inr {α σ β : Type*} (MM : MealyMachine α σ β)
    (h : ReversibleMealyMachine MM) (word : List (α ⊕ Unit)) (i : ℕ) (hi : i < word.length)
    (u : Unit) (hu : word[i] = Sum.inr u) :
    s4' MM h word ⟨i, hi⟩ = 1 := by
      unfold s4';
      rw [ show prevUnit word i hi = some ⟨ i, hi ⟩ from ?_ ];
      · unfold infixProduct; aesop;
      · induction' i with i ih; all_goals unfold prevUnit; aesop;

lemma s4'_inl_succ {α σ β : Type*} (MM : MealyMachine α σ β)
    (h : ReversibleMealyMachine MM) (word : List (α ⊕ Unit)) (i : ℕ) (hi : i + 1 < word.length)
    (a : α) (ha : word[i + 1] = Sum.inl a) :
    s4' MM h word ⟨i + 1, hi⟩ = s1 MM h word ⟨i + 1, hi⟩ * s4' MM h word ⟨i, by omega⟩ := by
      unfold s4';
      rw [ show prevUnit word ( i + 1 ) ( by omega ) = prevUnit word i ( by omega ) from ?_ ];
      · cases h' : prevUnit word i ( by omega ) <;> simp_all +decide [ s2 ];
        · exact Equiv.coe_inj.mp rfl;
        · rw [ infixProduct ];
          split_ifs <;> simp_all +decide;
          exact absurd ‹_› ( not_lt_of_ge ( prevUnit_le _ _ _ _ h' ) );
      · rw [ prevUnit, ha ]

lemma s1_apply {α σ β : Type*} (MM : MealyMachine α σ β)
    (h : ReversibleMealyMachine MM) (word : List (α ⊕ Unit)) (i : Fin word.length)
    (a : α) (ha : word[i] = Sum.inl a) (s : σ) :
    (s1 MM h word i) s = (MM.step s a).2 := by
      unfold s1; aesop;

lemma s5_eq_stateAt {α σ β : Type*} (MM : MealyMachine α σ β)
    (h : ReversibleMealyMachine MM) (word : List (α ⊕ Unit)) (i : Fin word.length) :
    (s5 MM h word i) MM.start = stateFrom MM MM.start word i.1 := by
      induction' i with i ih;
      induction' i with i ih;
      · unfold s5 stateFrom; aesop;
      · cases h' : word[i] <;> simp_all +decide [ s5 ];
        · rcases i with ( _ | i ) <;> simp_all +decide [ s4'_inl_succ, s1_apply ];
          · convert s1_apply MM h word ⟨ 0, by omega ⟩ _ h' MM.start using 1;
            · rw [ s4'_zero MM h word ( by omega ) ];
            · simp +decide [ stateFrom ];
              rw [ List.getElem?_eq_getElem ];
              rw [ h' ];
              linarith;
          · rw [ ih ( by linarith ) ];
            rw [ show stateFrom MM MM.start word ( i + 2 ) = ( MM.step ( stateFrom MM MM.start word ( i + 1 ) ) ‹_› ).2 from ?_ ];
            rw [ stateFrom ];
            rw [ List.getElem?_eq_getElem ( by linarith ) ] ; aesop;
        · rw [ s4'_inr MM h word i ( by omega ) _ h' ] ; simp +decide [ stateFrom ];
          rw [ List.getElem?_eq_getElem ( by omega ) ] ; aesop

lemma s6_eq_simOut {α σ β : Type*} (MM : MealyMachine α σ β)
    (h : ReversibleMealyMachine MM) (word : List (α ⊕ Unit)) :
    WordOf word (s6 MM h) = simOut MM MM.start word := by
      rw [ simOut_eq_ofFn ];
      convert List.ofFn_congr _ _;
      convert rfl;
      convert congr_arg ( fun s => match word[‹Fin word.length›] with | Sum.inl a => Sum.inl ( MM.step s a ).1 | Sum.inr PUnit.unit => Sum.inr () ) ( s5_eq_stateAt MM h word ‹_› ) using 1;
      rfl

theorem s6_eq_mapCMM {α σ β : Type*} (MM : MealyMachine α σ β) (h : ReversibleMealyMachine MM)
(word : List (α ⊕ Unit)) :
  WordOf word (s6 MM h) = (mapC MM.eval) word := by
  rw [s6_eq_simOut, mapC_eq_simOut]



-- /--
-- TODO: Maybe define a computable variant of Equiv.ofBijective
-- import Mathlib.Data.Fintype.Basic
-- import Mathlib.Logic.Equiv.Basic

-- variable {α : Type*} [Fintype α] [DecidableEq α]

-- A computable equivalence from a bijective function on a finite type.
-- def Equiv.Perm.ofBijectiveComputable (f : α → α) (hf : Function.Bijective f) : Equiv.Perm α where
--   toFun := f

--   -- Computably search for the unique pre-image
--   invFun y := Fintype.choose (fun x => f x = y) (by
--     -- Prove that exactly one such 'x' exists
--     obtain ⟨x, hx⟩ := hf.surjective y
--     exact ExistsUnique.intro x hx (fun x' hx' => hf.injective (hx'.trans hx.symm)))

--   left_inv x := by
--     -- Fintype.choose_spec gives us `f (invFun (f x)) = f x`.
--     -- Injectivity strips the outer `f`s to prove `invFun (f x) = x`.
--     apply hf.injective
--     exact Fintype.choose_spec (fun x' => f x' = f x) _

--   right_inv y := by
--     -- Fintype.choose_spec directly yields `f (invFun y) = y`.
--     exact Fintype.choose_spec (fun x => f x = y) _
-- -/
