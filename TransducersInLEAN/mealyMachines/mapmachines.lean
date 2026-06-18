import TransducersInLEAN.mealyMachines.KrohnRhodes
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
  | .succ x =>  prefixProduct f x (by omega) * f ⟨x.succ, hi⟩

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
  (s3 MM h word i)⁻¹ * (s2 MM h word i)

def infixProduct {k : ℕ} {S : Type*} [Mul S] [One S] (f : Fin k → S) (i : ℕ) (j : ℕ) (hi : i < k) (hj : j < k) : S :=
  if _h : j ≤ i then 1 else
  match j, hj with
  | .zero, _ => 1
  | .succ x, hj' => (infixProduct f i x hi (by omega)) * f ⟨x.succ, hj'⟩
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

-- noncomputable def s7 {α σ β} (MM : MealyMachine α σ β) (word : List (α ⊕ Unit)) (i : Fin word.length) :=
--   (mapC MM.eval word)[i]

lemma infixProduct_succ {k : ℕ} {S : Type*} [Mul S] [One S] (f : Fin k → S)
    (i x : ℕ) (hi : i < k) (hsx : x.succ < k) (hix : i ≤ x) :
    infixProduct f i x.succ hi hsx
      = infixProduct f i x hi (by omega) * f ⟨x.succ, hsx⟩ := by
        rw [infixProduct];
        grind

lemma infixProduct_le {k : ℕ} {S : Type*} [Mul S] [One S] (f : Fin k → S)
    (i j : ℕ) (hi : i < k) (hj : j < k) (hji : j ≤ i) :
    infixProduct f i j hi hj = 1 := by
      unfold infixProduct; aesop;

lemma prefixProduct_eq_mul_infixProduct {k : ℕ} {M : Type*} [Monoid M] (f : Fin k → M)
    (i j : ℕ) (hi : i < k) (hj : j < k) (hij : i ≤ j) :
    prefixProduct f j hj = prefixProduct f i hi * infixProduct f i j hi hj := by
      induction' j with j ih generalizing i;
      · unfold prefixProduct infixProduct; aesop;
      · cases hij;
        · unfold infixProduct; aesop;
        · rw [ show prefixProduct f ( j + 1 ) hj = prefixProduct f j ( by linarith ) * f ⟨ j + 1, hj ⟩ from rfl, ih i hi ( by linarith ) ( by assumption ), infixProduct_succ ];
          · rw [ mul_assoc ];
          · assumption

lemma prevUnit_le {α} (word : List (α ⊕ Unit)) (n : ℕ) (hn : n < word.length)
    (j : Fin word.length) (hj : prevUnit word n hn = some j) : j.1 ≤ n := by
      induction' n with n ih generalizing j;
      · unfold prevUnit at hj;
        cases h : word[0] <;> aesop;
      · cases h : word.get ⟨ n + 1, hn ⟩ <;> simp_all +decide [ prevUnit ];
        · exact Nat.le_succ_of_le ( ih ( Nat.lt_of_succ_lt hn ) );
        · aesop


theorem s4_eq_s4' {α σ β} (MM : MealyMachine α σ β) (h : ReversibleMealyMachine MM) (word : List (α ⊕ Unit)) (i : Fin word.length) :
    s4 MM h word i = s4' MM h word i := by
      unfold s4 s4';
      cases h' : prevUnit word i.1 ( by omega ) <;> simp_all +decide only [s3];
      · simp +decide;
      · have := prevUnit_le word i i.2 _ h';
        have := prefixProduct_eq_mul_infixProduct ( s1 MM h word ) ( ↑‹Fin word.length› ) i ( by omega ) ( by omega ) this; simp_all +decide [ s2 ] ;

def WordOf {α γ} (word : List (α ⊕ Unit))
    (f : (word : List (α ⊕ Unit)) → Fin word.length → γ) :
    List γ :=
  List.ofFn (fun i => f word i)

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

noncomputable def s1_to_s2MM {α σ β : Type*} [DecidableEq σ] (MM : MealyMachine α σ β) (h : ReversibleMealyMachine MM) :
  MealyMachine (Equiv.Perm σ) (Equiv.Perm σ) (Equiv.Perm σ) :=
  have stepfn (state : Equiv.Perm σ) (input : Equiv.Perm σ) :=
  ⟨ state * input , state * input ⟩
  have : Fintype σ := MM.statesFin
  {
    step := stepfn
    start := 1
  }

lemma prefixProduct_succ_cons {S : Type*} [Monoid S] {n : ℕ} (g : Fin (n + 1) → S)
    (i : ℕ) (hi : i < n) :
    prefixProduct g (i + 1) (by omega)
      = g 0 * prefixProduct (fun j : Fin n => g j.succ) i hi := by
  induction' i with i ih;
  · rfl;
  · unfold prefixProduct; simp +decide [ ih ( Nat.lt_of_succ_lt hi ) ] ;
    rw [ mul_assoc ]

lemma scan_evalFrom {S : Type*} [Monoid S] (mm : MealyMachine S S S)
    (hstep : ∀ s i, mm.step s i = (s * i, s * i))
    {n : ℕ} (g : Fin n → S) (s : S) :
    evalFrom s mm (List.ofFn g)
      = List.ofFn (fun i : Fin n => s * prefixProduct g i.1 i.2) := by
  induction' n with n ih generalizing s <;> simp_all +decide [ List.ofFn_succ ];
  · rfl;
  · simp_all +decide [ evalFrom, prefixProduct_succ_cons ];
    exact ⟨ by rfl, funext fun i => by rw [ mul_assoc ] ⟩


theorem s1_to_s2MM_eq {α σ β : Type*} [DecidableEq σ] (MM : MealyMachine α σ β)
  (h : ReversibleMealyMachine MM) (word : List (α ⊕ Unit)) :
  (s1_to_s2MM MM h).eval (WordOf word (s1 MM h)) = (WordOf word (s2 MM h)) := by
  have hstep : ∀ (s i : Equiv.Perm σ), (s1_to_s2MM MM h).step s i = (s * i, s * i) :=
    fun s i => rfl
  unfold eval WordOf
  rw [scan_evalFrom (s1_to_s2MM MM h) hstep (s1 MM h word) (s1_to_s2MM MM h).start]
  apply congrArg List.ofFn
  funext i
  show (1 : Equiv.Perm σ) * prefixProduct (s1 MM h word) i.1 i.2 = s2 MM h word i
  rw [one_mul, s2]

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

noncomputable def s0_times_s2 {α σ β} (MM : MealyMachine α σ β) (h : ReversibleMealyMachine MM)
    (word : List (α ⊕ Unit)) ( i: Fin word.length) :  (α ⊕ Unit) × Equiv.Perm σ :=
 ⟨s0 MM word i , s2 MM h word i⟩


theorem s0_s2_to_s3MM_eq {α σ β : Type*} [DecidableEq σ] (MM : MealyMachine α σ β) (h : ReversibleMealyMachine MM) (word : List (α ⊕ Unit)) :
  (s0_s2_to_s3MM MM h).eval (WordOf word (s0_times_s2 MM h)) = (WordOf word (s3 MM h)) := by sorry

noncomputable def s2_s3_to_s4MM {α σ β : Type*} [DecidableEq σ] (MM : MealyMachine α σ β) (h : ReversibleMealyMachine MM) :
  MealyMachine ((Equiv.Perm σ) × (Equiv.Perm σ)) Unit (Equiv.Perm σ) :=
  have : Fintype σ := MM.statesFin
  have : Fintype α := MM.alphaFin
  have stepfn  (_state : Unit) (input : ((Equiv.Perm σ) × (Equiv.Perm σ))) :=
    ⟨ input.2⁻¹ * input.1 , ()⟩
  {
    step := stepfn
    start := ()
  }

noncomputable def s2_times_s3 {α σ β} (MM : MealyMachine α σ β) (h : ReversibleMealyMachine MM)
    (word : List (α ⊕ Unit)) (i: Fin word.length) :  (Equiv.Perm σ) × (Equiv.Perm σ) :=
 ⟨s2 MM h word i , s3 MM h word i⟩

theorem s2_s3_to_s4MM_eq {α σ β : Type*} [DecidableEq σ] (MM : MealyMachine α σ β) (h : ReversibleMealyMachine MM) (word : List (α ⊕ Unit)) :
  (s2_s3_to_s4MM MM h).eval (WordOf word (s2_times_s3 MM h)) = (WordOf word (s4 MM h)) := by sorry

noncomputable def s4_to_s5MM {α σ β : Type*} [DecidableEq σ] (MM : MealyMachine α σ β):
  MealyMachine (Equiv.Perm σ) (Equiv.Perm σ) (Equiv.Perm σ) :=
  have : Fintype σ := MM.statesFin
  have stepfn (state : Equiv.Perm σ) (input : (Equiv.Perm σ)) :=
  ⟨ state ,input ⟩
  {
    step := stepfn
    start := 1
  }

theorem s4_to_s5MM_eq {α σ β : Type*} [DecidableEq σ] (MM : MealyMachine α σ β) (h : ReversibleMealyMachine MM) (word : List (α ⊕ Unit)) :
  (s4_to_s5MM MM).eval (WordOf word (s4 MM h)) = (WordOf word (s5 MM h)) := by sorry

noncomputable def s0_s5_to_s6MM {α σ β : Type*} [DecidableEq σ] (MM : MealyMachine α σ β):
  MealyMachine ((α ⊕ Unit) × (Equiv.Perm σ)) Unit (β ⊕ Unit) :=
  have : Fintype σ := MM.statesFin
  have : Fintype α := MM.alphaFin
  have : Fintype β := MM.betaFin
  have stepfn (_state : Unit) (input : (α ⊕ Unit) × (Equiv.Perm σ)) :=
    match input.1 with
    |.inr a => ⟨ Sum.inr (), ()⟩
    |.inl a => ⟨ Sum.inl (MM.step (input.2 MM.start) a).1, ()⟩
  {
    step := stepfn
    start := ()
  }

noncomputable def s0_times_s5 {α σ β} (MM : MealyMachine α σ β) (h : ReversibleMealyMachine MM)
    (word : List (α ⊕ Unit)) (i: Fin word.length) :  (α ⊕ Unit) × (Equiv.Perm σ) :=
 ⟨s0 MM word i , s3 MM h word i⟩

theorem s0_s5_to_s6MM_eq {α σ β : Type*} [DecidableEq σ] (MM : MealyMachine α σ β) (h : ReversibleMealyMachine MM) (word : List (α ⊕ Unit)) :
  (s0_s5_to_s6MM MM).eval (WordOf word (s0_times_s5 MM h)) = (WordOf word (s6 MM h)) := by sorry

theorem s6_eq_mapCMM {α σ β : Type*} [DecidableEq σ] (MM : MealyMachine α σ β) (h : ReversibleMealyMachine MM) (word : List (α ⊕ Unit)) :
  WordOf word (s6 MM h) = (mapC MM.eval) word := by sorry

/--
TODO: Maybe define a computable variant of Equiv.ofBijective
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Equiv.Basic

variable {α : Type*} [Fintype α] [DecidableEq α]

A computable equivalence from a bijective function on a finite type.
def Equiv.Perm.ofBijectiveComputable (f : α → α) (hf : Function.Bijective f) : Equiv.Perm α where
  toFun := f

  -- Computably search for the unique pre-image
  invFun y := Fintype.choose (fun x => f x = y) (by
    -- Prove that exactly one such 'x' exists
    obtain ⟨x, hx⟩ := hf.surjective y
    exact ExistsUnique.intro x hx (fun x' hx' => hf.injective (hx'.trans hx.symm)))

  left_inv x := by
    -- Fintype.choose_spec gives us `f (invFun (f x)) = f x`.
    -- Injectivity strips the outer `f`s to prove `invFun (f x) = x`.
    apply hf.injective
    exact Fintype.choose_spec (fun x' => f x' = f x) _

  right_inv y := by
    -- Fintype.choose_spec directly yields `f (invFun y) = y`.
    exact Fintype.choose_spec (fun x => f x = y) _
-/
