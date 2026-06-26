import TransducersInLEAN.mealyMachines.mapmachines

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

def WordOf' {α β} (word : List α) (f : (word' : List α) → Fin word'.length → β) : (List β) :=
    List.ofFn (fun i => f word i)

theorem len_WordOf' (word : List α) (f : (word' : List α) → Fin word'.length → β) :
  word.length = (WordOf' word f).length := by
    simp [WordOf']

def closure_lift [Monoid M] [DecidableEq M] [Fintype M] {G : Set M} (f : Fin i → G) :
  Fin i → Submonoid.closure G :=
  fun i => ⟨(f i).1 , Submonoid.subset_closure (f i).2⟩

def s0' {M} [Monoid M] [DecidableEq M] [Fintype M] {G : Set M} (word : List G)
(i : Fin word.length) : G :=
  word[i]

def G_map {M} [Monoid M] [DecidableEq M] [Fintype M] {G : Set M}
  (g : G) (x : G) : (↥(G \ {g.val})) ⊕ Unit :=
  if h_eq : x.val = g.val then
    Sum.inr ()
  else
    Sum.inl ⟨x.val, ⟨x.property, h_eq⟩⟩

def s1' {M} [Monoid M] [DecidableEq M] [Fintype M] (G : Set M) (g : G)
    (word : List G) (i : Fin word.length) : (↥(G \ {g.val})) ⊕ Unit :=
  G_map g word[i]

def s2' {M} [Monoid M] [DecidableEq M] [Fintype M] (G : Set M) (g : G)
    (word : List G) (i : Fin word.length) : (Submonoid.closure G) ⊕ Unit :=
    let x := s1' G g word i
    if h_eq : x = Sum.inr () then
      Sum.inr ()
    else
      let v:=
      match (prevUnit (WordOf' word (s1' G g)) i.1 (by rw [← len_WordOf'] ; exact i.2 ;) ) with
      | none => prefixProduct (closure_lift (s0' word)) i.1 i.2
      | some val => infixProduct (closure_lift (s0' word)) val.1 i.1
        (by rw [len_WordOf' (f := s1' G g)]; exact val.2;) i.2
      Sum.inl v

def s3' {M} [Monoid M] [DecidableEq M] [Fintype M] (G : Set M) (g : G)
    (word : List G) (i : Fin word.length) : (Submonoid.closure G) :=
    match (s2' G g word i) with
    | Sum.inr _ => 1
    | Sum.inl val => val

def s4'' {M} [Monoid M] [DecidableEq M] [Fintype M] (G : Set M) (g : G)
    (word : List G) (i : Fin word.length) : (Submonoid.closure G) :=
    match h : i.val with
    | Nat.zero => 1
    | Nat.succ j => s3' G g word ⟨j , by omega⟩

def InClosureShiftOrOne {M : Type _} [Monoid M] (G : Set M) (g : M) (x : M) : Prop :=
  (∃ s ∈ Submonoid.closure G, x = s * g) ∨ x = 1

def ClosureShiftOrOne {M : Type _} [Monoid M] (G : Set M) (g : M) :=
  { x : M // InClosureShiftOrOne G g x }

namespace ClosureShiftOrOne

variable {M : Type _} [Monoid M] {G : Set M} {g : M}

def ofMul (s : Submonoid.closure G) : ClosureShiftOrOne G g :=
  ⟨s.1 * g, Or.inl ⟨s.1, s.2, rfl⟩⟩

def ofOne : ClosureShiftOrOne G g :=
  ⟨1, Or.inr rfl⟩

end ClosureShiftOrOne

def s5' {M} [Monoid M] [DecidableEq M] [Fintype M] (G : Set M) (g : G)
    (word : List G) (i : Fin word.length) : ClosureShiftOrOne G g.1 :=
    match (s2' G g word i) with
    | Sum.inr _nil => ClosureShiftOrOne.ofMul (s4'' G g word i)
    | Sum.inl _val => ClosureShiftOrOne.ofOne

def s6' {M} [Monoid M] [DecidableEq M] [Fintype M] (G : Set M) (g : G)
    (word : List (G)) (i : Fin word.length) : (Submonoid.closure G) :=
    match (prevUnit (WordOf' word (s1' G g)) i.1 (by rw [← len_WordOf'] ; exact i.2 ;) ) with
    | none => 1
    | some val => prefixProduct (closure_lift (s0' word)) val.1
      (by rw [len_WordOf' (f := s1' G g)]; exact val.2;)

def s7' {M} [Monoid M] [DecidableEq M] [Fintype M] (G : Set M) (_g : G)
    (word : List (G)) (i : Fin word.length) : (Submonoid.closure G) :=
    prefixProduct (closure_lift (s0' word)) i.1 i.2

theorem s0'_to_s1' {M} [Monoid M] [DecidableEq M] [Fintype M] {G : Set M} (word : List G) (g : G) :
  ∃ ( l : ListOfListFunctions G ((↥(G \ {g.val})) ⊕ Unit) ) ,
isListOfPrimeFunction l ∧ l.eval (WordOf' word s0') = WordOf' word (s1' G g) := by sorry

instance fintypeGen (M : Type) (G : Set M) [Monoid M] [Fintype M] : Fintype (Submonoid.closure G) := sorry

instance fintypeGenS (M : Type) (G : Set M) [Semigroup M] [Fintype M] : Fintype (Subsemigroup.closure G) := sorry

instance fintypeSubset (M : Type) (G : Set M) [Fintype M] : Fintype G := sorry

theorem s1'_to_s2' {M} [Monoid M] [DecidableEq M] [Fintype M] {G : Set M} (word : List G) (g : G)
  (ih : ∀ (G : Set M), Fintype.card ↥(Submonoid.closure G) ≤ n + 1 → Fintype.card ↑G ≤ m → ∃ f, CorrectPrefSubG G f ∧ CompositionOfPrimes f)
  (hn : Fintype.card ↥(Submonoid.closure G) ≤ n + 1) (hm : Fintype.card ↑G ≤ m + 1) :
  ∃ ( l : ListOfListFunctions  ((↥(G \ {g.val})) ⊕ Unit) ((Submonoid.closure G) ⊕ Unit) ) ,
isListOfPrimeFunction l ∧ l.eval (WordOf' word (s1' G g)) = WordOf' word (s2' G g) := by sorry

theorem s2'_to_s3' {M} [Monoid M] [DecidableEq M] [Fintype M] {G : Set M} (word : List G) (g : G) :
  ∃ ( l : ListOfListFunctions ((Submonoid.closure G) ⊕ Unit) (Submonoid.closure G) ) ,
isListOfPrimeFunction l ∧ l.eval (WordOf' word (s2' G g)) = WordOf' word (s3' G g) := by sorry

theorem s3'_to_s4'' {M} [Monoid M] [DecidableEq M] [Fintype M] {G : Set M} (word : List G) (g : G) :
  ∃ ( l : ListOfListFunctions (Submonoid.closure G) (Submonoid.closure G) ) ,
isListOfPrimeFunction l ∧ l.eval (WordOf' word (s3' G g)) = WordOf' word (s4'' G g) := by sorry

def s2'_times_s4''{M} [Monoid M] [DecidableEq M] [Fintype M] (G : Set M) (g : G)
    (word : List G) (i : Fin word.length) :
  ((Submonoid.closure G) ⊕ Unit) × (Submonoid.closure G) :=
  ⟨ s2' G g word i , s4'' G g word i ⟩

theorem s2'_s4''_to_s5' {M} [Monoid M] [DecidableEq M] [Fintype M] {G : Set M} (word : List G) (g : G) :
  ∃ ( l : ListOfListFunctions (((Submonoid.closure G) ⊕ Unit) × (Submonoid.closure G)) (ClosureShiftOrOne G g.1) ) ,
isListOfPrimeFunction l ∧ l.eval (WordOf' word (s2'_times_s4'' G g)) = WordOf' word (s5' G g) := by sorry

theorem s5'_to_s6' {n m} {M} [Monoid M] [DecidableEq M] [Fintype M] {G : Set M} (word : List G) (g : G)
  (ih' : ∀ (G : Set M) (m : ℕ),
  Fintype.card ↥(Submonoid.closure G) ≤ n → Fintype.card ↑G ≤ m → ∃ f, CorrectPrefSubG G f ∧ CompositionOfPrimes f)
  (hn : Fintype.card ↥(Submonoid.closure G) ≤ n + 1) (hm : Fintype.card ↑G ≤ m + 1) :
  ∃ ( l : ListOfListFunctions (ClosureShiftOrOne G g.1) (Submonoid.closure G)),
isListOfPrimeFunction l ∧ l.eval (WordOf' word (s5' G g)) = WordOf' word (s6' G g) := by sorry

def s2'_times_s6' {M} [Monoid M] [DecidableEq M] [Fintype M] (G : Set M) (g : G)
    (word : List G) (i : Fin word.length) :
  ((Submonoid.closure G) ⊕ Unit) × (Submonoid.closure G) :=
  ⟨ s2' G g word i , s6' G g word i ⟩


theorem s2'_s6'_to_s7' {n m} {M} [Monoid M] [DecidableEq M] [Fintype M] {G : Set M} (word : List G) (g : G)
  (ih' : ∀ (G : Set M) (m : ℕ),
  Fintype.card ↥(Submonoid.closure G) ≤ n → Fintype.card ↑G ≤ m → ∃ f, CorrectPrefSubG G f ∧ CompositionOfPrimes f)
  (hn : Fintype.card ↥(Submonoid.closure G) ≤ n + 1) (hm : Fintype.card ↑G ≤ m + 1) :
  ∃ ( l : ListOfListFunctions (((Submonoid.closure G) ⊕ Unit) × (Submonoid.closure G)) (Submonoid.closure G)),
isListOfPrimeFunction l ∧ l.eval (WordOf' word (s2'_times_s6' G g)) = WordOf' word (s7' G g) := by sorry
