import TransducersInLEAN.mealyMachines.mapmachines

def WordOf' {α β} (word : List α) (f : (word' : List α) → Fin word'.length → β) : (List β) :=
    List.ofFn (fun i => f word i)

theorem len_WordOf' (word : List α) (f : (word' : List α) → Fin word'.length → β) :
  word.length = (WordOf' word f).length := by
    simp [WordOf']

theorem f'_is_bijective
    {M : Type*} [Monoid M] [Fintype M]
    (G : Set M)
    (h_equalsm :
      ∀ g ∈ G,
        (fun x ↦ x * g) '' (Subsemigroup.closure G : Set M)
          = (Subsemigroup.closure G : Set M))
    (g : M) (hg : g ∈ G) :
    Function.Bijective
      (fun (x : Subsemigroup.closure G) ↦
        (⟨(x : M) * g, Subsemigroup.mul_mem (Subsemigroup.closure G) x.2 (Subsemigroup.subset_closure hg)⟩ : Subsemigroup.closure G)) := by
  rw [← Finite.surjective_iff_bijective]
  intro y
  have hy_mem : (y : M) ∈ (Subsemigroup.closure G : Set M) := y.2
  have h_surj := h_equalsm g hg
  have hy_in_image : (y : M) ∈ (fun x ↦ x * g) '' (Subsemigroup.closure G : Set M) := by
    rw [h_surj]
    exact hy_mem
  rcases hy_in_image with ⟨x_val, hx_mem, hx_eq⟩
  use ⟨x_val, hx_mem⟩
  ext
  exact hx_eq

theorem f'_is_surjective
    {M : Type*} [Monoid M] [Fintype M]
    (G : Set M)
    (h_equalsm :
      ∀ g ∈ G,
        (fun x ↦ x * g) '' (Subsemigroup.closure G : Set M)
          = (Subsemigroup.closure G : Set M))
    (g : M) (hg : g ∈ G) :
    Function.Surjective
      (fun (x : Subsemigroup.closure G) ↦
        (⟨(x : M) * g, Subsemigroup.mul_mem (Subsemigroup.closure G) x.2 (Subsemigroup.subset_closure hg)⟩ : Subsemigroup.closure G)) := by
  exact (f'_is_bijective G h_equalsm g hg).surjective

theorem f'_is_injective
    {M : Type*} [Monoid M] [Fintype M]
    (G : Set M)
    (h_equalsm :
      ∀ g ∈ G,
        (fun x ↦ x * g) '' (Subsemigroup.closure G : Set M)
          = (Subsemigroup.closure G : Set M))
    (g : M) (hg : g ∈ G) :
    Function.Injective
      (fun (x : Subsemigroup.closure G) ↦
        (⟨(x : M) * g, Subsemigroup.mul_mem (Subsemigroup.closure G) x.2 (Subsemigroup.subset_closure hg)⟩ : Subsemigroup.closure G)) := by
  exact (f'_is_bijective G h_equalsm g hg).injective


def r0 {M} [Monoid M] [Fintype M] [DecidableEq M] (word : List M) (i : Fin word.length):=
  word[i]

noncomputable def toPerm
    {M : Type*} [Monoid M] [Fintype M] [DecidableEq M]
    {G : Set M}
    (h_equalsm : ∀ g ∈ G, (fun x ↦ x * g) '' (Subsemigroup.closure G : Set M) = (Subsemigroup.closure G : Set M))
    {g : M} (h : g ∈ G ∨ g = 1) :
    Equiv.Perm (Subsemigroup.closure G) :=
  if hg : g = 1 then
    Equiv.refl _
  else
    have hg_in_G : g ∈ G := by
      rcases h with h_in_G | rfl
      · exact h_in_G
      · contradiction

    Equiv.ofBijective
      (fun x ↦ ⟨x * g, Subsemigroup.mul_mem _ x.2 (Subsemigroup.subset_closure hg_in_G)⟩)
      (f'_is_bijective _ h_equalsm _ hg_in_G)

def r0' {M : Type*} [Monoid M] [Fintype M]
    (G : Set M) [DecidablePred (· ∈ G)] [DecidableEq M]
    (word : List M) (i : Fin word.length) : M :=
  if word[i] ∈ G then word[i] else 1

lemma r0'_mem_or_one
    {M : Type*} [Monoid M] [Fintype M] [DecidableEq M]
    (G : Set M) [DecidablePred (· ∈ G)]
    (word : List M) (i : Fin word.length) :
    r0' G word i ∈ G ∨ r0' G word i = 1 := by
  unfold r0'
  split_ifs with h
  · exact Or.inl h
  · exact Or.inr rfl

noncomputable def r1 {M : Type*} [Monoid M] [Fintype M] [DecidableEq M]
    (G : Set M) [DecidablePred (· ∈ G)]
    (h_equalsm : ∀ g ∈ G, (fun x ↦ x * g) '' (Subsemigroup.closure G : Set M) = (Subsemigroup.closure G : Set M))
    (word : List M) (i : Fin word.length) : Equiv.Perm (Subsemigroup.closure G) :=
  toPerm h_equalsm (r0'_mem_or_one G word i)

def r2 {M} [Monoid M] [Fintype M] [DecidableEq M] (word : List M) (i : Fin word.length) : Bool :=
  match i.val with
  | Nat.zero => Bool.true
  | Nat.succ _j => Bool.false

noncomputable def r3 {M} [Monoid M] [Fintype M] [DecidableEq M] (G : Set M) [DecidablePred (· ∈ G)] (h_equalsm : ∀ g ∈ G, (fun x ↦ x * g) '' (Subsemigroup.closure G : Set M) = (Subsemigroup.closure G : Set M)) (word : List M) (i : Fin word.length) : Equiv.Perm (Subsemigroup.closure G) :=
  match i.val with
  | Nat.zero => 1
  | Nat.succ _j => r1 G h_equalsm word i

-- accumulate
noncomputable def r4 {M} [Monoid M] [Fintype M] [DecidableEq M] (G : Set M) [DecidablePred (· ∈ G)] (h_equalsm : ∀ g ∈ G, (fun x ↦ x * g) '' (Subsemigroup.closure G : Set M) = (Subsemigroup.closure G : Set M)) (word : List M) (i : Fin word.length) : Equiv.Perm (Subsemigroup.closure G) :=
  prefixProduct (r3 G h_equalsm word) i.1 i.2

-- capture first element
def r5 {M} [Monoid M] [Fintype M] [DecidableEq M] (G : Set M) [DecidablePred (· ∈ G)] (word : List M) (i : Fin word.length) : M :=
  r0' G word ⟨0, Fin.pos i⟩

-- final function
noncomputable def r6 {M} [Monoid M] [Fintype M] [DecidableEq M]
    (G : Set M) [DecidablePred (· ∈ G)]
    (h_equalsm : ∀ g ∈ G, (fun x ↦ x * g) '' (Subsemigroup.closure G : Set M) = (Subsemigroup.closure G : Set M))
    (word : List M) (i : Fin word.length) : M :=
  let perm := r4 G h_equalsm word i
  let g := r5 G word i
  if h_in_G : g ∈ G then
    let valid_elem : Subsemigroup.closure G := ⟨g, Subsemigroup.subset_closure h_in_G⟩
    (perm valid_elem : M)
  else
    1
