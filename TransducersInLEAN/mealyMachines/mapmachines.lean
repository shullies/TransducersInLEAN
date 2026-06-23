import TransducersInLEAN.mealyMachines.reversibleMapMachines

open scoped Classical

def flipfloplift {α σ β}
    (MM : MealyMachine α σ β) : MealyMachine (α ⊕ Unit) σ (β ⊕ Unit) :=
  have : Fintype α := MM.alphaFin
  have : Fintype β := MM.betaFin
  have : Fintype σ := MM.statesFin
  let step_fn (state : σ) (input : α ⊕ Unit) : (β ⊕ Unit) × σ :=
    match input with
    | .inl a =>
      let (out, next_state) := MM.step state a
      (Sum.inl out, next_state)
    | .inr () =>
      (Sum.inr (), MM.start)
  {
    step := step_fn ,
    start := MM.start
  }

theorem flipfloplift_is_prime {α β σ} (MM : MealyMachine α σ β) (h : FlipFlopMachine MM) :
  FlipFlopMachine (flipfloplift MM) := by
  rw [FlipFlopMachine]
  intro a
  match a with
  | .inr () =>
  right
  use MM.start
  trivial
  | .inl a =>
  rw [FlipFlopMachine] at h
  rcases (h a) with identity | sing_output
  · left
    ext s
    unfold nextState
    dsimp
    have h := congr_fun identity s
    unfold nextState at h
    dsimp at h
    exact h
  · right
    obtain ⟨ s , hs ⟩  := sing_output
    use s
    unfold nextState
    dsimp
    apply hs

lemma MM_eval_split {α β σ} (MM : MealyMachine α σ β) (word1 : List α) (word2 : List α)
  (state : σ) :
  MM.evalFrom state (word1 ++ word2) =
  (MM.evalFrom state word1) ++ (MM.evalFrom (MM.evalstate state word1) word2) := by
  induction word1 generalizing state with
  | nil => trivial
  | cons h t ih =>
  simp [MealyMachine.evalFrom]
  apply ih

lemma flipfloplifteval_on_pure_word {α β σ} (MM : MealyMachine α σ β) (word : List α)
  (state : σ) :
  (flipfloplift MM).evalFrom state (word.map Sum.inl) = (MM.evalFrom state word).map Sum.inl := by
  induction word generalizing state with
  | nil => trivial
  | cons h t ih =>
  simp [MealyMachine.evalFrom,flipfloplift]
  rw [← flipfloplift]
  apply ih

lemma BaseCase {α β σ} (MM : MealyMachine α σ β) (_h : FlipFlopMachine MM) (stored : List α)
  (state : σ):
  List.map Sum.inl (MealyMachine.evalFrom state MM stored) =
  MealyMachine.evalFrom state (flipfloplift MM) (List.map Sum.inl stored) := by
  induction stored generalizing state with
  | nil => trivial
  | cons h t ih =>
  simp [flipfloplift , MealyMachine.evalFrom]
  rw [← flipfloplift ]
  apply ih

lemma flipfloplift_ismapCAux {α β σ} (MM : MealyMachine α σ β) (h : FlipFlopMachine MM)
  (stored : List α) (tail : List (α ⊕ Unit)) :
  mapCaux stored MM.eval tail = (flipfloplift MM).eval ((stored.map Sum.inl ) ++ tail) := by
  induction tail generalizing stored with
  | nil =>
  simp
  apply BaseCase
  exact h
  |cons h t ih =>
  simp [mapCaux]
  match h with
  | .inr a =>
  simp [MealyMachine.eval]
  rw [MM_eval_split]
  rw [flipfloplifteval_on_pure_word]
  simp [flipfloplift,MealyMachine.evalFrom]
  rw [← flipfloplift]
  apply ih
  | .inl a =>
  simp [ih]

lemma flipfloplift_ismapC {α β σ} (MM : MealyMachine α σ β) (h : FlipFlopMachine MM) :
  mapC (MM.eval) = (flipfloplift MM).eval := by
  funext word
  rw [mapC]
  simp [flipfloplift_ismapCAux,h]


theorem s0_to_s1MM_is_prime {α σ β : Type*} [DecidableEq σ] (MM : MealyMachine α σ β)
  (h : ReversibleMealyMachine MM) :
  PrimeMachine (s0_to_s1MM MM h) := by
  apply single_State_MM_is_prime

theorem s1_to_s2MM_is_prime {α σ β : Type*} [DecidableEq σ] (MM : MealyMachine α σ β)
  (h : ReversibleMealyMachine MM) :
  PrimeMachine (s1_to_s2MM MM h) := by
  unfold PrimeMachine
  left
  simp only [ReversibleMealyMachine , s1_to_s2MM ]
  intro letter
  unfold nextState
  dsimp
  simpa using (Equiv.mulLeft letter).bijective

theorem s0_s2_to_s3MM_is_prime {α σ β : Type*} [DecidableEq σ] (MM : MealyMachine α σ β)
  (h : ReversibleMealyMachine MM) :
  (PrimeMachine (s0_s2_to_s3MM MM h)) := by
  unfold PrimeMachine
  right
  simp only [FlipFlopMachine ]
  intro letter
  rcases letter with ⟨val | val, perm⟩
  · left
    unfold nextState
    dsimp
    simp only [s0_s2_to_s3MM]
    trivial
  · right
    use perm
    unfold nextState
    simp only [s0_s2_to_s3MM]

theorem s2_s3_to_s4MM_is_prime {α σ β : Type*} [DecidableEq σ] (MM : MealyMachine α σ β)
  (h : ReversibleMealyMachine MM) :
  (PrimeMachine (s2_s3_to_s4MM MM h)) := by
  apply single_State_MM_is_prime

theorem s4_to_s5MM_is_prime {α σ β : Type*} [DecidableEq σ] (MM : MealyMachine α σ β) :
  (PrimeMachine (s4_to_s5MM MM)) := by
  unfold PrimeMachine
  right
  unfold FlipFlopMachine
  intro letter
  right
  use letter
  unfold nextState
  simp only [s4_to_s5MM]

theorem s0_s5_to_s6MM_is_prime {α σ β : Type*} [DecidableEq σ] (MM : MealyMachine α σ β) :
  (PrimeMachine (s0_s5_to_s6MM MM)) := by
  apply single_State_MM_is_prime

def rearrangement_machine (α β γ) [Fintype α] [Fintype β] [Fintype γ]: MealyMachine ((α × β) × γ) Unit (α × (β × γ)) :=
 have stepfn (_state : Unit) (input : ((α × β) × γ)) :=
 ((input.1.1,(input.1.2,input.2)),())
 {
    start := ()
    step := stepfn
  }

theorem rearrangement_machine_eval
    (α β γ : Type)
    [Fintype α] [Fintype β] [Fintype γ]
    (word : List ((α × β) × γ)) :
    (rearrangement_machine α β γ).eval word =
      word.map (fun x => (x.1.1, (x.1.2, x.2))) := by
  induction word with
  | nil =>
      rfl
  | cons h t ih =>
      dsimp [rearrangement_machine]
      simp [MealyMachine.eval, MealyMachine.evalFrom]
      rw [← MealyMachine.eval]
      exact ih

theorem rearrangement_machine_eval_zip
    (α β γ : Type)
    [Fintype α] [Fintype β] [Fintype γ]
    (a : List α) (b : List β) (c : List γ) :
    (rearrangement_machine α β γ).eval (List.zip (List.zip a b) c) =
      List.zip a (List.zip b c) := by
  rw [rearrangement_machine_eval]
  apply List.ext_getElem
  · simp;
  · intro i h1 h2
    simp

universe u v w

noncomputable def list_of_primes_rev {α σ β} [DecidableEq σ] (MM : MealyMachine α σ β) (h : ReversibleMealyMachine MM) :
  ListOfListFunctions (α ⊕ Unit) (β ⊕ Unit) :=
  have _alphaFin := MM.alphaFin
  have m1 := copy_machine (s0_to_s1MM MM h)
  have m2 := ForwardMachine (α ⊕ Unit) (s1_to_s2MM MM h)
  have _equivFin := m2.statesFin
  have m3 := copy_machine (s0_s2_to_s3MM MM h)
  have m4 := rearrangement_machine (α ⊕ Unit) (Equiv.Perm σ) (Equiv.Perm σ)
  have m5 := ForwardMachine (α ⊕ Unit) (s2_s3_to_s4MM MM h)
  have m6 := ForwardMachine (α ⊕ Unit) (s4_to_s5MM MM)
  have m7 := s0_s5_to_s6MM MM
  ListOfListFunctions.cons m1.eval
  (ListOfListFunctions.cons m2.eval
  (ListOfListFunctions.cons m3.eval
  (ListOfListFunctions.cons m4.eval
  (ListOfListFunctions.cons m5.eval
  (ListOfListFunctions.cons m6.eval
  (ListOfListFunctions.cons m7.eval
  (ListOfListFunctions.nil (β ⊕ Unit)
  )))))))

lemma ForwardMachine_evalFrom_zip {α β σ γ} [Fintype γ]
    (MM : MealyMachine α σ β) (a : List γ) (b : List α) (s : σ) :
    (ForwardMachine γ MM).evalFrom s (List.zip a b) = List.zip a (MM.evalFrom s b) := by
    induction a generalizing s b
    · simp[MealyMachine.evalFrom]
    next ih =>
      cases b
      · simp [MealyMachine.evalFrom]
      · simp [MealyMachine.evalFrom]
        constructor
        · simp [ForwardMachine]
        · simp [ih]
          congr 1

lemma ForwardMachine_eval_zip {α β σ γ} [Fintype γ]
    (MM : MealyMachine α σ β) (a : List γ) (b : List α) :
    (ForwardMachine γ MM).eval (List.zip a b) = List.zip a (MM.eval b) := by
  simp [MealyMachine.eval]
  apply ForwardMachine_evalFrom_zip

-- A very hacky fix here by just putting all of these belonging to Type , I don't know how to fix it
theorem list_of_primes_for_rev {α σ β : Type} [DecidableEq σ] (MM : MealyMachine α σ β) (h : ReversibleMealyMachine MM) :
  CompositionOfPrimes (mapC MM.eval) := by
  letI  alphaFin := MM.alphaFin
  unfold CompositionOfPrimes
  use (list_of_primes_rev MM h : ListOfListFunctions (α ⊕ Unit) (β ⊕ Unit))
  constructor
  · unfold isListOfPrimeFunction
    simp only [ListOfListFunctions.all,list_of_primes_rev,
    copy_machine_prime ,
    ForwardMachine_is_prime_if_MM_is_prime ,
    primeSeqeuntial_of_primeMM ,
    s1_to_s2MM_is_prime ,
    s0_s2_to_s3MM_is_prime ,
    s4_to_s5MM_is_prime ,
    rearrangement_machine,
    single_State_MM_is_prime
    ]
    trivial
  · funext l
    rw [← s6_eq_mapCMM (h := h)]
    rw [← s0_s5_to_s6MM_eq]
    simp [list_of_primes_rev,ListOfListFunctions.eval]
    apply congrArg
    have  h3: WordOf l (s0_times_s5 MM h) = List.zip (WordOf l (s0 MM )) (WordOf l (s5 MM h)):= by
      unfold WordOf s0_times_s5
      apply List.ext_getElem
      · simp
      · intro i h1 h2
        simp only [List.getElem_zip, List.getElem_ofFn]

    have  h1: WordOf l (s0_times_s2 MM h) = List.zip (WordOf l (s0 MM )) (WordOf l (s2 MM h)):= by
      unfold WordOf s0_times_s2
      apply List.ext_getElem
      · simp
      · intro i h1 h2
        simp only [List.getElem_zip, List.getElem_ofFn]

    have  h2: WordOf l (s2_times_s3 MM h) = List.zip (WordOf l (s2 MM h)) (WordOf l (s3 MM h)):= by
      unfold WordOf s2_times_s3
      apply List.ext_getElem
      · simp
      · intro i h1 h2
        simp only [List.getElem_zip, List.getElem_ofFn]

    nth_rw 1 [← s0_eq_word (word := l) (MM := MM)]
    nth_rw 2 [copy_machine_eval]
    rw [s0_to_s1MM_eq]
    rw [ForwardMachine_eval_zip]
    rw [s1_to_s2MM_eq]
    rw [copy_machine_eval]
    nth_rw 2 [← h1]
    rw [s0_s2_to_s3MM_eq]
    rw [rearrangement_machine_eval_zip]
    rw [← h2]
    rw [ForwardMachine_eval_zip]
    rw [s2_s3_to_s4MM_eq]
    rw [ForwardMachine_eval_zip]
    rw [s4_to_s5MM_eq]
    rw [h3]


theorem list_of_primes_for_flipflop {α σ β} (MM : MealyMachine α σ β) (h : FlipFlopMachine MM) :
  CompositionOfPrimes (mapC MM.eval) := by
  unfold CompositionOfPrimes
  use (ListOfListFunctions.cons (flipfloplift MM).eval (ListOfListFunctions.nil (β ⊕ Unit)))
  constructor
  rw [isListOfPrimeFunction , ListOfListFunctions.all]
  · constructor
    · apply primeSeqeuntial_of_primeMM
      right
      apply flipfloplift_is_prime
      exact h
    · simp [ListOfListFunctions.all]
  · simp [ListOfListFunctions.eval]
    symm
    apply flipfloplift_ismapC
    exact h

theorem map_lift {α β : Type} (l : ListOfListFunctions α β) (h : isListOfPrimeFunction l) :
  ∃ (l2 : ListOfListFunctions (α ⊕ Unit) (β ⊕ Unit)) , isListOfPrimeFunction l2 ∧ l2.eval = mapC l.eval := by
  induction l with
  | nil a =>
  use ListOfListFunctions.nil (a ⊕ Unit)
  constructor
  · trivial
  · simp [mapC , ListOfListFunctions.eval]
    funext x
    have h (stored : List a) (t : List (a ⊕ Unit)) : mapCaux stored id t = id (stored.map Sum.inl)++t := by
      induction t generalizing stored with
      | nil =>  simp [mapCaux]
      | cons head tail ih =>
        match head with
        | .inl elem =>
          simp [ih,mapCaux]
        | .inr elem =>
          simp [ih,mapCaux]
    simp [h]
  | cons head t ih =>
  have head_is_prime : PrimeSequentialFunction head := by
    simp [isListOfPrimeFunction,ListOfListFunctions.all] at h
    exact h.left
  unfold PrimeSequentialFunction at head_is_prime
  obtain ⟨ states , mealymachine , ⟨prime_MM , eval_is_head⟩⟩ := head_is_prime
  rcases prime_MM with rev | flipflop
  · have states_fin := mealymachine.statesFin
    obtain ⟨head_list , ⟨head_list_is_prime_list , head_list_eval⟩⟩ := list_of_primes_for_rev mealymachine rev
    have tail_is_prime : isListOfPrimeFunction t := by
      simp [isListOfPrimeFunction,ListOfListFunctions.all] at h
      rw [isListOfPrimeFunction]
      exact h.right
    obtain ⟨tail_list , ⟨tail_list_is_prime_list , tail_list_eval⟩⟩ := ih tail_is_prime
    use head_list.concat tail_list
    constructor
    · rw [isListOfPrimeFunction,ListOfListFunctions.concat_all]
      constructor
      · rw [← isListOfPrimeFunction]
        exact head_list_is_prime_list
      · rw [← isListOfPrimeFunction]
        exact tail_list_is_prime_list
    · rw [ListOfListFunctions.eval,← ListOfListFunctions.concat_eval]
      rw [tail_list_eval,head_list_eval,eval_is_head]
      rw [distribution_of_map]
  · obtain ⟨head_list , ⟨head_list_is_prime_list , head_list_eval⟩⟩ := list_of_primes_for_flipflop mealymachine flipflop
    have tail_is_prime : isListOfPrimeFunction t := by
      simp [isListOfPrimeFunction,ListOfListFunctions.all] at h
      rw [isListOfPrimeFunction]
      exact h.right
    obtain ⟨tail_list , ⟨tail_list_is_prime_list , tail_list_eval⟩⟩ := ih tail_is_prime
    use head_list.concat tail_list
    constructor
    · rw [isListOfPrimeFunction,ListOfListFunctions.concat_all]
      constructor
      · rw [← isListOfPrimeFunction]
        exact head_list_is_prime_list
      · rw [← isListOfPrimeFunction]
        exact tail_list_is_prime_list
    · rw [ListOfListFunctions.eval,← ListOfListFunctions.concat_eval]
      rw [tail_list_eval,head_list_eval,eval_is_head]
      rw [distribution_of_map]

theorem map_prime_composition {α β : Type} (f : List α → List β) (h : CompositionOfPrimes f) :
CompositionOfPrimes (mapC f) := by
  unfold CompositionOfPrimes at h
  obtain ⟨ l , l_prime , l_eval ⟩ := h
  obtain ⟨ l2 , l2_prime , l2_eval ⟩ := map_lift l l_prime
  use l2
  constructor
  · exact l2_prime
  · rw [l2_eval,l_eval]
