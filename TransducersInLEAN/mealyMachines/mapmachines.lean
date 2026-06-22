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


theorem list_of_primes_for_rev {α σ β} [DecidableEq σ] (MM : MealyMachine α σ β) (h : ReversibleMealyMachine MM) :
  CompositionOfPrimes (mapC MM.eval) := by
  unfold CompositionOfPrimes
  sorry

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

theorem map_lift {α β} (l : ListOfListFunctions α β) (h : isListOfPrimeFunction l) :
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

theorem map_prime_composition {α β} (f : List α → List β) (h : CompositionOfPrimes f) :
CompositionOfPrimes (mapC f) := by
  unfold CompositionOfPrimes at h
  obtain ⟨ l , l_prime , l_eval ⟩ := h
  obtain ⟨ l2 , l2_prime , l2_eval ⟩ := map_lift l l_prime
  use l2
  constructor
  · exact l2_prime
  · rw [l2_eval,l_eval]
