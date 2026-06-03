-- Main Results: Lemmas and Theorems
-- Key statements from "On Perfect Functional Representations"

import «PerfectFunctionalRepresentations».FunctionalRepresentation

namespace PerfectRepresentability

open InfoTheory FunctionalRepresentation

def has_cardinality_two (α : Type) : Prop :=
  ∃ a b : α, a ≠ b ∧ ∀ x : α, x = a ∨ x = b

noncomputable def binary_total_variation_radius {X Y : Type}
    (pXY : JointDistribution X Y) : Probability := by
  classical
  by_cases h : has_cardinality_two X
  · let x₁ : X := Classical.choose h
    let x₂ : X := Classical.choose (Classical.choose_spec h)
    exact total_variation_distance
      (conditional_distribution_of_joint pXY x₁)
      (conditional_distribution_of_joint pXY x₂)
  · exact 0

noncomputable def maximal_functional_representation_information_of_pair {X : Type} {Y : Type}
    (pXY : JointDistribution X Y) : Probability :=
  maximal_functional_representation_information pXY

axiom exists_canonical_representation_of_equation_one {X Y Z : Type}
    (pXYZ : TripleDistribution X Y Z)
    (h_eq1 : satisfies_equation_one pXYZ) :
    Exists fun representation : CanonicalFunctionalRepresentation X Y =>
      And
        (is_canonical_functional_representation (joint_xy_of_xyz pXYZ) representation)
        (mutual_information
            (joint_yw_of_canonical_representation (joint_xy_of_xyz pXYZ) representation) =
          mutual_information (joint_yz_of_xyz pXYZ))

-- LEMMA 1: Canonical representations are as informative as arbitrary functional representations
theorem lemma_1_canonical_representation {X : Type} {Y : Type} {Z : Type}
    (pXYZ : TripleDistribution X Y Z)
    (h_eq1 : satisfies_equation_one pXYZ) :
    Exists fun representation : CanonicalFunctionalRepresentation X Y =>
      And
        (is_canonical_functional_representation (joint_xy_of_xyz pXYZ) representation)
        (mutual_information
            (joint_yw_of_canonical_representation (joint_xy_of_xyz pXYZ) representation) =
          mutual_information (joint_yz_of_xyz pXYZ)) := by
  exact exists_canonical_representation_of_equation_one pXYZ h_eq1

-- LEMMA 2: Singularity is necessary for perfect representability
axiom singularity_characterization_binary_cases {X Y : Type}
    (pY_X : Channel X Y) :
    And
      (perfectly_representable pY_X -> is_singular_channel pY_X)
      (And
        ((And (is_singular_channel pY_X) (has_cardinality_two X)) -> perfectly_representable pY_X)
        ((And (is_singular_channel pY_X) (has_cardinality_two Y)) -> perfectly_representable pY_X))

theorem lemma_2_singularity {X Y : Type}
    (pY_X : Channel X Y) :
    And
      (perfectly_representable pY_X -> is_singular_channel pY_X)
      (And
        ((And (is_singular_channel pY_X) (has_cardinality_two X)) -> perfectly_representable pY_X)
        ((And (is_singular_channel pY_X) (has_cardinality_two Y)) -> perfectly_representable pY_X)) := by
  exact singularity_characterization_binary_cases pY_X

-- LEMMA 3: Total variation distance characterization for |X| = 2
axiom binary_total_variation_characterization {X Y : Type}
    (pXY : JointDistribution X Y)
    (_h_card : has_cardinality_two X) :
    And
      (maximal_functional_representation_information_of_pair pXY =
        entropy (marginal_right pXY) -
          binary_total_variation_radius pXY * entropy (marginal_left pXY))
      (Iff
        (binary_total_variation_radius pXY * entropy (marginal_left pXY) =
          mutual_information pXY)
        (is_singular_channel (conditional_distribution_of_joint pXY)))

theorem lemma_3_total_variation {X Y : Type}
    (pXY : JointDistribution X Y)
    (_h_card : has_cardinality_two X) :
    And
      (maximal_functional_representation_information_of_pair pXY =
        entropy (marginal_right pXY) -
          binary_total_variation_radius pXY * entropy (marginal_left pXY))
      (Iff
        (binary_total_variation_radius pXY * entropy (marginal_left pXY) =
          mutual_information pXY)
        (is_singular_channel (conditional_distribution_of_joint pXY))) := by
  exact binary_total_variation_characterization pXY _h_card

structure ConditionalProbabilityMatrix (k m : Nat) where
  entry : Fin k → Fin m → Probability
  nonnegative : ∀ i j, 0 ≤ entry i j

theorem ConditionalProbabilityMatrix.ext {k m : Nat}
    {M N : ConditionalProbabilityMatrix k m}
    (h_entry : ∀ i : Fin k, ∀ j : Fin m, M.entry i j = N.entry i j) :
    M = N := by
  cases M with
  | mk entryM nonnegativeM =>
      cases N with
      | mk entryN nonnegativeN =>
          have h_fun : entryM = entryN := by
            funext i j
            exact h_entry i j
          cases h_fun
          have h_proof : nonnegativeM = nonnegativeN := by
            exact Subsingleton.elim _ _
          cases h_proof
          rfl

def ConditionalProbabilityMatrix.cast {k m n : Nat}
    (M : ConditionalProbabilityMatrix k m)
    (h : m = n) :
    ConditionalProbabilityMatrix k n :=
  { entry := fun i j => M.entry i (Fin.cast h.symm j)
    nonnegative := by
      intro i j
      exact M.nonnegative i (Fin.cast h.symm j) }

theorem ConditionalProbabilityMatrix.cast_entry {k m n : Nat}
    (M : ConditionalProbabilityMatrix k m)
    (h : m = n)
    (i : Fin k)
    (j : Fin n) :
    (M.cast h).entry i j = M.entry i (Fin.cast h.symm j) := by
  rfl

theorem ConditionalProbabilityMatrix.cast_rfl {k m : Nat}
    (M : ConditionalProbabilityMatrix k m) :
    M.cast rfl = M := by
  apply ConditionalProbabilityMatrix.ext
  intro i j
  rfl

theorem List.ofFn_succ {α : Type} {n : Nat} (f : Fin (n + 1) → α) :
    List.ofFn f = f 0 :: List.ofFn (fun i : Fin n => f i.succ) := by
  apply List.ext_get
  · simp [List.length_ofFn]
  · intro k hk_left hk_right
    cases k with
    | zero =>
        calc
          (List.ofFn f).get ⟨0, hk_left⟩ = f 0 := by
            exact List.getElem_ofFn (f := f) hk_left
          _ = (f 0 :: List.ofFn (fun i : Fin n => f i.succ)).get ⟨0, hk_right⟩ := by
            rfl
    | succ k =>
        have hk_tail : k < (List.ofFn (fun i : Fin n => f i.succ)).length := by
          simpa [List.length_ofFn] using hk_right
        have h_tail_get :
            (List.ofFn (fun i : Fin n => f i.succ)).get ⟨k, hk_tail⟩ =
              f ⟨Nat.succ k, by simpa [List.length_ofFn] using hk_left⟩ := by
          exact List.getElem_ofFn (f := fun i : Fin n => f i.succ) hk_tail
        calc
          (List.ofFn f).get ⟨Nat.succ k, hk_left⟩ =
              f ⟨Nat.succ k, by simpa [List.length_ofFn] using hk_left⟩ := by
                exact List.getElem_ofFn (f := f) hk_left
          _ = (List.ofFn (fun i : Fin n => f i.succ)).get ⟨k, hk_tail⟩ := h_tail_get.symm
          _ = (f 0 :: List.ofFn (fun i : Fin n => f i.succ)).get ⟨Nat.succ k, hk_right⟩ := by
                rfl

theorem List.ofFn_succ_eq_map_finRange {n : Nat} :
    List.ofFn (fun i : Fin n => i.succ) = (List.finRange n).map Fin.succ := by
  apply List.ext_get
  · simp [List.finRange, List.length_ofFn]
  · intro k hk_left hk_right
    have hk_range : k < (List.finRange n).length := by
      simpa [List.length_map] using hk_right
    have h_get_range :
        (List.finRange n).get ⟨k, hk_range⟩ =
          (⟨k, by simpa [List.finRange, List.length_ofFn] using hk_range⟩ : Fin n) := by
      change (List.ofFn (fun i : Fin n => i)).get ⟨k, hk_range⟩ =
        (⟨k, by simpa [List.finRange, List.length_ofFn] using hk_range⟩ : Fin n)
      exact List.getElem_ofFn (f := fun i : Fin n => i) hk_range
    have h_get_map :
        ((List.finRange n).map Fin.succ).get ⟨k, hk_right⟩ =
          Fin.succ ((List.finRange n).get ⟨k, hk_range⟩) := by
      change ((List.finRange n).map Fin.succ)[k] = Fin.succ ((List.finRange n)[k]'hk_range)
      exact List.getElem_map (l := List.finRange n) (f := Fin.succ) (i := k) (h := hk_right)
    calc
      (List.ofFn (fun i : Fin n => i.succ)).get ⟨k, hk_left⟩ =
          (⟨k, by simpa [List.length_ofFn] using hk_left⟩ : Fin n).succ := by
            exact List.getElem_ofFn (f := fun i : Fin n => i.succ) hk_left
      _ = Fin.succ ((List.finRange n).get ⟨k, hk_range⟩) := by
            rw [h_get_range]
      _ = ((List.finRange n).map Fin.succ).get ⟨k, hk_right⟩ := by
            exact h_get_map.symm

theorem List.flatten_map_singleton {α β : Type} (f : α → β) :
    ∀ l : List α, (List.map (fun x => [f x]) l).flatten = List.map f l
  | [] => by
      simp
  | x :: l => by
      simp [List.flatten_map_singleton f l]

theorem List.ofFn_nodup_of_injective {α : Type} {n : Nat}
    (f : Fin n → α)
    (h_injective : Function.Injective f) :
    (List.ofFn f).Nodup := by
  induction n with
  | zero =>
      simp [List.ofFn]
  | succ n ih =>
      rw [List.ofFn_succ f, List.nodup_cons]
      refine ⟨?_, ?_⟩
      · intro h_mem
        rcases (List.mem_ofFn.mp h_mem) with ⟨i, hi⟩
        have h_eq : i.succ = (0 : Fin (n + 1)) := h_injective hi
        have h_val : i.1 + 1 = 0 := by
          simpa using congrArg Fin.val h_eq
        omega
      · apply ih
        intro i j h_eq
        apply Fin.ext
        simpa using congrArg Fin.val (h_injective h_eq)

theorem List.map_nodup_of_injective {α β : Type}
    (f : α → β)
    (h_injective : Function.Injective f)
    {l : List α}
    (h_nodup : l.Nodup) :
    (l.map f).Nodup := by
  induction l with
  | nil =>
      simp
  | cons a l ih =>
      rw [List.nodup_cons] at h_nodup
      rcases h_nodup with ⟨h_not_mem, h_tail⟩
      rw [show List.map f (a :: l) = f a :: List.map f l by rfl, List.nodup_cons]
      refine ⟨?_, ih h_tail⟩
      intro h_mem
      rcases (List.mem_map.mp h_mem) with ⟨a', ha'_mem, h_eq⟩
      apply h_not_mem
      have h_same : a' = a := h_injective h_eq
      simpa [h_same] using ha'_mem

theorem List.finRange_nodup (n : Nat) : (List.finRange n).Nodup := by
  simpa [List.finRange] using
    List.ofFn_nodup_of_injective (fun i : Fin n => i) (fun _ _ h => h)

theorem List.get_finRange_eq {n : Nat} (k : Nat) (hk : k < (List.finRange n).length) :
    (List.finRange n).get ⟨k, hk⟩ =
      (⟨k, by simpa [List.finRange, List.length_ofFn] using hk⟩ : Fin n) := by
  change (List.ofFn (fun i : Fin n => i)).get ⟨k, hk⟩ =
    (⟨k, by simpa [List.finRange, List.length_ofFn] using hk⟩ : Fin n)
  exact List.getElem_ofFn (f := fun i : Fin n => i) hk

theorem List.mem_foldr_append_blocks {α β : Type} (block : β → List α) :
    ∀ {l : List β} {x : α},
      x ∈ List.foldr (fun b acc => block b ++ acc) [] l ↔ ∃ b, b ∈ l ∧ x ∈ block b
  | [], x => by
      simp
  | b :: l, x => by
      constructor
      · intro h_mem
        rcases List.mem_append.mp h_mem with h_mem | h_mem
        · exact ⟨b, by simp, h_mem⟩
        · rcases (List.mem_foldr_append_blocks (block := block)).mp h_mem with ⟨b', hb'_mem, hx⟩
          exact ⟨b', by simp [hb'_mem], hx⟩
      · intro h_mem
        rcases h_mem with ⟨b', hb'_mem, hx⟩
        rcases List.mem_cons.mp hb'_mem with rfl | hb'_tail
        · exact List.mem_append.mpr (Or.inl hx)
        · exact List.mem_append.mpr
            (Or.inr ((List.mem_foldr_append_blocks (block := block)).mpr ⟨b', hb'_tail, hx⟩))

theorem List.foldr_append_blocks_nodup {α β : Type}
    (block : β → List α)
    (h_block : ∀ b, (block b).Nodup)
    (h_cross : ∀ b₁ b₂, b₁ ≠ b₂ → ∀ x, x ∈ block b₁ → ∀ y, y ∈ block b₂ → x ≠ y) :
    ∀ l : List β, l.Nodup → (List.foldr (fun b acc => block b ++ acc) [] l).Nodup
  | [], _ => by
      simp
  | b :: l, h_nodup => by
      rw [List.nodup_cons] at h_nodup
      rcases h_nodup with ⟨h_not_mem, h_tail⟩
      rw [List.foldr, List.nodup_append]
      refine ⟨h_block b, List.foldr_append_blocks_nodup block h_block h_cross l h_tail, ?_⟩
      intro x hx y hy
      rcases (List.mem_foldr_append_blocks block).mp hy with ⟨b', hb'_mem, hy'⟩
      have h_ne : b ≠ b' := by
        intro h_eq
        apply h_not_mem
        simpa [h_eq] using hb'_mem
      exact h_cross b b' h_ne x hx y hy'

theorem List.nodup_get_eq {α : Type} {l : List α}
    (h_nodup : l.Nodup)
    {i j : Fin l.length}
    (h_eq : l.get i = l.get j) :
    i = j := by
  induction l with
  | nil =>
      cases i.2
  | cons a l ih =>
      rw [List.nodup_cons] at h_nodup
      rcases h_nodup with ⟨h_not_mem, h_tail⟩
      cases i with
      | mk i hi =>
          cases i with
          | zero =>
              cases j with
              | mk j hj =>
                  cases j with
                  | zero =>
                      rfl
                  | succ j =>
                      exfalso
                      let j' : Fin l.length := ⟨j, by simpa using hj⟩
                      have h_tail_mem : l.get j' ∈ l := List.get_mem l j'
                      have h_head_eq : a = l.get j' := by
                        simpa [j'] using h_eq
                      have h_a_mem : a ∈ l := by
                        rw [h_head_eq]
                        exact h_tail_mem
                      exact h_not_mem h_a_mem
          | succ i =>
              let i' : Fin l.length := ⟨i, by simpa using hi⟩
              cases j with
              | mk j hj =>
                  cases j with
                  | zero =>
                      exfalso
                      have h_tail_mem : l.get i' ∈ l := List.get_mem l i'
                      have h_head_eq : l.get i' = a := by
                        simpa [i'] using h_eq
                      have h_a_mem : a ∈ l := by
                        rw [← h_head_eq]
                        exact h_tail_mem
                      exact h_not_mem h_a_mem
                  | succ j =>
                      let j' : Fin l.length := ⟨j, by simpa using hj⟩
                      have h_tail_eq : l.get i' = l.get j' := by
                        simpa [i', j'] using h_eq
                      have h_indices : i' = j' := ih h_tail h_tail_eq
                      apply Fin.ext
                      simpa [i', j'] using congrArg Fin.val h_indices

theorem List.nodup_get_injective {α : Type} {l : List α}
    (h_nodup : l.Nodup) :
    Function.Injective (fun i : Fin l.length => l.get i) := by
  intro i j h_eq
  exact List.nodup_get_eq h_nodup h_eq

theorem List.foldr_cons_map_eq_append {α β : Type} (f : α → β) :
    ∀ (l : List α) (acc : List β),
      List.foldr (fun a acc' => f a :: acc') acc l = l.map f ++ acc
  | [], acc => by
      simp
  | a :: l, acc => by
      simp [List.foldr_cons_map_eq_append f l acc]

theorem List.filter_nodup_of_nodup {α : Type} (p : α → Bool) :
    ∀ {l : List α}, l.Nodup → (l.filter fun a => p a).Nodup
  | [], _ => by
      simp
  | a :: l, h_nodup => by
      rw [List.nodup_cons] at h_nodup
      rcases h_nodup with ⟨h_not_mem, h_tail⟩
      by_cases hp : p a = true
      · simp [List.filter, hp, List.filter_nodup_of_nodup (p := p) h_tail]
        intro h_mem
        have h_mem_l : a ∈ l := by
          simpa using h_mem
        exact h_not_mem h_mem_l
      · simpa [List.filter, hp] using List.filter_nodup_of_nodup (p := p) h_tail

theorem List.flatten_map_eq_nil {α β : Type} (f : β → List α) :
    ∀ {l : List β}, (∀ b, b ∈ l → f b = []) -> (l.map f).flatten = []
  | [], _ => by
      simp
  | b :: l, h_nil => by
      have h_head : f b = [] := h_nil b (by simp)
      have h_tail : (l.map f).flatten = [] :=
        List.flatten_map_eq_nil f (fun b' hb' => h_nil b' (by simp [hb']))
      simp [h_head, h_tail]

theorem List.flatten_map_eq_of_nodup_mem {α β : Type} (f : β → List α) :
  ∀ {l : List β} {b : β},
    l.Nodup ->
    b ∈ l ->
      (∀ b', b' ∈ l -> b' ≠ b -> f b' = []) ->
      (l.map f).flatten = f b
  | [], _, _, h_mem, _ => by
      cases h_mem
  | a :: l, b, h_nodup, h_mem, h_zero => by
      rw [List.nodup_cons] at h_nodup
      rcases h_nodup with ⟨h_not_mem, h_tail_nodup⟩
      rcases List.mem_cons.mp h_mem with rfl | h_mem_tail
      · have h_tail_nil : (l.map f).flatten = [] := by
          apply List.flatten_map_eq_nil f
          intro b' hb'
          exact h_zero b' (by simp [hb']) (by
            intro h_eq
            apply h_not_mem
            simpa [h_eq] using hb')
        simp [h_tail_nil]
      · have h_head_nil : f a = [] := by
          exact h_zero a (by simp) (by
            intro h_eq
            subst h_eq
            exact h_not_mem h_mem_tail)
        have h_tail : (l.map f).flatten = f b := by
          apply List.flatten_map_eq_of_nodup_mem f h_tail_nodup h_mem_tail
          intro b' hb' hb'_ne
          exact h_zero b' (by simp [hb']) hb'_ne
        simp [h_head_nil, h_tail]

theorem List.flatten_map_filter_eq {α β : Type} (f : β → List α) (p : β → Bool) :
    ∀ l : List β,
      (List.map (fun b => if p b then f b else []) l).flatten =
        (List.map f (l.filter fun b => p b)).flatten
  | [] => by
      simp
  | b :: l => by
      by_cases hp : p b = true
      · simp [hp, List.flatten_map_filter_eq f p l]
      · simp [hp, List.flatten_map_filter_eq f p l]

theorem List.get_append_left_eq {α : Type} :
  ∀ {l₁ l₂ : List α} (j : Fin l₁.length),
    (l₁ ++ l₂).get ⟨j.1, by
    have h_le : l₁.length ≤ (l₁ ++ l₂).length := by
      simp [List.length_append]
    exact Nat.lt_of_lt_of_le j.2 h_le⟩ = l₁.get j
  | [], l₂, j => by
    cases j.2
  | a :: l₁, l₂, j => by
    cases j with
    | mk j hj =>
      cases j with
      | zero =>
        rfl
      | succ j =>
        let j' : Fin l₁.length := ⟨j, by simpa using hj⟩
        simpa [j'] using List.get_append_left_eq (l₁ := l₁) (l₂ := l₂) j'

theorem List.get_append_right_eq {α : Type} :
  ∀ {l₁ l₂ : List α} (j : Fin l₂.length),
    (l₁ ++ l₂).get ⟨j.1 + l₁.length, by
      have h_lt : j.1 + l₁.length < l₂.length + l₁.length :=
        Nat.add_lt_add_right j.2 l₁.length
      simpa [List.length_append, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h_lt⟩ = l₂.get j
  | l₁, l₂, j => by
    exact (List.getElem_append_right' l₁ (l₂ := l₂) (i := j.1) j.2).symm

def matrix_is_singular {k m : Nat} (M : ConditionalProbabilityMatrix k m) : Prop :=
  ∀ j i₁ i₂,
    0 < M.entry i₁ j →
    0 < M.entry i₂ j →
    M.entry i₁ j = M.entry i₂ j

def matrix_perfectly_representable {k m : Nat}
    (M : ConditionalProbabilityMatrix k m) : Prop :=
  perfectly_representable M.entry

noncomputable def column_value {k m : Nat}
    (M : ConditionalProbabilityMatrix k m) (j : Fin m) : Probability := by
  classical
  by_cases h : ∃ i : Fin k, 0 < M.entry i j
  · exact M.entry (Classical.choose h) j
  · exact 0

def column_pattern {k m : Nat}
    (M : ConditionalProbabilityMatrix k m) (j : Fin m) : Fin k → Bool :=
  fun i => if 0 < M.entry i j then true else false

theorem entry_eq_column_value_or_zero {k m : Nat}
    (M : ConditionalProbabilityMatrix k m)
    (h_singular : matrix_is_singular M)
    (i : Fin k) (j : Fin m) :
    M.entry i j = if column_pattern M j i then column_value M j else 0 := by
  classical
  by_cases h_pos : 0 < M.entry i j
  · have h_exists : ∃ i' : Fin k, 0 < M.entry i' j := ⟨i, h_pos⟩
    rw [show column_pattern M j i = true by simp [column_pattern, h_pos]]
    simp [column_value, h_exists]
    exact h_singular j i (Classical.choose h_exists) h_pos (Classical.choose_spec h_exists)
  · have h_le_zero : M.entry i j ≤ 0 := Rat.not_lt.mp h_pos
    have h_eq_zero : M.entry i j = 0 := Rat.le_antisymm h_le_zero (M.nonnegative i j)
    rw [show column_pattern M j i = false by simp [column_pattern, h_pos]]
    simp [h_eq_zero]

theorem column_value_positive_of_pattern_true {k m : Nat}
    (M : ConditionalProbabilityMatrix k m)
    (h_singular : matrix_is_singular M)
    (i : Fin k) (j : Fin m)
    (h_col : column_pattern M j i = true) :
    0 < column_value M j := by
  have h_pos : 0 < M.entry i j := by
    by_cases h_pos : 0 < M.entry i j
    · exact h_pos
    · simp [column_pattern, h_pos] at h_col
  have h_eq : M.entry i j = column_value M j := by
    rw [entry_eq_column_value_or_zero M h_singular i j, h_col]
    simp
  rw [← h_eq]
  exact h_pos

structure ColumnTransport (α β : Type) where
  forward : α → β
  backward : β → α
  left_inv : ∀ a : α, backward (forward a) = a
  right_inv : ∀ b : β, forward (backward b) = b

abbrev ColumnsExceptOne {m : Nat} (source : Fin m) :=
  { j : Fin m // j ≠ source }

abbrev ColumnsExceptTwo {m : Nat} (source₁ source₂ : Fin m) :=
  { j : Fin m // j ≠ source₁ ∧ j ≠ source₂ }

abbrev ColumnsExceptTarget {n : Nat} (target : Fin n) :=
  { j : Fin n // j ≠ target }

abbrev ColumnsExceptPair {n : Nat} (left right : Fin n) :=
  { j : Fin n // j ≠ left ∧ j ≠ right }

def excludeOne_forward {n : Nat} (source : Fin (n + 1))
    (j : ColumnsExceptOne source) : Fin n :=
  if hlt : j.1.1 < source.1 then
    ⟨j.1.1, Nat.lt_of_lt_of_le hlt (Nat.le_of_lt_succ source.2)⟩
  else
    have h_ne_val : j.1.1 ≠ source.1 := by
      intro h_eq
      apply j.2
      apply Fin.ext
      simpa using h_eq
    have h_gt : source.1 < j.1.1 := by
      omega
    ⟨j.1.1 - 1, by omega⟩

def excludeOne_backward {n : Nat} (source : Fin (n + 1))
    (j : Fin n) : ColumnsExceptOne source :=
  if hlt : j.1 < source.1 then
    ⟨j.castSucc, by
      intro h_eq
      have h_val : j.1 = source.1 := by
        simpa using congrArg Fin.val h_eq
      omega⟩
  else
    ⟨j.succ, by
      intro h_eq
      have h_val : j.1 + 1 = source.1 := by
        simpa using congrArg Fin.val h_eq
      have h_ge : source.1 ≤ j.1 := Nat.not_lt.mp hlt
      omega⟩

theorem excludeOne_backward_forward {n : Nat} (source : Fin (n + 1))
    (j : ColumnsExceptOne source) :
    excludeOne_backward source (excludeOne_forward source j) = j := by
  rcases j with ⟨j, h_ne⟩
  by_cases hlt : j.1 < source.1
  · apply Subtype.ext
    apply Fin.ext
    dsimp [excludeOne_forward, excludeOne_backward]
    rw [dif_pos hlt, dif_pos hlt]
    rfl
  · have h_ne_val : j.1 ≠ source.1 := by
      intro h_eq
      apply h_ne
      apply Fin.ext
      simpa using h_eq
    have h_gt : source.1 < j.1 := by
      omega
    have hlt' : ¬ j.1 - 1 < source.1 := by
      omega
    have hj_ge : 1 ≤ j.1 := by
      omega
    apply Subtype.ext
    apply Fin.ext
    dsimp [excludeOne_forward, excludeOne_backward]
    rw [dif_neg hlt, dif_neg hlt']
    simpa using Nat.sub_add_cancel hj_ge

theorem excludeOne_forward_backward {n : Nat} (source : Fin (n + 1))
    (j : Fin n) :
    excludeOne_forward source (excludeOne_backward source j) = j := by
  by_cases hlt : j.1 < source.1
  · apply Fin.ext
    have h_cast : (j.castSucc : Fin (n + 1)).1 < source.1 := by
      simpa using hlt
    dsimp [excludeOne_backward, excludeOne_forward]
    rw [dif_pos hlt, dif_pos h_cast]
    rfl
  · have h_ge : source.1 ≤ j.1 := Nat.not_lt.mp hlt
    have h_if : ¬ j.1 + 1 < source.1 := by
      exact Nat.not_lt.mpr (Nat.le_trans h_ge (Nat.le_succ j.1))
    apply Fin.ext
    simp [excludeOne_backward, excludeOne_forward, hlt, h_if]

def excludeOne_transport {n : Nat} (source : Fin (n + 1)) :
    ColumnTransport (ColumnsExceptOne source) (Fin n) :=
  { forward := excludeOne_forward source
    backward := excludeOne_backward source
    left_inv := excludeOne_backward_forward source
    right_inv := excludeOne_forward_backward source }

axiom discrete_sum_fin_remove {n : Nat} (source : Fin (n + 1))
    (f : Fin (n + 1) → Probability) :
    discrete_sum f =
      f source + discrete_sum (fun j : Fin n => f (excludeOne_backward source j).1)

theorem excludeOne_backward_zero {n : Nat} (j : Fin n) :
    (excludeOne_backward (0 : Fin (n + 1)) j).1 = j.succ := by
  simp [excludeOne_backward]

theorem discrete_sum_fin_reindex_injective {n : Nat}
    (f : Fin n → Probability)
    (σ : Fin n → Fin n)
    (h_inj : Function.Injective σ) :
    discrete_sum (fun j : Fin n => f (σ j)) = discrete_sum f := by
  induction n with
  | zero =>
      apply InfoTheory.discrete_sum_congr
      intro j
      exact False.elim (Nat.not_lt_zero _ j.2)
  | succ n ih =>
      let source : Fin (n + 1) := σ 0
      have h_tail_ne : ∀ j : Fin n, σ j.succ ≠ source := by
        intro j h_eq
        have h_same : j.succ = 0 := h_inj (by simpa [source] using h_eq)
        have h_val : j.1 + 1 = 0 := by
          simpa using congrArg Fin.val h_same
        exact Nat.succ_ne_zero j.1 h_val
      let τ : Fin n → Fin n := fun j =>
        excludeOne_forward source ⟨σ j.succ, h_tail_ne j⟩
      have h_tau_inj : Function.Injective τ := by
        intro j₁ j₂ h_eq
        have h_sub :
            (⟨σ j₁.succ, h_tail_ne j₁⟩ : ColumnsExceptOne source) =
              (⟨σ j₂.succ, h_tail_ne j₂⟩ : ColumnsExceptOne source) := by
          calc
            (⟨σ j₁.succ, h_tail_ne j₁⟩ : ColumnsExceptOne source) =
                excludeOne_backward source (τ j₁) := by
                  exact (excludeOne_backward_forward source
                    ⟨σ j₁.succ, h_tail_ne j₁⟩).symm
            _ = excludeOne_backward source (τ j₂) := by rw [h_eq]
            _ = (⟨σ j₂.succ, h_tail_ne j₂⟩ : ColumnsExceptOne source) := by
                  exact excludeOne_backward_forward source
                    ⟨σ j₂.succ, h_tail_ne j₂⟩
        have h_sigma : σ j₁.succ = σ j₂.succ := congrArg Subtype.val h_sub
        have h_succ : j₁.succ = j₂.succ := h_inj h_sigma
        apply Fin.ext
        have h_val : j₁.1 + 1 = j₂.1 + 1 := by
          simpa using congrArg Fin.val h_succ
        omega
      have h_tail :
          discrete_sum (fun j : Fin n => f (σ j.succ)) =
            discrete_sum (fun j : Fin n => f (excludeOne_backward source j).1) := by
        calc
          discrete_sum (fun j : Fin n => f (σ j.succ)) =
              discrete_sum (fun j : Fin n => f (excludeOne_backward source (τ j)).1) := by
                apply InfoTheory.discrete_sum_congr
                intro j
                have h_back :
                    excludeOne_backward source (τ j) =
                      (⟨σ j.succ, h_tail_ne j⟩ : ColumnsExceptOne source) := by
                  exact excludeOne_backward_forward source
                    ⟨σ j.succ, h_tail_ne j⟩
                simpa [τ] using (congrArg f (congrArg Subtype.val h_back)).symm
          _ = discrete_sum (fun j : Fin n => f (excludeOne_backward source j).1) := by
                exact ih (fun j : Fin n => f (excludeOne_backward source j).1) τ h_tau_inj
      calc
        discrete_sum (fun j : Fin (n + 1) => f (σ j)) =
            f source + discrete_sum (fun j : Fin n => f (σ j.succ)) := by
              simpa [source] using discrete_sum_fin_remove
                (source := (0 : Fin (n + 1)))
                (f := fun j : Fin (n + 1) => f (σ j))
        _ = f source + discrete_sum (fun j : Fin n => f (excludeOne_backward source j).1) := by
              rw [h_tail]
        _ = discrete_sum f := by
              symm
              exact discrete_sum_fin_remove source f

theorem discrete_sum_fin_reindex_injective_of_zero_off_range {m n : Nat}
    (f : Fin n → Probability)
    (σ : Fin m → Fin n)
    (h_inj : Function.Injective σ)
    (h_zero_off : ∀ k : Fin n, (∀ j : Fin m, σ j ≠ k) → f k = 0) :
    discrete_sum (fun j : Fin m => f (σ j)) = discrete_sum f := by
  induction m generalizing n with
  | zero =>
      have h_zero_fun : f = fun _ => 0 := by
        funext k
        exact h_zero_off k (by
          intro j
          exact False.elim (Nat.not_lt_zero _ j.2))
      have h_empty_fun : (fun j : Fin 0 => f (σ j)) = fun _ : Fin 0 => 0 := by
        funext j
        exact False.elim (Nat.not_lt_zero _ j.2)
      calc
        discrete_sum (fun j : Fin 0 => f (σ j)) = discrete_sum (fun _ : Fin 0 => 0) := by
          rw [h_empty_fun]
        _ = 0 := InfoTheory.discrete_sum_zero
        _ = discrete_sum f := by
          rw [h_zero_fun]
          symm
          exact InfoTheory.discrete_sum_zero
  | succ m ih =>
      cases n with
      | zero =>
          have h_false : False := by
            exact Nat.not_lt_zero _ (σ 0).2
          exact False.elim h_false
      | succ n =>
          let source : Fin (n + 1) := σ 0
          have h_tail_ne : ∀ j : Fin m, σ j.succ ≠ source := by
            intro j h_eq
            have h_same : j.succ = 0 := h_inj (by simpa [source] using h_eq)
            have h_val : j.1 + 1 = 0 := by
              simpa using congrArg Fin.val h_same
            exact Nat.succ_ne_zero j.1 h_val
          let τ : Fin m → Fin n := fun j =>
            excludeOne_forward source ⟨σ j.succ, h_tail_ne j⟩
          have h_tau_inj : Function.Injective τ := by
            intro j₁ j₂ h_eq
            have h_sub :
                (⟨σ j₁.succ, h_tail_ne j₁⟩ : ColumnsExceptOne source) =
                  (⟨σ j₂.succ, h_tail_ne j₂⟩ : ColumnsExceptOne source) := by
              calc
                (⟨σ j₁.succ, h_tail_ne j₁⟩ : ColumnsExceptOne source) =
                    excludeOne_backward source (τ j₁) := by
                      exact (excludeOne_backward_forward source
                        ⟨σ j₁.succ, h_tail_ne j₁⟩).symm
                _ = excludeOne_backward source (τ j₂) := by rw [h_eq]
                _ = (⟨σ j₂.succ, h_tail_ne j₂⟩ : ColumnsExceptOne source) := by
                      exact excludeOne_backward_forward source
                        ⟨σ j₂.succ, h_tail_ne j₂⟩
            have h_sigma : σ j₁.succ = σ j₂.succ := congrArg Subtype.val h_sub
            have h_succ : j₁.succ = j₂.succ := h_inj h_sigma
            apply Fin.ext
            have h_val : j₁.1 + 1 = j₂.1 + 1 := by
              simpa using congrArg Fin.val h_succ
            omega
          have h_zero_tail :
              ∀ k : Fin n,
                (∀ j : Fin m, τ j ≠ k) →
                  (fun j : Fin n => f (excludeOne_backward source j).1) k = 0 := by
            intro k h_off
            exact h_zero_off (excludeOne_backward source k).1 (by
              intro j
              by_cases h_zero : j = 0
              · intro h_eq
                have h_eq_source : (excludeOne_backward source k).1 = source := by
                  simpa [h_zero, source] using h_eq.symm
                exact (excludeOne_backward source k).2 h_eq_source
              · let j' : Fin m := ⟨j.1 - 1, by
                  have h_ne : j.1 ≠ 0 := by
                    intro h_val
                    apply h_zero
                    apply Fin.ext
                    exact h_val
                  have h_pos : 0 < j.1 := Nat.pos_of_ne_zero h_ne
                  have h_lt : j.1 < m + 1 := j.2
                  omega⟩
                have h_j : j = j'.succ := by
                  apply Fin.ext
                  dsimp [j']
                  have h_ne : j.1 ≠ 0 := by
                    intro h_val
                    apply h_zero
                    apply Fin.ext
                    exact h_val
                  have h_pos : 0 < j.1 := Nat.pos_of_ne_zero h_ne
                  omega
                intro h_eq
                apply h_off j'
                have h_sub :
                    (⟨σ j'.succ, h_tail_ne j'⟩ : ColumnsExceptOne source) =
                      excludeOne_backward source k := by
                  apply Subtype.ext
                  simpa [h_j] using h_eq
                calc
                  τ j' = excludeOne_forward source (excludeOne_backward source k) := by
                    simpa [τ] using congrArg (excludeOne_forward source) h_sub
                  _ = k := excludeOne_forward_backward source k)
          have h_tail :
              discrete_sum (fun j : Fin m => f (σ j.succ)) =
                discrete_sum (fun j : Fin n => f (excludeOne_backward source j).1) := by
            calc
              discrete_sum (fun j : Fin m => f (σ j.succ)) =
                  discrete_sum (fun j : Fin m => f (excludeOne_backward source (τ j)).1) := by
                    apply InfoTheory.discrete_sum_congr
                    intro j
                    have h_back :
                        excludeOne_backward source (τ j) =
                          (⟨σ j.succ, h_tail_ne j⟩ : ColumnsExceptOne source) := by
                      exact excludeOne_backward_forward source
                        ⟨σ j.succ, h_tail_ne j⟩
                    simpa [τ] using (congrArg f (congrArg Subtype.val h_back)).symm
              _ = discrete_sum (fun j : Fin n => f (excludeOne_backward source j).1) := by
                    exact ih (fun j : Fin n => f (excludeOne_backward source j).1) τ h_tau_inj h_zero_tail
          calc
            discrete_sum (fun j : Fin (m + 1) => f (σ j)) =
                f source + discrete_sum (fun j : Fin m => f (σ j.succ)) := by
                  simpa [source] using discrete_sum_fin_remove
                    (source := (0 : Fin (m + 1)))
                    (f := fun j : Fin (m + 1) => f (σ j))
            _ = f source + discrete_sum (fun j : Fin n => f (excludeOne_backward source j).1) := by
                  rw [h_tail]
            _ = discrete_sum f := by
                  symm
                  exact discrete_sum_fin_remove source f

theorem discrete_sum_fin_one (f : Fin 1 → Probability) :
    discrete_sum f = f 0 := by
  have h_tail_zero :
      discrete_sum (fun j : Fin 0 => f (excludeOne_backward (0 : Fin 1) j).1) = 0 := by
    have h_fun :
        (fun j : Fin 0 => f (excludeOne_backward (0 : Fin 1) j).1) = fun _ : Fin 0 => 0 := by
      funext j
      exact False.elim (Nat.not_lt_zero _ j.2)
    rw [h_fun, InfoTheory.discrete_sum_zero]
  calc
    discrete_sum f = f 0 + discrete_sum (fun j : Fin 0 => f (excludeOne_backward (0 : Fin 1) j).1) := by
      simpa using discrete_sum_fin_remove (source := (0 : Fin 1)) (f := f)
    _ = f 0 := by rw [h_tail_zero, Rat.add_zero]

theorem discrete_sum_singleton_indicator {n : Nat} (w₀ : Fin n) :
    discrete_sum (fun w : Fin n => if w = w₀ then 1 else 0) = 1 := by
  let f : Fin n → Probability := fun w => if w = w₀ then 1 else 0
  let σ : Fin 1 → Fin n := fun _ => w₀
  have h_inj : Function.Injective σ := by
    intro a b _
    exact Subsingleton.elim _ _
  have h_zero_off : ∀ k : Fin n, (∀ j : Fin 1, σ j ≠ k) → f k = 0 := by
    intro k h_off
    by_cases h_eq : k = w₀
    · exfalso
      exact h_off 0 (by simp [σ, h_eq])
    · simp [f, h_eq]
  have h_reindex : discrete_sum (fun j : Fin 1 => f (σ j)) = discrete_sum f := by
    exact discrete_sum_fin_reindex_injective_of_zero_off_range f σ h_inj h_zero_off
  have h_left : discrete_sum (fun j : Fin 1 => f (σ j)) = 1 := by
    have h_fun : (fun j : Fin 1 => f (σ j)) = fun _ : Fin 1 => 1 := by
      funext j
      simp [f, σ]
    rw [h_fun, discrete_sum_fin_one]
  calc
    discrete_sum f = discrete_sum (fun j : Fin 1 => f (σ j)) := by symm; exact h_reindex
    _ = 1 := h_left

theorem exists_duplicate_fin_succ {n : Nat}
    (f : Fin (n + 1) → Fin n) :
    ∃ i j : Fin (n + 1), i ≠ j ∧ f i = f j := by
  induction n with
  | zero =>
      have h_false : False := by
        have h_lt : (f 0).1 < 0 := (f 0).2
        exact (Nat.not_lt_zero _ h_lt)
      exact False.elim h_false
  | succ n ih =>
      let source : Fin (n + 1) := f 0
      by_cases h_hit : ∃ j : Fin (n + 1), f j.succ = source
      · rcases h_hit with ⟨j, h_eq⟩
        refine ⟨0, j.succ, ?_, ?_⟩
        · intro h_idx
          have h_zero : j.1 + 1 = 0 := by
            simpa using congrArg Fin.val h_idx.symm
          exact Nat.succ_ne_zero j.1 h_zero
        · simpa [source] using h_eq.symm
      · let transport := excludeOne_transport source
        let g : Fin (n + 1) → Fin n := fun j =>
          transport.forward ⟨f j.succ, by
            intro h_eq
            exact h_hit ⟨j, h_eq⟩⟩
        rcases ih g with ⟨j₁, j₂, h_ne, h_eqg⟩
        refine ⟨j₁.succ, j₂.succ, ?_, ?_⟩
        · intro h_idx
          apply h_ne
          apply Fin.ext
          have h_val : j₁.1 + 1 = j₂.1 + 1 := by
            simpa using congrArg Fin.val h_idx
          omega
        · have h_sub_eq :
            (⟨f j₁.succ, by
                intro h_eq
                exact h_hit ⟨j₁, h_eq⟩⟩ : ColumnsExceptOne source) =
              ⟨f j₂.succ, by
                intro h_eq
                exact h_hit ⟨j₂, h_eq⟩⟩ := by
            calc
              (⟨f j₁.succ, by
                  intro h_eq
                  exact h_hit ⟨j₁, h_eq⟩⟩ : ColumnsExceptOne source) =
                    transport.backward (g j₁) := by
                      symm
                      exact transport.left_inv _
              _ = transport.backward (g j₂) := by
                    exact congrArg transport.backward h_eqg
              _ = (⟨f j₂.succ, by
                  intro h_eq
                  exact h_hit ⟨j₂, h_eq⟩⟩ : ColumnsExceptOne source) := by
                    exact transport.left_inv _
          exact congrArg Subtype.val h_sub_eq

theorem exists_duplicate_of_lt {m n : Nat}
    (f : Fin m → Fin n)
    (h_lt : n < m) :
    ∃ i j : Fin m, i ≠ j ∧ f i = f j := by
  let g : Fin (n + 1) → Fin n := fun i =>
    f ⟨i.1, Nat.lt_of_lt_of_le i.2 (Nat.succ_le_of_lt h_lt)⟩
  rcases exists_duplicate_fin_succ g with ⟨i, j, h_ne, h_eq⟩
  refine ⟨⟨i.1, Nat.lt_of_lt_of_le i.2 (Nat.succ_le_of_lt h_lt)⟩,
    ⟨j.1, Nat.lt_of_lt_of_le j.2 (Nat.succ_le_of_lt h_lt)⟩, ?_, h_eq⟩
  intro h_idx
  apply h_ne
  apply Fin.ext
  simpa using congrArg Fin.val h_idx

theorem exists_ordered_duplicate_of_lt {m n : Nat}
    (f : Fin m → Fin n)
    (h_lt : n < m) :
    ∃ i j : Fin m, i.1 < j.1 ∧ f i = f j := by
  rcases exists_duplicate_of_lt f h_lt with ⟨i, j, h_ne, h_eq⟩
  have h_val_ne : i.1 ≠ j.1 := by
    intro h_val
    apply h_ne
    apply Fin.ext
    simpa using h_val
  by_cases h_order : i.1 < j.1
  · exact ⟨i, j, h_order, h_eq⟩
  · have h_rev : j.1 < i.1 := by
      omega
    exact ⟨j, i, h_rev, h_eq.symm⟩

theorem fin_surjective_le {m n : Nat}
    (f : Fin m → Fin n)
    (h_surj : ∀ y : Fin n, ∃ x : Fin m, f x = y) :
    n ≤ m := by
  classical
  by_cases h_le : n ≤ m
  · exact h_le
  · have h_lt : m < n := Nat.lt_of_not_ge h_le
    let pick : Fin n → Fin m := fun y => Classical.choose (h_surj y)
    have h_pick : ∀ y : Fin n, f (pick y) = y := by
      intro y
      exact Classical.choose_spec (h_surj y)
    rcases exists_duplicate_of_lt (f := pick) h_lt with ⟨y₁, y₂, h_ne, h_eq⟩
    apply False.elim
    apply h_ne
    calc
      y₁ = f (pick y₁) := by symm; exact h_pick y₁
      _ = f (pick y₂) := by rw [h_eq]
      _ = y₂ := h_pick y₂

theorem fin_surjective_same_injective {n : Nat}
    (f : Fin n → Fin n)
    (h_surj : ∀ y : Fin n, ∃ x : Fin n, f x = y) :
    Function.Injective f := by
  classical
  intro i j h_eq
  by_cases h_same : i = j
  · exact h_same
  · cases n with
    | zero =>
        exact False.elim (Nat.not_lt_zero _ i.2)
    | succ n =>
        let g : Fin n → Fin (n + 1) := fun x => f (excludeOne_backward j x).1
        have h_g_surj : ∀ y : Fin (n + 1), ∃ x : Fin n, g x = y := by
          intro y
          by_cases h_yj : y = f j
          · let keep : ColumnsExceptOne j := ⟨i, h_same⟩
            refine ⟨excludeOne_forward j keep, ?_⟩
            calc
              g (excludeOne_forward j keep) = f (excludeOne_backward j (excludeOne_forward j keep)).1 := by
                rfl
              _ = f keep.1 := by rw [excludeOne_backward_forward j keep]
              _ = f i := rfl
              _ = f j := h_eq
              _ = y := h_yj.symm
          · rcases h_surj y with ⟨x, hx⟩
            have h_xj : x ≠ j := by
              intro h_xj_eq
              apply h_yj
              calc
                y = f x := hx.symm
                _ = f j := by rw [h_xj_eq]
            let keep : ColumnsExceptOne j := ⟨x, h_xj⟩
            refine ⟨excludeOne_forward j keep, ?_⟩
            calc
              g (excludeOne_forward j keep) = f (excludeOne_backward j (excludeOne_forward j keep)).1 := by
                rfl
              _ = f keep.1 := by rw [excludeOne_backward_forward j keep]
              _ = f x := rfl
              _ = y := hx
        have h_le : n + 1 ≤ n := fin_surjective_le g h_g_surj
        exact False.elim (Nat.not_succ_le_self n h_le)

def adjacent_ppm_forward {n : Nat} (target : Fin n)
    (j : ColumnsExceptTwo target.castSucc target.succ) : ColumnsExceptTarget target :=
  if hlt : j.1.1 < target.1 then
    ⟨⟨j.1.1, Nat.lt_trans hlt target.2⟩, by
      intro h_eq
      have h_val : j.1.1 = target.1 := by
        simpa using congrArg Fin.val h_eq
      omega⟩
  else
    have h_gt : target.1 + 1 < j.1.1 := by
      have h_ne_left_val : j.1.1 ≠ target.1 := by
        intro h
        apply j.2.1
        apply Fin.ext
        simpa using h
      have h_ne_right_val : j.1.1 ≠ target.1 + 1 := by
        intro h
        apply j.2.2
        apply Fin.ext
        simpa using h
      omega
    ⟨⟨j.1.1 - 1, by omega⟩, by
      intro h_eq
      have h_val : j.1.1 - 1 = target.1 := by
        simpa using congrArg Fin.val h_eq
      have h_right_val : j.1.1 = target.1 + 1 := by
        omega
      apply j.2.2
      apply Fin.ext
      simpa using h_right_val⟩

def adjacent_ppm_backward {n : Nat} (target : Fin n)
    (j : ColumnsExceptTarget target) : ColumnsExceptTwo target.castSucc target.succ :=
  if hlt : j.1.1 < target.1 then
    ⟨j.1.castSucc, by
      constructor
      · intro h_eq
        apply j.2
        apply Fin.ext
        simpa using congrArg Fin.val h_eq
      · intro h_eq
        have h_val : j.1.1 = target.1 + 1 := by
          simpa using congrArg Fin.val h_eq
        omega⟩
  else
    ⟨j.1.succ, by
      constructor
      · intro h_eq
        have h_val : j.1.1 + 1 = target.1 := by
          simpa using congrArg Fin.val h_eq
        omega
      · intro h_eq
        apply j.2
        apply Fin.ext
        have h_val : j.1.1 + 1 = target.1 + 1 := by
          simpa using congrArg Fin.val h_eq
        omega⟩

theorem adjacent_ppm_backward_forward {n : Nat} (target : Fin n)
    (j : ColumnsExceptTwo target.castSucc target.succ) :
    adjacent_ppm_backward target (adjacent_ppm_forward target j) = j := by
  rcases j with ⟨j, h_ne_left, h_ne_right⟩
  by_cases hlt : j.1 < target.1
  · apply Subtype.ext
    apply Fin.ext
    dsimp [adjacent_ppm_forward, adjacent_ppm_backward]
    rw [dif_pos hlt, dif_pos hlt]
    rfl
  · have h_ne_left_val : target.1 ≠ j.1 := by
      intro h
      apply h_ne_left
      apply Fin.ext
      simp [h]
    have h_ne_right_val : target.1 + 1 ≠ j.1 := by
      intro h
      apply h_ne_right
      apply Fin.ext
      simp [h]
    have h_gt : target.1 + 1 < j.1 := by
      omega
    have hlt' : ¬ j.1 - 1 < target.1 := by
      omega
    have hj_ge : 1 ≤ j.1 := by
      omega
    apply Subtype.ext
    apply Fin.ext
    dsimp [adjacent_ppm_forward, adjacent_ppm_backward]
    rw [dif_neg hlt, dif_neg hlt']
    simpa using Nat.sub_add_cancel hj_ge

theorem adjacent_ppm_forward_backward {n : Nat} (target : Fin n)
    (j : ColumnsExceptTarget target) :
    adjacent_ppm_forward target (adjacent_ppm_backward target j) = j := by
  rcases j with ⟨j, h_ne_target⟩
  by_cases hlt : j.1 < target.1
  · apply Subtype.ext
    apply Fin.ext
    have h_cast : (j.castSucc : Fin (n + 1)).1 < target.1 := by
      simpa using hlt
    dsimp [adjacent_ppm_backward, adjacent_ppm_forward]
    rw [dif_pos hlt, dif_pos h_cast]
    rfl
  · have h_ge : target.1 ≤ j.1 := Nat.not_lt.mp hlt
    have h_ne_target_val : target.1 ≠ j.1 := by
      intro h
      apply h_ne_target
      apply Fin.ext
      simp [h]
    have h_succ_ge : target.1 ≤ (j.succ : Fin (n + 1)).1 := by
      exact Nat.le_trans h_ge (Nat.le_succ j.1)
    have h_succ : ¬ (j.succ : Fin (n + 1)).1 < target.1 := by
      exact Nat.not_lt.mpr h_succ_ge
    apply Subtype.ext
    apply Fin.ext
    dsimp [adjacent_ppm_backward, adjacent_ppm_forward]
    rw [dif_neg hlt, dif_neg h_succ]
    simp

def adjacent_ppm_transport {n : Nat} (target : Fin n) :
    ColumnTransport (ColumnsExceptTwo target.castSucc target.succ) (ColumnsExceptTarget target) :=
  { forward := adjacent_ppm_forward target
    backward := adjacent_ppm_backward target
    left_inv := adjacent_ppm_backward_forward target
    right_inv := adjacent_ppm_forward_backward target }

def adjacent_pps_transport {m : Nat} (source : Fin m) :
    ColumnTransport (ColumnsExceptOne source) (ColumnsExceptPair source.castSucc source.succ) :=
  { forward := adjacent_ppm_backward source
    backward := adjacent_ppm_forward source
    left_inv := adjacent_ppm_forward_backward source
    right_inv := adjacent_ppm_backward_forward source }

def adjacent_pps_split_matrix {k m : Nat}
    (M : ConditionalProbabilityMatrix k m)
    (source : Fin m)
    (α : Probability)
    (h_alpha_nonneg : 0 ≤ α)
    (h_beta_nonneg : 0 ≤ 1 - α) :
    ConditionalProbabilityMatrix k (m + 1) :=
  { entry := fun i j =>
      if h_left : j = source.castSucc then
        α * M.entry i source
      else if h_right : j = source.succ then
        (1 - α) * M.entry i source
      else
        M.entry i ((adjacent_pps_transport source).backward ⟨j, h_left, h_right⟩).1
    nonnegative := by
      intro i j
      by_cases h_left : j = source.castSucc
      · dsimp
        rw [dif_pos h_left]
        exact Rat.mul_nonneg h_alpha_nonneg (M.nonnegative i source)
      · by_cases h_right : j = source.succ
        · dsimp
          rw [dif_neg h_left, dif_pos h_right]
          exact Rat.mul_nonneg h_beta_nonneg (M.nonnegative i source)
        · dsimp
          rw [dif_neg h_left, dif_neg h_right]
          exact M.nonnegative i ((adjacent_pps_transport source).backward ⟨j, h_left, h_right⟩).1 }

theorem adjacent_pps_split_matrix_left {k m : Nat}
    (M : ConditionalProbabilityMatrix k m)
    (source : Fin m)
    (α : Probability)
    (h_alpha_nonneg : 0 ≤ α)
    (h_beta_nonneg : 0 ≤ 1 - α)
    (i : Fin k) :
    (adjacent_pps_split_matrix M source α h_alpha_nonneg h_beta_nonneg).entry i source.castSucc =
      α * M.entry i source := by
  simp [adjacent_pps_split_matrix]

theorem adjacent_pps_split_matrix_right {k m : Nat}
    (M : ConditionalProbabilityMatrix k m)
    (source : Fin m)
    (α : Probability)
    (h_alpha_nonneg : 0 ≤ α)
    (h_beta_nonneg : 0 ≤ 1 - α)
    (i : Fin k) :
    (adjacent_pps_split_matrix M source α h_alpha_nonneg h_beta_nonneg).entry i source.succ =
      (1 - α) * M.entry i source := by
  have h_ne : (source.succ : Fin (m + 1)) ≠ source.castSucc := by
    intro h_eq
    have h_val : source.1 + 1 = source.1 := by
      simpa using congrArg Fin.val h_eq
    omega
  simp [adjacent_pps_split_matrix, h_ne]

theorem adjacent_pps_split_matrix_rest {k m : Nat}
    (M : ConditionalProbabilityMatrix k m)
    (source : Fin m)
    (α : Probability)
    (h_alpha_nonneg : 0 ≤ α)
    (h_beta_nonneg : 0 ≤ 1 - α)
    (old : ColumnsExceptOne source)
    (i : Fin k) :
    (adjacent_pps_split_matrix M source α h_alpha_nonneg h_beta_nonneg).entry i
        ((adjacent_pps_transport source).forward old).1 =
      M.entry i old.1 := by
  dsimp [adjacent_pps_split_matrix, adjacent_pps_transport]
  rw [dif_neg (adjacent_ppm_backward source old).2.1,
    dif_neg (adjacent_ppm_backward source old).2.2]
  have hold :
      (adjacent_ppm_forward source (adjacent_ppm_backward source old)).1 = old.1 :=
    congrArg Subtype.val (adjacent_ppm_forward_backward source old)
  simpa using congrArg (fun j => M.entry i j) hold

theorem adjacent_pps_split_matrix_tail_shift_zero {k m : Nat}
    (M : ConditionalProbabilityMatrix k (m + 1))
    (α : Probability)
    (h_alpha_nonneg : 0 ≤ α)
    (h_beta_nonneg : 0 ≤ 1 - α)
    (i : Fin k)
    (j : Fin m) :
    (adjacent_pps_split_matrix M 0 α h_alpha_nonneg h_beta_nonneg).entry i j.succ.succ =
      M.entry i j.succ := by
  let oldColumn : ColumnsExceptOne (0 : Fin (m + 1)) := ⟨j.succ, by
    intro h_eq
    have h_val : j.1 + 1 = 0 := by
      simpa using congrArg Fin.val h_eq
    exact Nat.succ_ne_zero j.1 h_val⟩
  have h_forward : ((adjacent_pps_transport (0 : Fin (m + 1))).forward oldColumn).1 = j.succ.succ := by
    apply Fin.ext
    simp [adjacent_pps_transport, oldColumn, adjacent_ppm_backward]
  calc
    (adjacent_pps_split_matrix M 0 α h_alpha_nonneg h_beta_nonneg).entry i j.succ.succ =
        (adjacent_pps_split_matrix M 0 α h_alpha_nonneg h_beta_nonneg).entry i
          ((adjacent_pps_transport (0 : Fin (m + 1))).forward oldColumn).1 := by
            rw [h_forward]
    _ = M.entry i oldColumn.1 :=
        adjacent_pps_split_matrix_rest M 0 α h_alpha_nonneg h_beta_nonneg oldColumn i
    _ = M.entry i j.succ := by
        rfl

theorem adjacent_pps_split_matrix_is_singular {k m : Nat}
    (M : ConditionalProbabilityMatrix k m)
    (source : Fin m)
    (α : Probability)
    (h_singular : matrix_is_singular M)
    (h_alpha_nonneg : 0 ≤ α)
  (h_beta_nonneg : 0 ≤ 1 - α) :
    matrix_is_singular (adjacent_pps_split_matrix M source α h_alpha_nonneg h_beta_nonneg) := by
  intro j i₁ i₂ h_pos₁ h_pos₂
  by_cases h_left : j = source.castSucc
  · subst j
    have h_source₁ : 0 < M.entry i₁ source := by
      by_cases h_old : 0 < M.entry i₁ source
      · exact h_old
      · have h_zero : M.entry i₁ source = 0 :=
          Rat.le_antisymm (Rat.not_lt.mp h_old) (M.nonnegative i₁ source)
        rw [adjacent_pps_split_matrix_left M source α h_alpha_nonneg h_beta_nonneg i₁,
          h_zero, Rat.mul_zero] at h_pos₁
        simp at h_pos₁
    have h_source₂ : 0 < M.entry i₂ source := by
      by_cases h_old : 0 < M.entry i₂ source
      · exact h_old
      · have h_zero : M.entry i₂ source = 0 :=
          Rat.le_antisymm (Rat.not_lt.mp h_old) (M.nonnegative i₂ source)
        rw [adjacent_pps_split_matrix_left M source α h_alpha_nonneg h_beta_nonneg i₂,
          h_zero, Rat.mul_zero] at h_pos₂
        simp at h_pos₂
    calc
      (adjacent_pps_split_matrix M source α h_alpha_nonneg h_beta_nonneg).entry i₁ source.castSucc =
          α * M.entry i₁ source :=
            adjacent_pps_split_matrix_left M source α h_alpha_nonneg h_beta_nonneg i₁
      _ = α * M.entry i₂ source := by rw [h_singular source i₁ i₂ h_source₁ h_source₂]
      _ = (adjacent_pps_split_matrix M source α h_alpha_nonneg h_beta_nonneg).entry i₂ source.castSucc := by
            symm
            exact adjacent_pps_split_matrix_left M source α h_alpha_nonneg h_beta_nonneg i₂
  · by_cases h_right : j = source.succ
    · subst j
      have h_source₁ : 0 < M.entry i₁ source := by
        by_cases h_old : 0 < M.entry i₁ source
        · exact h_old
        · have h_zero : M.entry i₁ source = 0 :=
            Rat.le_antisymm (Rat.not_lt.mp h_old) (M.nonnegative i₁ source)
          rw [adjacent_pps_split_matrix_right M source α h_alpha_nonneg h_beta_nonneg i₁,
            h_zero, Rat.mul_zero] at h_pos₁
          simp at h_pos₁
      have h_source₂ : 0 < M.entry i₂ source := by
        by_cases h_old : 0 < M.entry i₂ source
        · exact h_old
        · have h_zero : M.entry i₂ source = 0 :=
            Rat.le_antisymm (Rat.not_lt.mp h_old) (M.nonnegative i₂ source)
          rw [adjacent_pps_split_matrix_right M source α h_alpha_nonneg h_beta_nonneg i₂,
            h_zero, Rat.mul_zero] at h_pos₂
          simp at h_pos₂
      calc
        (adjacent_pps_split_matrix M source α h_alpha_nonneg h_beta_nonneg).entry i₁ source.succ =
            (1 - α) * M.entry i₁ source :=
              adjacent_pps_split_matrix_right M source α h_alpha_nonneg h_beta_nonneg i₁
        _ = (1 - α) * M.entry i₂ source := by rw [h_singular source i₁ i₂ h_source₁ h_source₂]
        _ = (adjacent_pps_split_matrix M source α h_alpha_nonneg h_beta_nonneg).entry i₂ source.succ := by
              symm
              exact adjacent_pps_split_matrix_right M source α h_alpha_nonneg h_beta_nonneg i₂
    · let newColumn : ColumnsExceptPair source.castSucc source.succ := ⟨j, h_left, h_right⟩
      let oldColumn : ColumnsExceptOne source := (adjacent_pps_transport source).backward newColumn
      have h_j : ((adjacent_pps_transport source).forward oldColumn).1 = j := by
        simpa [adjacent_pps_transport, newColumn, oldColumn] using
          congrArg Subtype.val ((adjacent_pps_transport source).right_inv newColumn)
      have h_old₁ : 0 < M.entry i₁ oldColumn.1 := by
        have h_split : 0 < (adjacent_pps_split_matrix M source α h_alpha_nonneg h_beta_nonneg).entry i₁
            ((adjacent_pps_transport source).forward oldColumn).1 := by
          simpa [h_j] using h_pos₁
        rw [adjacent_pps_split_matrix_rest M source α h_alpha_nonneg h_beta_nonneg oldColumn i₁] at h_split
        exact h_split
      have h_old₂ : 0 < M.entry i₂ oldColumn.1 := by
        have h_split : 0 < (adjacent_pps_split_matrix M source α h_alpha_nonneg h_beta_nonneg).entry i₂
            ((adjacent_pps_transport source).forward oldColumn).1 := by
          simpa [h_j] using h_pos₂
        rw [adjacent_pps_split_matrix_rest M source α h_alpha_nonneg h_beta_nonneg oldColumn i₂] at h_split
        exact h_split
      calc
        (adjacent_pps_split_matrix M source α h_alpha_nonneg h_beta_nonneg).entry i₁ j =
            (adjacent_pps_split_matrix M source α h_alpha_nonneg h_beta_nonneg).entry i₁
              ((adjacent_pps_transport source).forward oldColumn).1 := by rw [h_j]
        _ = M.entry i₁ oldColumn.1 :=
            adjacent_pps_split_matrix_rest M source α h_alpha_nonneg h_beta_nonneg oldColumn i₁
        _ = M.entry i₂ oldColumn.1 := h_singular oldColumn.1 i₁ i₂ h_old₁ h_old₂
        _ = (adjacent_pps_split_matrix M source α h_alpha_nonneg h_beta_nonneg).entry i₂
              ((adjacent_pps_transport source).forward oldColumn).1 := by
              symm
              exact adjacent_pps_split_matrix_rest M source α h_alpha_nonneg h_beta_nonneg oldColumn i₂
        _ = (adjacent_pps_split_matrix M source α h_alpha_nonneg h_beta_nonneg).entry i₂ j := by rw [h_j]

def adjacent_ppm_merge_matrix {k n : Nat}
    (M : ConditionalProbabilityMatrix k (n + 1))
    (target : Fin n) :
    ConditionalProbabilityMatrix k n :=
  { entry := fun i j =>
      if h : j = target then
        M.entry i target.castSucc + M.entry i target.succ
      else
        M.entry i (adjacent_ppm_backward target ⟨j, h⟩).1
    nonnegative := by
      intro i j
      by_cases h : j = target
      · have h_left : 0 ≤ M.entry i target.castSucc := M.nonnegative i target.castSucc
        have h_right : 0 ≤ M.entry i target.succ := M.nonnegative i target.succ
        simp [h, Rat.add_nonneg h_left h_right]
      · simp [h, M.nonnegative i (adjacent_ppm_backward target ⟨j, h⟩).1] }

theorem adjacent_ppm_merge_matrix_target {k n : Nat}
    (M : ConditionalProbabilityMatrix k (n + 1))
    (target : Fin n)
    (i : Fin k) :
    (adjacent_ppm_merge_matrix M target).entry i target =
      M.entry i target.castSucc + M.entry i target.succ := by
  simp [adjacent_ppm_merge_matrix]

theorem adjacent_ppm_merge_matrix_rest {k n : Nat}
    (M : ConditionalProbabilityMatrix k (n + 1))
    (target : Fin n)
    (old : ColumnsExceptTwo target.castSucc target.succ)
    (i : Fin k) :
    (adjacent_ppm_merge_matrix M target).entry i ((adjacent_ppm_transport target).forward old).1 =
      M.entry i old.1 := by
  dsimp [adjacent_ppm_merge_matrix, adjacent_ppm_transport]
  rw [dif_neg ((adjacent_ppm_forward target old).2)]
  have hold : (adjacent_ppm_backward target (adjacent_ppm_forward target old)).1 = old.1 :=
    congrArg Subtype.val (adjacent_ppm_backward_forward target old)
  simpa using congrArg (fun j => M.entry i j) hold

theorem adjacent_ppm_merge_matrix_rest_pattern {k n : Nat}
    (M : ConditionalProbabilityMatrix k (n + 1))
    (target : Fin n)
    (old : ColumnsExceptTwo target.castSucc target.succ) :
    column_pattern (adjacent_ppm_merge_matrix M target)
        ((adjacent_ppm_transport target).forward old).1 =
      column_pattern M old.1 := by
  funext i
  by_cases h_pos : 0 < M.entry i old.1
  · have h_merge_pos :
        0 < (adjacent_ppm_merge_matrix M target).entry i
          ((adjacent_ppm_transport target).forward old).1 := by
      rw [adjacent_ppm_merge_matrix_rest M target old i]
      exact h_pos
    simp [column_pattern, h_pos, h_merge_pos]
  · have h_merge_not_pos :
        ¬ 0 < (adjacent_ppm_merge_matrix M target).entry i
          ((adjacent_ppm_transport target).forward old).1 := by
      rw [adjacent_ppm_merge_matrix_rest M target old i]
      exact h_pos
    simp [column_pattern, h_pos, h_merge_not_pos]

theorem adjacent_ppm_merge_matrix_target_by_pattern {k n : Nat}
    (M : ConditionalProbabilityMatrix k (n + 1))
    (target : Fin n)
    (h_singular : matrix_is_singular M)
    (h_pattern : column_pattern M target.castSucc = column_pattern M target.succ)
    (i : Fin k) :
    (adjacent_ppm_merge_matrix M target).entry i target =
      if column_pattern M target.castSucc i then
        column_value M target.castSucc + column_value M target.succ
      else 0 := by
  have h_pattern_i : column_pattern M target.castSucc i = column_pattern M target.succ i :=
    congrArg (fun f => f i) h_pattern
  calc
    (adjacent_ppm_merge_matrix M target).entry i target =
        M.entry i target.castSucc + M.entry i target.succ := by
          exact adjacent_ppm_merge_matrix_target M target i
    _ =
        (if column_pattern M target.castSucc i then column_value M target.castSucc else 0) +
          (if column_pattern M target.succ i then column_value M target.succ else 0) := by
            rw [entry_eq_column_value_or_zero M h_singular i target.castSucc,
              entry_eq_column_value_or_zero M h_singular i target.succ]
    _ =
        (if column_pattern M target.castSucc i then column_value M target.castSucc else 0) +
          (if column_pattern M target.castSucc i then column_value M target.succ else 0) := by
            rw [h_pattern_i]
    _ = if column_pattern M target.castSucc i then
          column_value M target.castSucc + column_value M target.succ
        else 0 := by
          by_cases h_col : column_pattern M target.castSucc i
          · simp [h_col]
          · simp [h_col, Rat.zero_add]

theorem adjacent_ppm_merge_matrix_target_pattern {k n : Nat}
    (M : ConditionalProbabilityMatrix k (n + 1))
    (target : Fin n)
    (h_singular : matrix_is_singular M)
    (h_pattern : column_pattern M target.castSucc = column_pattern M target.succ) :
    column_pattern (adjacent_ppm_merge_matrix M target) target =
      column_pattern M target.castSucc := by
  funext i
  by_cases h_col : column_pattern M target.castSucc i = true
  · have h_col_right : column_pattern M target.succ i = true := by
      simpa [h_col] using (congrArg (fun f => f i) h_pattern).symm
    have h_value_pos_left : 0 < column_value M target.castSucc :=
      column_value_positive_of_pattern_true M h_singular i target.castSucc h_col
    have h_value_pos_right : 0 < column_value M target.succ :=
      column_value_positive_of_pattern_true M h_singular i target.succ h_col_right
    have h_entry_pos : 0 < (adjacent_ppm_merge_matrix M target).entry i target := by
      rw [adjacent_ppm_merge_matrix_target_by_pattern M target h_singular h_pattern i, h_col]
      have h_lt_sum :
          column_value M target.castSucc <
            column_value M target.castSucc + column_value M target.succ := by
        simpa [Rat.add_zero] using
          (Rat.add_lt_add_left (c := column_value M target.castSucc)).2 h_value_pos_right
      calc
        0 < column_value M target.castSucc := h_value_pos_left
        _ < column_value M target.castSucc + column_value M target.succ := h_lt_sum
    rw [h_col]
    simp [column_pattern, h_entry_pos]
  · have h_entry_zero : (adjacent_ppm_merge_matrix M target).entry i target = 0 := by
      rw [adjacent_ppm_merge_matrix_target_by_pattern M target h_singular h_pattern i]
      simp [h_col]
    have h_not_pos : ¬ 0 < (adjacent_ppm_merge_matrix M target).entry i target := by
      rw [h_entry_zero]
      simp
    have h_col_false : column_pattern M target.castSucc i = false := by
      cases h_eq : column_pattern M target.castSucc i <;> simp [h_eq] at h_col ⊢
    rw [h_col_false]
    simp [column_pattern, h_not_pos]

theorem adjacent_ppm_merge_matrix_preserves_same_pattern {k n : Nat}
    (M : ConditionalProbabilityMatrix k (n + 1))
    (target : Fin n)
    (h_singular : matrix_is_singular M)
    (h_pattern : column_pattern M target.castSucc = column_pattern M target.succ)
    (old : ColumnsExceptTwo target.castSucc target.succ)
    (h_old_pattern : column_pattern M old.1 = column_pattern M target.castSucc) :
    column_pattern (adjacent_ppm_merge_matrix M target) target =
      column_pattern (adjacent_ppm_merge_matrix M target)
        ((adjacent_ppm_transport target).forward old).1 := by
  rw [adjacent_ppm_merge_matrix_target_pattern M target h_singular h_pattern,
    adjacent_ppm_merge_matrix_rest_pattern M target old,
    h_old_pattern]

theorem adjacent_ppm_merge_matrix_is_singular {k n : Nat}
    (M : ConditionalProbabilityMatrix k (n + 1))
    (target : Fin n)
    (h_singular : matrix_is_singular M)
    (h_pattern : column_pattern M target.castSucc = column_pattern M target.succ) :
    matrix_is_singular (adjacent_ppm_merge_matrix M target) := by
  intro j i₁ i₂ h_pos₁ h_pos₂
  by_cases h_target : j = target
  · subst j
    have h_target₁ := adjacent_ppm_merge_matrix_target_by_pattern M target h_singular h_pattern i₁
    have h_target₂ := adjacent_ppm_merge_matrix_target_by_pattern M target h_singular h_pattern i₂
    have h_col₁ : column_pattern M target.castSucc i₁ = true := by
      by_cases h_col : column_pattern M target.castSucc i₁
      · simpa using h_col
      · rw [h_target₁] at h_pos₁
        simp [h_col] at h_pos₁
    have h_col₂ : column_pattern M target.castSucc i₂ = true := by
      by_cases h_col : column_pattern M target.castSucc i₂
      · simpa using h_col
      · rw [h_target₂] at h_pos₂
        simp [h_col] at h_pos₂
    rw [h_target₁, h_col₁, h_target₂, h_col₂]
  · let newColumn : ColumnsExceptTarget target := ⟨j, h_target⟩
    let oldColumn : ColumnsExceptTwo target.castSucc target.succ := adjacent_ppm_backward target newColumn
    have h_j : ((adjacent_ppm_transport target).forward oldColumn).1 = j := by
      simpa [adjacent_ppm_transport, newColumn, oldColumn] using
        congrArg Subtype.val (adjacent_ppm_forward_backward target newColumn)
    have h_old₁ : 0 < M.entry i₁ oldColumn.1 := by
      have h_merge : 0 < (adjacent_ppm_merge_matrix M target).entry i₁ ((adjacent_ppm_transport target).forward oldColumn).1 := by
        simpa [h_j] using h_pos₁
      rw [adjacent_ppm_merge_matrix_rest M target oldColumn i₁] at h_merge
      exact h_merge
    have h_old₂ : 0 < M.entry i₂ oldColumn.1 := by
      have h_merge : 0 < (adjacent_ppm_merge_matrix M target).entry i₂ ((adjacent_ppm_transport target).forward oldColumn).1 := by
        simpa [h_j] using h_pos₂
      rw [adjacent_ppm_merge_matrix_rest M target oldColumn i₂] at h_merge
      exact h_merge
    calc
      (adjacent_ppm_merge_matrix M target).entry i₁ j =
          (adjacent_ppm_merge_matrix M target).entry i₁ ((adjacent_ppm_transport target).forward oldColumn).1 := by
            rw [h_j]
      _ = M.entry i₁ oldColumn.1 := adjacent_ppm_merge_matrix_rest M target oldColumn i₁
      _ = M.entry i₂ oldColumn.1 := h_singular oldColumn.1 i₁ i₂ h_old₁ h_old₂
      _ = (adjacent_ppm_merge_matrix M target).entry i₂ ((adjacent_ppm_transport target).forward oldColumn).1 := by
            symm
            exact adjacent_ppm_merge_matrix_rest M target oldColumn i₂
      _ = (adjacent_ppm_merge_matrix M target).entry i₂ j := by
            rw [h_j]

def ordered_vpm_target {n : Nat}
    (left right : Fin (n + 1))
    (h_lt : left.1 < right.1) : Fin n :=
  ⟨left.1, by omega⟩

def ordered_vpm_forward {n : Nat}
    (left right : Fin (n + 1))
    (h_lt : left.1 < right.1)
    (j : ColumnsExceptTwo left right) :
    ColumnsExceptTarget (ordered_vpm_target left right h_lt) :=
  if h_before : j.1.1 < right.1 then
    ⟨⟨j.1.1, by omega⟩, by
      intro h_eq
      have h_val : j.1.1 = left.1 := by
        simpa [ordered_vpm_target] using congrArg Fin.val h_eq
      apply j.2.1
      apply Fin.ext
      simpa using h_val⟩
  else
    have h_after : right.1 < j.1.1 := by
      have h_ne_right_val : j.1.1 ≠ right.1 := by
        intro h
        apply j.2.2
        apply Fin.ext
        simpa using h
      omega
    ⟨⟨j.1.1 - 1, by omega⟩, by
      intro h_eq
      have h_val : j.1.1 - 1 = left.1 := by
        simpa [ordered_vpm_target] using congrArg Fin.val h_eq
      omega⟩

def ordered_vpm_backward {n : Nat}
    (left right : Fin (n + 1))
    (h_lt : left.1 < right.1)
    (j : ColumnsExceptTarget (ordered_vpm_target left right h_lt)) :
    ColumnsExceptTwo left right :=
  if h_before : j.1.1 < right.1 then
    ⟨j.1.castSucc, by
      constructor
      · intro h_eq
        apply j.2
        apply Fin.ext
        simpa [ordered_vpm_target] using congrArg Fin.val h_eq
      · intro h_eq
        have h_val : j.1.1 = right.1 := by
          simpa using congrArg Fin.val h_eq
        omega⟩
  else
    ⟨j.1.succ, by
      constructor
      · intro h_eq
        have h_val : j.1.1 + 1 = left.1 := by
          simpa using congrArg Fin.val h_eq
        omega
      · intro h_eq
        have h_val : j.1.1 + 1 = right.1 := by
          simpa using congrArg Fin.val h_eq
        omega⟩

theorem ordered_vpm_backward_forward {n : Nat}
    (left right : Fin (n + 1))
    (h_lt : left.1 < right.1)
    (j : ColumnsExceptTwo left right) :
    ordered_vpm_backward left right h_lt (ordered_vpm_forward left right h_lt j) = j := by
  rcases j with ⟨j, h_ne_left, h_ne_right⟩
  by_cases h_before : j.1 < right.1
  · apply Subtype.ext
    apply Fin.ext
    dsimp [ordered_vpm_forward, ordered_vpm_backward]
    rw [dif_pos h_before, dif_pos h_before]
    rfl
  · have h_after : right.1 < j.1 := by
      have h_ne_right_val : right.1 ≠ j.1 := by
        intro h
        apply h_ne_right
        apply Fin.ext
        simpa using h.symm
      omega
    have h_before' : ¬ j.1 - 1 < right.1 := by
      omega
    have hj_ge : 1 ≤ j.1 := by
      omega
    apply Subtype.ext
    apply Fin.ext
    dsimp [ordered_vpm_forward, ordered_vpm_backward]
    rw [dif_neg h_before, dif_neg h_before']
    simpa using Nat.sub_add_cancel hj_ge

theorem ordered_vpm_forward_backward {n : Nat}
    (left right : Fin (n + 1))
    (h_lt : left.1 < right.1)
    (j : ColumnsExceptTarget (ordered_vpm_target left right h_lt)) :
    ordered_vpm_forward left right h_lt (ordered_vpm_backward left right h_lt j) = j := by
  rcases j with ⟨j, h_ne_target⟩
  by_cases h_before : j.1 < right.1
  · apply Subtype.ext
    apply Fin.ext
    have h_cast : (j.castSucc : Fin (n + 1)).1 < right.1 := by
      simpa using h_before
    dsimp [ordered_vpm_backward, ordered_vpm_forward]
    rw [dif_pos h_before, dif_pos h_cast]
    rfl
  · have h_right_le : right.1 ≤ j.1 := Nat.not_lt.mp h_before
    have h_succ : ¬ (j.succ : Fin (n + 1)).1 < right.1 := by
      exact Nat.not_lt.mpr (Nat.le_trans h_right_le (Nat.le_succ j.1))
    apply Subtype.ext
    apply Fin.ext
    dsimp [ordered_vpm_backward, ordered_vpm_forward]
    rw [dif_neg h_before, dif_neg h_succ]
    simp

def ordered_vpm_transport {n : Nat}
    (left right : Fin (n + 1))
    (h_lt : left.1 < right.1) :
    ColumnTransport (ColumnsExceptTwo left right)
      (ColumnsExceptTarget (ordered_vpm_target left right h_lt)) :=
  { forward := ordered_vpm_forward left right h_lt
    backward := ordered_vpm_backward left right h_lt
    left_inv := ordered_vpm_backward_forward left right h_lt
    right_inv := ordered_vpm_forward_backward left right h_lt }

def ordered_vpm_merge_matrix {k n : Nat}
    (M : ConditionalProbabilityMatrix k (n + 1))
    (left right : Fin (n + 1))
    (h_lt : left.1 < right.1) :
    ConditionalProbabilityMatrix k n :=
  { entry := fun i j =>
      if h : j = ordered_vpm_target left right h_lt then
        M.entry i left + M.entry i right
      else
        M.entry i (ordered_vpm_backward left right h_lt ⟨j, h⟩).1
    nonnegative := by
      intro i j
      by_cases h : j = ordered_vpm_target left right h_lt
      · have h_left : 0 ≤ M.entry i left := M.nonnegative i left
        have h_right : 0 ≤ M.entry i right := M.nonnegative i right
        simp [h, Rat.add_nonneg h_left h_right]
      · simp [h, M.nonnegative i (ordered_vpm_backward left right h_lt ⟨j, h⟩).1] }

theorem ordered_vpm_merge_matrix_target {k n : Nat}
    (M : ConditionalProbabilityMatrix k (n + 1))
    (left right : Fin (n + 1))
    (h_lt : left.1 < right.1)
    (i : Fin k) :
    (ordered_vpm_merge_matrix M left right h_lt).entry i (ordered_vpm_target left right h_lt) =
      M.entry i left + M.entry i right := by
  simp [ordered_vpm_merge_matrix]

theorem ordered_vpm_merge_matrix_rest {k n : Nat}
    (M : ConditionalProbabilityMatrix k (n + 1))
    (left right : Fin (n + 1))
    (h_lt : left.1 < right.1)
    (old : ColumnsExceptTwo left right)
    (i : Fin k) :
    (ordered_vpm_merge_matrix M left right h_lt).entry i
        ((ordered_vpm_transport left right h_lt).forward old).1 =
      M.entry i old.1 := by
  dsimp [ordered_vpm_merge_matrix, ordered_vpm_transport]
  rw [dif_neg ((ordered_vpm_forward left right h_lt old).2)]
  have hold :
      (ordered_vpm_backward left right h_lt (ordered_vpm_forward left right h_lt old)).1 = old.1 :=
    congrArg Subtype.val (ordered_vpm_backward_forward left right h_lt old)
  simpa using congrArg (fun j => M.entry i j) hold

theorem ordered_vpm_merge_matrix_target_value {k n : Nat}
    (M : ConditionalProbabilityMatrix k (n + 1))
    (left right : Fin (n + 1))
    (h_lt : left.1 < right.1)
    (h_singular : matrix_is_singular M)
    (h_value : column_value M left = column_value M right)
    (h_disjoint : ∀ i : Fin k, 0 < M.entry i left → M.entry i right = 0)
    (i : Fin k)
    (h_pos : 0 < (ordered_vpm_merge_matrix M left right h_lt).entry i (ordered_vpm_target left right h_lt)) :
    (ordered_vpm_merge_matrix M left right h_lt).entry i (ordered_vpm_target left right h_lt) =
      column_value M left := by
  by_cases h_left_pos : 0 < M.entry i left
  · have h_right_zero : M.entry i right = 0 := h_disjoint i h_left_pos
    have h_left_eq : M.entry i left = column_value M left := by
      rw [entry_eq_column_value_or_zero M h_singular i left,
        show column_pattern M left i = true by simp [column_pattern, h_left_pos]]
      simp
    calc
      (ordered_vpm_merge_matrix M left right h_lt).entry i (ordered_vpm_target left right h_lt)
          = M.entry i left + M.entry i right := by
              exact ordered_vpm_merge_matrix_target M left right h_lt i
      _ = column_value M left + 0 := by rw [h_left_eq, h_right_zero]
      _ = column_value M left := by rw [Rat.add_zero]
  · have h_left_zero : M.entry i left = 0 := by
      exact Rat.le_antisymm (Rat.not_lt.mp h_left_pos) (M.nonnegative i left)
    have h_right_pos : 0 < M.entry i right := by
      rw [ordered_vpm_merge_matrix_target M left right h_lt i, h_left_zero, Rat.zero_add] at h_pos
      exact h_pos
    have h_right_eq : M.entry i right = column_value M right := by
      rw [entry_eq_column_value_or_zero M h_singular i right,
        show column_pattern M right i = true by simp [column_pattern, h_right_pos]]
      simp
    calc
      (ordered_vpm_merge_matrix M left right h_lt).entry i (ordered_vpm_target left right h_lt)
          = M.entry i left + M.entry i right := by
              exact ordered_vpm_merge_matrix_target M left right h_lt i
      _ = 0 + column_value M right := by rw [h_left_zero, h_right_eq]
      _ = column_value M right := by rw [Rat.zero_add]
      _ = column_value M left := by rw [← h_value]

theorem ordered_vpm_merge_matrix_is_singular {k n : Nat}
    (M : ConditionalProbabilityMatrix k (n + 1))
    (left right : Fin (n + 1))
    (h_lt : left.1 < right.1)
    (h_singular : matrix_is_singular M)
    (h_value : column_value M left = column_value M right)
    (h_disjoint : ∀ i : Fin k, 0 < M.entry i left → M.entry i right = 0) :
    matrix_is_singular (ordered_vpm_merge_matrix M left right h_lt) := by
  intro j i₁ i₂ h_pos₁ h_pos₂
  by_cases h_target : j = ordered_vpm_target left right h_lt
  · subst j
    rw [ordered_vpm_merge_matrix_target_value M left right h_lt h_singular h_value h_disjoint i₁ h_pos₁,
      ordered_vpm_merge_matrix_target_value M left right h_lt h_singular h_value h_disjoint i₂ h_pos₂]
  · let newColumn : ColumnsExceptTarget (ordered_vpm_target left right h_lt) := ⟨j, h_target⟩
    let oldColumn : ColumnsExceptTwo left right := ordered_vpm_backward left right h_lt newColumn
    have h_j : ((ordered_vpm_transport left right h_lt).forward oldColumn).1 = j := by
      simpa [ordered_vpm_transport, newColumn, oldColumn] using
        congrArg Subtype.val (ordered_vpm_forward_backward left right h_lt newColumn)
    have h_old₁ : 0 < M.entry i₁ oldColumn.1 := by
      have h_merge : 0 < (ordered_vpm_merge_matrix M left right h_lt).entry i₁
          ((ordered_vpm_transport left right h_lt).forward oldColumn).1 := by
        simpa [h_j] using h_pos₁
      rw [ordered_vpm_merge_matrix_rest M left right h_lt oldColumn i₁] at h_merge
      exact h_merge
    have h_old₂ : 0 < M.entry i₂ oldColumn.1 := by
      have h_merge : 0 < (ordered_vpm_merge_matrix M left right h_lt).entry i₂
          ((ordered_vpm_transport left right h_lt).forward oldColumn).1 := by
        simpa [h_j] using h_pos₂
      rw [ordered_vpm_merge_matrix_rest M left right h_lt oldColumn i₂] at h_merge
      exact h_merge
    calc
      (ordered_vpm_merge_matrix M left right h_lt).entry i₁ j =
          (ordered_vpm_merge_matrix M left right h_lt).entry i₁
            ((ordered_vpm_transport left right h_lt).forward oldColumn).1 := by
              rw [h_j]
      _ = M.entry i₁ oldColumn.1 := ordered_vpm_merge_matrix_rest M left right h_lt oldColumn i₁
      _ = M.entry i₂ oldColumn.1 := h_singular oldColumn.1 i₁ i₂ h_old₁ h_old₂
      _ = (ordered_vpm_merge_matrix M left right h_lt).entry i₂
            ((ordered_vpm_transport left right h_lt).forward oldColumn).1 := by
              symm
              exact ordered_vpm_merge_matrix_rest M left right h_lt oldColumn i₂
      _ = (ordered_vpm_merge_matrix M left right h_lt).entry i₂ j := by
              rw [h_j]

def one_vector_matrix (k : Nat) : ConditionalProbabilityMatrix k 1 :=
  { entry := fun _ _ => 1
    nonnegative := by
      intro _ _
      decide }

-- Matrix operations record exact pointwise entry transformations.
def is_pps_operation {k m n : Nat}
    (M : ConditionalProbabilityMatrix k m) (M' : ConditionalProbabilityMatrix k n) : Prop :=
  matrix_is_singular M ∧
    matrix_is_singular M' ∧
    n = m + 1 ∧
    ∃ source : Fin m, ∃ α : Probability,
      0 < α ∧
      α < 1 ∧
      ∃ left right : Fin n,
        left ≠ right ∧
        left.val + 1 = right.val ∧
        ∃ transport : ColumnTransport (ColumnsExceptOne source) (ColumnsExceptPair left right),
          (∀ i : Fin k, M'.entry i left = α * M.entry i source) ∧
          (∀ i : Fin k, M'.entry i right = (1 - α) * M.entry i source) ∧
          (∀ j : ColumnsExceptOne source, ∀ i : Fin k,
            M'.entry i (transport.forward j).1 = M.entry i j.1)

def is_ppm_operation {k m n : Nat}
    (M : ConditionalProbabilityMatrix k m) (M' : ConditionalProbabilityMatrix k n) : Prop :=
  matrix_is_singular M ∧
    matrix_is_singular M' ∧
    m = n + 1 ∧
    ∃ source₁ source₂ : Fin m,
      source₁ ≠ source₂ ∧
      column_pattern M source₁ = column_pattern M source₂ ∧
      ∃ target : Fin n,
        target.val = Nat.min source₁.val source₂.val ∧
        ∃ transport : ColumnTransport (ColumnsExceptTwo source₁ source₂) (ColumnsExceptTarget target),
          (∀ i : Fin k, M'.entry i target = M.entry i source₁ + M.entry i source₂) ∧
          (∀ j : ColumnsExceptTwo source₁ source₂, ∀ i : Fin k,
            M'.entry i (transport.forward j).1 = M.entry i j.1)

def is_vps_operation {k m n : Nat}
    (M : ConditionalProbabilityMatrix k m) (M' : ConditionalProbabilityMatrix k n) : Prop :=
  matrix_is_singular M ∧
    matrix_is_singular M' ∧
    n = m + 1 ∧
    ∃ source : Fin m, ∃ splitter : Fin k → Bool,
      ∃ left right : Fin n,
        left ≠ right ∧
        left.val + 1 = right.val ∧
        ∃ transport : ColumnTransport (ColumnsExceptOne source) (ColumnsExceptPair left right),
          (∀ i : Fin k, M'.entry i left = if splitter i then M.entry i source else 0) ∧
          (∀ i : Fin k, M'.entry i right = if splitter i then 0 else M.entry i source) ∧
          (∀ j : ColumnsExceptOne source, ∀ i : Fin k,
            M'.entry i (transport.forward j).1 = M.entry i j.1)

def is_vpm_operation {k m n : Nat}
    (M : ConditionalProbabilityMatrix k m) (M' : ConditionalProbabilityMatrix k n) : Prop :=
  matrix_is_singular M ∧
    matrix_is_singular M' ∧
    m = n + 1 ∧
    ∃ source₁ source₂ : Fin m,
      source₁ ≠ source₂ ∧
      column_value M source₁ = column_value M source₂ ∧
      (∀ i : Fin k,
        0 < M.entry i source₁ → M.entry i source₂ = 0) ∧
      ∃ target : Fin n,
        target.val = Nat.min source₁.val source₂.val ∧
        ∃ transport : ColumnTransport (ColumnsExceptTwo source₁ source₂) (ColumnsExceptTarget target),
          (∀ i : Fin k, M'.entry i target = M.entry i source₁ + M.entry i source₂) ∧
          (∀ j : ColumnsExceptTwo source₁ source₂, ∀ i : Fin k,
            M'.entry i (transport.forward j).1 = M.entry i j.1)

theorem ordered_vpm_merge_is_vpm_operation {k n : Nat}
    (M : ConditionalProbabilityMatrix k (n + 1))
    (left right : Fin (n + 1))
    (h_lt : left.1 < right.1)
    (h_singular : matrix_is_singular M)
    (h_value : column_value M left = column_value M right)
    (h_disjoint : ∀ i : Fin k, 0 < M.entry i left → M.entry i right = 0) :
    is_vpm_operation M (ordered_vpm_merge_matrix M left right h_lt) := by
  refine ⟨h_singular,
    ordered_vpm_merge_matrix_is_singular M left right h_lt h_singular h_value h_disjoint,
    rfl, left, right, ?_, h_value, h_disjoint, ordered_vpm_target left right h_lt, ?_,
    ordered_vpm_transport left right h_lt, ?_, ?_⟩
  · intro h_eq
    have h_val : left.1 = right.1 := by
      simpa using congrArg Fin.val h_eq
    omega
  · simp [ordered_vpm_target, Nat.min_eq_left (Nat.le_of_lt h_lt)]
  · intro i
    exact ordered_vpm_merge_matrix_target M left right h_lt i
  · intro old i
    exact ordered_vpm_merge_matrix_rest M left right h_lt old i

theorem adjacent_ppm_merge_is_ppm_operation {k n : Nat}
    (M : ConditionalProbabilityMatrix k (n + 1))
    (target : Fin n)
    (h_singular : matrix_is_singular M)
    (h_pattern : column_pattern M target.castSucc = column_pattern M target.succ) :
    is_ppm_operation M (adjacent_ppm_merge_matrix M target) := by
  refine ⟨h_singular, adjacent_ppm_merge_matrix_is_singular M target h_singular h_pattern,
    rfl, target.castSucc, target.succ, ?_, h_pattern, target, ?_, adjacent_ppm_transport target, ?_, ?_⟩
  · intro h_eq
    have h_val : target.1 = target.1 + 1 := by
      simpa using congrArg Fin.val h_eq
    omega
  · simp
  · intro i
    exact adjacent_ppm_merge_matrix_target M target i
  · intro old i
    exact adjacent_ppm_merge_matrix_rest M target old i

abbrev MatrixState (k : Nat) := Sigma (ConditionalProbabilityMatrix k)

theorem MatrixState.cast_eq {k m n : Nat}
    (M : ConditionalProbabilityMatrix k m)
    (h : m = n) :
    (⟨n, M.cast h⟩ : MatrixState k) = ⟨m, M⟩ := by
  cases h
  simp [ConditionalProbabilityMatrix.cast_rfl]

inductive MatrixReachable {k : Nat} (step : MatrixState k → MatrixState k → Prop) :
    MatrixState k → MatrixState k → Prop where
  | refl (state : MatrixState k) : MatrixReachable step state state
  | tail {start next finish : MatrixState k} :
      step start next →
      MatrixReachable step next finish →
      MatrixReachable step start finish

theorem MatrixReachable.trans {k : Nat}
  {step : MatrixState k → MatrixState k → Prop}
  {start middle finish : MatrixState k}
  (h_left : MatrixReachable step start middle)
  (h_right : MatrixReachable step middle finish) :
  MatrixReachable step start finish := by
  induction h_left generalizing finish with
  | refl state =>
    simpa using h_right
  | @tail start next middle h_step h_tail ih =>
    exact MatrixReachable.tail h_step (ih h_right)

theorem MatrixReachable.single {k : Nat}
  {step : MatrixState k → MatrixState k → Prop}
  {start finish : MatrixState k}
  (h_step : step start finish) :
  MatrixReachable step start finish := by
  exact MatrixReachable.tail h_step (MatrixReachable.refl finish)

def pps_step {k : Nat} : MatrixState k → MatrixState k → Prop
  | ⟨_, M⟩, ⟨_, M'⟩ => is_pps_operation M M'

def vps_step {k : Nat} : MatrixState k → MatrixState k → Prop
  | ⟨_, M⟩, ⟨_, M'⟩ => is_vps_operation M M'

def ppm_step {k : Nat} : MatrixState k → MatrixState k → Prop
  | ⟨_, M⟩, ⟨_, M'⟩ => is_ppm_operation M M'

def vpm_step {k : Nat} : MatrixState k → MatrixState k → Prop
  | ⟨_, M⟩, ⟨_, M'⟩ => is_vpm_operation M M'

def pps_vps_ppm_step {k : Nat} : MatrixState k → MatrixState k → Prop
  | start, finish =>
      pps_step start finish ∨ vps_step start finish ∨ ppm_step start finish

def pps_ppm_vpm_step {k : Nat} : MatrixState k → MatrixState k → Prop
  | start, finish =>
      pps_step start finish ∨ ppm_step start finish ∨ vpm_step start finish

theorem adjacent_ppm_merge_reachable_by_ppm {k n : Nat}
    (M : ConditionalProbabilityMatrix k (n + 1))
    (target : Fin n)
    (h_singular : matrix_is_singular M)
    (h_pattern : column_pattern M target.castSucc = column_pattern M target.succ) :
    MatrixReachable (ppm_step (k := k))
      ⟨n + 1, M⟩ ⟨n, adjacent_ppm_merge_matrix M target⟩ := by
  apply MatrixReachable.single
  dsimp [ppm_step]
  exact adjacent_ppm_merge_is_ppm_operation M target h_singular h_pattern

theorem adjacent_ppm_merge_reachable_by_pps_ppm_vpm {k n : Nat}
    (M : ConditionalProbabilityMatrix k (n + 1))
    (target : Fin n)
    (h_singular : matrix_is_singular M)
    (h_pattern : column_pattern M target.castSucc = column_pattern M target.succ) :
    MatrixReachable (pps_ppm_vpm_step (k := k))
      ⟨n + 1, M⟩ ⟨n, adjacent_ppm_merge_matrix M target⟩ := by
  apply MatrixReachable.single
  dsimp [pps_ppm_vpm_step, pps_step, ppm_step, vpm_step]
  exact Or.inr (Or.inl (adjacent_ppm_merge_is_ppm_operation M target h_singular h_pattern))

theorem one_sub_nonneg_of_lt_one (α : Probability) (h_alpha_lt_one : α < 1) :
    0 ≤ 1 - α := by
  apply Rat.not_lt.mp
  intro h_neg
  have h_add : (1 - α) + α < 0 + α :=
    (Rat.add_lt_add_right (c := α)).2 h_neg
  have h_contra : 1 < α := by
    calc
      1 = (1 - α) + α := by
            rw [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.neg_add_cancel, Rat.add_zero]
      _ < 0 + α := h_add
      _ = α := Rat.zero_add α
  exact (Rat.not_lt.mpr (Rat.le_of_lt h_alpha_lt_one)) h_contra

theorem adjacent_pps_split_is_pps_operation {k m : Nat}
    (M : ConditionalProbabilityMatrix k m)
    (source : Fin m)
    (α : Probability)
    (h_singular : matrix_is_singular M)
    (h_alpha_pos : 0 < α)
    (h_alpha_lt_one : α < 1) :
    is_pps_operation M
      (adjacent_pps_split_matrix M source α (Rat.le_of_lt h_alpha_pos)
        (one_sub_nonneg_of_lt_one α h_alpha_lt_one)) := by
  let h_beta_nonneg : 0 ≤ 1 - α := one_sub_nonneg_of_lt_one α h_alpha_lt_one
  refine ⟨h_singular,
    adjacent_pps_split_matrix_is_singular M source α h_singular
      (Rat.le_of_lt h_alpha_pos) h_beta_nonneg,
    rfl, source, α, h_alpha_pos, h_alpha_lt_one,
    source.castSucc, source.succ, ?_, ?_, adjacent_pps_transport source, ?_, ?_, ?_⟩
  · intro h_eq
    have h_val : source.1 = source.1 + 1 := by
      simpa using congrArg Fin.val h_eq
    omega
  · simp
  · intro i
    exact adjacent_pps_split_matrix_left M source α (Rat.le_of_lt h_alpha_pos) h_beta_nonneg i
  · intro i
    exact adjacent_pps_split_matrix_right M source α (Rat.le_of_lt h_alpha_pos) h_beta_nonneg i
  · intro old i
    exact adjacent_pps_split_matrix_rest M source α (Rat.le_of_lt h_alpha_pos) h_beta_nonneg old i

theorem adjacent_pps_split_reachable_by_pps {k m : Nat}
    (M : ConditionalProbabilityMatrix k m)
    (source : Fin m)
    (α : Probability)
    (h_singular : matrix_is_singular M)
    (h_alpha_pos : 0 < α)
    (h_alpha_lt_one : α < 1) :
    MatrixReachable (pps_step (k := k))
      ⟨m, M⟩
      ⟨m + 1,
        adjacent_pps_split_matrix M source α (Rat.le_of_lt h_alpha_pos)
          (one_sub_nonneg_of_lt_one α h_alpha_lt_one)⟩ := by
  apply MatrixReachable.single
  dsimp [pps_step]
  exact adjacent_pps_split_is_pps_operation M source α h_singular h_alpha_pos h_alpha_lt_one

theorem adjacent_pps_split_reachable_by_pps_ppm_vpm {k m : Nat}
    (M : ConditionalProbabilityMatrix k m)
    (source : Fin m)
    (α : Probability)
    (h_singular : matrix_is_singular M)
    (h_alpha_pos : 0 < α)
    (h_alpha_lt_one : α < 1) :
    MatrixReachable (pps_ppm_vpm_step (k := k))
      ⟨m, M⟩
      ⟨m + 1,
        adjacent_pps_split_matrix M source α (Rat.le_of_lt h_alpha_pos)
          (one_sub_nonneg_of_lt_one α h_alpha_lt_one)⟩ := by
  apply MatrixReachable.single
  dsimp [pps_ppm_vpm_step, pps_step, ppm_step, vpm_step]
  exact Or.inl
    (adjacent_pps_split_is_pps_operation M source α h_singular h_alpha_pos h_alpha_lt_one)

def massMatrix (k n : Nat)
    (mass : Fin n → Probability)
    (h_nonneg : ∀ j : Fin n, 0 ≤ mass j) :
    ConditionalProbabilityMatrix k n :=
  { entry := fun _ j => mass j
    nonnegative := by
      intro _ j
      exact h_nonneg j }

theorem massMatrix_entry_eq {k n : Nat}
    (mass : Fin n → Probability)
    (h_nonneg : ∀ j : Fin n, 0 ≤ mass j)
    (i : Fin k) (j : Fin n) :
    (massMatrix k n mass h_nonneg).entry i j = mass j := by
  rfl

theorem massMatrix_is_singular {k n : Nat}
    (mass : Fin n → Probability)
    (h_nonneg : ∀ j : Fin n, 0 ≤ mass j) :
    matrix_is_singular (massMatrix k n mass h_nonneg) := by
  intro j i₁ i₂ _ _
  rfl

theorem massMatrix_column_pattern_true {k n : Nat}
    (mass : Fin n → Probability)
    (h_nonneg : ∀ j : Fin n, 0 ≤ mass j)
    (h_pos : ∀ j : Fin n, 0 < mass j)
    (j : Fin n) :
    column_pattern (massMatrix k n mass h_nonneg) j = fun _ => true := by
  funext i
  have h_entry : 0 < (massMatrix k n mass h_nonneg).entry i j := by
    simpa [massMatrix] using h_pos j
  simp [column_pattern, h_entry]

def prependSourceMassMatrix {k m n : Nat}
    (M : ConditionalProbabilityMatrix k (m + 1))
    (mass : Fin (n + 1) → Probability)
    (h_nonneg : ∀ j : Fin (n + 1), 0 ≤ mass j) :
    ConditionalProbabilityMatrix k (n + m + 1) :=
  { entry := fun i j =>
      if h_head : j.1 < n + 1 then
        mass ⟨j.1, h_head⟩ * M.entry i 0
      else
        M.entry i ((excludeOne_backward (0 : Fin (m + 1)) ⟨j.1 - (n + 1), by omega⟩).1)
    nonnegative := by
      intro i j
      by_cases h_head : j.1 < n + 1
      · dsimp
        rw [dif_pos h_head]
        exact Rat.mul_nonneg (h_nonneg ⟨j.1, h_head⟩) (M.nonnegative i 0)
      · dsimp
        rw [dif_neg h_head]
        exact M.nonnegative i
          ((excludeOne_backward (0 : Fin (m + 1)) ⟨j.1 - (n + 1), by omega⟩).1) }

theorem prependSourceMassMatrix_entry_of_lt {k m n : Nat}
    (M : ConditionalProbabilityMatrix k (m + 1))
    (mass : Fin (n + 1) → Probability)
    (h_nonneg : ∀ j : Fin (n + 1), 0 ≤ mass j)
    (i : Fin k)
    (j : Fin (n + m + 1))
    (h_head : j.1 < n + 1) :
    (prependSourceMassMatrix M mass h_nonneg).entry i j =
      mass ⟨j.1, h_head⟩ * M.entry i 0 := by
  simp [prependSourceMassMatrix, h_head]

theorem prependSourceMassMatrix_entry_of_ge {k m n : Nat}
    (M : ConditionalProbabilityMatrix k (m + 1))
    (mass : Fin (n + 1) → Probability)
    (h_nonneg : ∀ j : Fin (n + 1), 0 ≤ mass j)
    (i : Fin k)
    (j : Fin (n + m + 1))
    (h_head : ¬ j.1 < n + 1) :
    (prependSourceMassMatrix M mass h_nonneg).entry i j =
      M.entry i ((excludeOne_backward (0 : Fin (m + 1)) ⟨j.1 - (n + 1), by omega⟩).1) := by
  simp [prependSourceMassMatrix, h_head]

theorem prependSourceMassMatrix_is_singular {k m n : Nat}
    (M : ConditionalProbabilityMatrix k (m + 1))
    (mass : Fin (n + 1) → Probability)
    (h_nonneg : ∀ j : Fin (n + 1), 0 ≤ mass j)
    (h_singular : matrix_is_singular M) :
    matrix_is_singular (prependSourceMassMatrix M mass h_nonneg) := by
  intro j i₁ i₂ h_pos₁ h_pos₂
  by_cases h_head : j.1 < n + 1
  · let head : Fin (n + 1) := ⟨j.1, h_head⟩
    have h_source₁ : 0 < M.entry i₁ 0 := by
      by_cases h_old : 0 < M.entry i₁ 0
      · exact h_old
      · have h_zero : M.entry i₁ 0 = 0 :=
          Rat.le_antisymm (Rat.not_lt.mp h_old) (M.nonnegative i₁ 0)
        rw [prependSourceMassMatrix_entry_of_lt M mass h_nonneg i₁ j h_head,
          h_zero, Rat.mul_zero] at h_pos₁
        simp at h_pos₁
    have h_source₂ : 0 < M.entry i₂ 0 := by
      by_cases h_old : 0 < M.entry i₂ 0
      · exact h_old
      · have h_zero : M.entry i₂ 0 = 0 :=
          Rat.le_antisymm (Rat.not_lt.mp h_old) (M.nonnegative i₂ 0)
        rw [prependSourceMassMatrix_entry_of_lt M mass h_nonneg i₂ j h_head,
          h_zero, Rat.mul_zero] at h_pos₂
        simp at h_pos₂
    calc
      (prependSourceMassMatrix M mass h_nonneg).entry i₁ j =
          mass head * M.entry i₁ 0 := by
            exact prependSourceMassMatrix_entry_of_lt M mass h_nonneg i₁ j h_head
      _ = mass head * M.entry i₂ 0 := by
            rw [h_singular 0 i₁ i₂ h_source₁ h_source₂]
      _ = (prependSourceMassMatrix M mass h_nonneg).entry i₂ j := by
            symm
            exact prependSourceMassMatrix_entry_of_lt M mass h_nonneg i₂ j h_head
  · let old : Fin (m + 1) :=
      (excludeOne_backward (0 : Fin (m + 1)) ⟨j.1 - (n + 1), by omega⟩).1
    have h_old₁ : 0 < M.entry i₁ old := by
      rw [prependSourceMassMatrix_entry_of_ge M mass h_nonneg i₁ j h_head] at h_pos₁
      simpa [old] using h_pos₁
    have h_old₂ : 0 < M.entry i₂ old := by
      rw [prependSourceMassMatrix_entry_of_ge M mass h_nonneg i₂ j h_head] at h_pos₂
      simpa [old] using h_pos₂
    calc
      (prependSourceMassMatrix M mass h_nonneg).entry i₁ j = M.entry i₁ old := by
        simpa [old] using prependSourceMassMatrix_entry_of_ge M mass h_nonneg i₁ j h_head
      _ = M.entry i₂ old := h_singular old i₁ i₂ h_old₁ h_old₂
      _ = (prependSourceMassMatrix M mass h_nonneg).entry i₂ j := by
            symm
            simpa [old] using prependSourceMassMatrix_entry_of_ge M mass h_nonneg i₂ j h_head

theorem prependSourceMassMatrix_head {k m n : Nat}
    (M : ConditionalProbabilityMatrix k (m + 1))
    (mass : Fin (n + 1) → Probability)
    (h_nonneg : ∀ j : Fin (n + 1), 0 ≤ mass j)
    (i : Fin k)
    (j : Fin (n + 1)) :
    (prependSourceMassMatrix M mass h_nonneg).entry i ⟨j.1, by omega⟩ =
      mass j * M.entry i 0 := by
  have h_head : (⟨j.1, by omega⟩ : Fin (n + m + 1)).1 < n + 1 := by
    simp [j.2]
  exact prependSourceMassMatrix_entry_of_lt M mass h_nonneg i ⟨j.1, by omega⟩ h_head

theorem prependSourceMassMatrix_tail {k m n : Nat}
    (M : ConditionalProbabilityMatrix k (m + 1))
    (mass : Fin (n + 1) → Probability)
    (h_nonneg : ∀ j : Fin (n + 1), 0 ≤ mass j)
    (i : Fin k)
    (j : Fin m) :
    (prependSourceMassMatrix M mass h_nonneg).entry i ⟨n + 1 + j.1, by
      have h_succ : j.1 + 1 < m + 1 := Nat.succ_lt_succ j.2
      omega⟩ =
      M.entry i j.succ := by
  let tailIndex : Fin (n + m + 1) := ⟨n + 1 + j.1, by
    have h_succ : j.1 + 1 < m + 1 := Nat.succ_lt_succ j.2
    omega⟩
  have h_head : ¬ tailIndex.1 < n + 1 := by
    exact Nat.not_lt.mpr (Nat.le_add_right (n + 1) j.1)
  have h_tail : (⟨tailIndex.1 - (n + 1), by
      have h_bound : tailIndex.1 < n + m + 1 := tailIndex.2
      omega⟩ : Fin m) = j := by
    apply Fin.ext
    change tailIndex.1 - (n + 1) = j.1
    dsimp [tailIndex]
    omega
  change (prependSourceMassMatrix M mass h_nonneg).entry i tailIndex = M.entry i j.succ
  calc
    (prependSourceMassMatrix M mass h_nonneg).entry i tailIndex =
        M.entry i ((excludeOne_backward (0 : Fin (m + 1)) ⟨tailIndex.1 - (n + 1), by
          have h_bound : tailIndex.1 < n + m + 1 := tailIndex.2
          omega⟩).1) := by
            exact prependSourceMassMatrix_entry_of_ge M mass h_nonneg i tailIndex h_head
    _ = M.entry i ((excludeOne_backward (0 : Fin (m + 1)) j).1) := by rw [h_tail]
    _ = M.entry i j.succ := by rw [excludeOne_backward_zero]

theorem prependSourceMassMatrix_singleton_eq {k m : Nat}
    (M : ConditionalProbabilityMatrix k (m + 1))
    (mass : Fin 1 → Probability)
    (h_nonneg : ∀ j : Fin 1, 0 ≤ mass j)
    (h_mass_one : mass 0 = 1) :
    prependSourceMassMatrix (n := 0) M mass h_nonneg = M.cast (by omega) := by
  let h_width : m + 1 = 0 + m + 1 := by omega
  change prependSourceMassMatrix (n := 0) M mass h_nonneg = M.cast h_width
  apply ConditionalProbabilityMatrix.ext
  intro i j
  let j' : Fin (m + 1) := Fin.cast h_width.symm j
  by_cases h_zero : j'.1 = 0
  · have h_j : j = 0 := by
      apply Fin.ext
      simpa [j'] using h_zero
    subst j
    calc
      (prependSourceMassMatrix (n := 0) M mass h_nonneg).entry i 0 =
          mass 0 * M.entry i 0 := by
            simpa using prependSourceMassMatrix_head (n := 0) M mass h_nonneg i 0
      _ = 1 * M.entry i 0 := by rw [h_mass_one]
      _ = M.entry i 0 := by rw [Rat.one_mul]
      _ = (M.cast h_width).entry i 0 := by
            rw [ConditionalProbabilityMatrix.cast_entry]
            rfl
  · let tail : Fin m := ⟨j'.1 - 1, by
      have h_bound : j'.1 < m + 1 := j'.2
      omega⟩
    let tailIndex : Fin (0 + m + 1) := ⟨0 + 1 + tail.1, by
      have h_succ : tail.1 + 1 < m + 1 := Nat.succ_lt_succ tail.2
      omega⟩
    have h_tail_succ_val : tail.1 + 1 = j'.1 := by
      dsimp [tail]
      exact Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.pos_of_ne_zero h_zero))
    have h_j : tailIndex = j := by
      apply Fin.ext
      calc
        tailIndex.1 = 0 + 1 + tail.1 := by rfl
        _ = tail.1 + 1 := by rw [Nat.add_comm]
        _ = j'.1 := h_tail_succ_val
        _ = j.1 := by rfl
    have h_j' : tail.succ = j' := by
      apply Fin.ext
      simpa using h_tail_succ_val
    have h_tail_entry :
        (prependSourceMassMatrix (n := 0) M mass h_nonneg).entry i tailIndex = M.entry i tail.succ := by
      simpa [tailIndex, Nat.add_assoc] using
        prependSourceMassMatrix_tail (n := 0) M mass h_nonneg i tail
    have h_cast_tailIndex : Fin.cast h_width.symm tailIndex = j' := by
      rw [h_j]
    calc
      (prependSourceMassMatrix (n := 0) M mass h_nonneg).entry i j =
          (prependSourceMassMatrix (n := 0) M mass h_nonneg).entry i tailIndex := by
            rw [← h_j]
      _ =
          M.entry i tail.succ := h_tail_entry
      _ = M.entry i j' := by rw [h_j']
      _ = (M.cast h_width).entry i tailIndex := by
            rw [ConditionalProbabilityMatrix.cast_entry, h_cast_tailIndex]
      _ = (M.cast h_width).entry i j := by rw [h_j]

theorem prependSourceMassMatrix_singleton_state_eq {k m : Nat}
    (M : ConditionalProbabilityMatrix k (m + 1))
    (mass : Fin 1 → Probability)
    (h_nonneg : ∀ j : Fin 1, 0 ≤ mass j)
    (h_mass_one : mass 0 = 1) :
    (⟨0 + m + 1, prependSourceMassMatrix (n := 0) M mass h_nonneg⟩ : MatrixState k) =
      ⟨m + 1, M⟩ := by
  rw [prependSourceMassMatrix_singleton_eq M mass h_nonneg h_mass_one]
  simpa using (MatrixState.cast_eq (M := M) (h := show m + 1 = 0 + m + 1 by omega))

theorem prependSourceMassMatrix_splitWidth_eq (m n : Nat) :
    (n + 1) + m + 1 = n + m + 2 := by
  omega

def prependSourceMassMatrixSplitWidth {k m n : Nat}
    (M : ConditionalProbabilityMatrix k (m + 1))
    (mass : Fin (n + 2) → Probability)
    (h_nonneg : ∀ j : Fin (n + 2), 0 ≤ mass j) :
    ConditionalProbabilityMatrix k (n + m + 2) :=
  (prependSourceMassMatrix (n := n + 1) M mass h_nonneg).cast
    (prependSourceMassMatrix_splitWidth_eq m n)

theorem prependSourceMassMatrixSplitWidth_head {k m n : Nat}
    (M : ConditionalProbabilityMatrix k (m + 1))
    (mass : Fin (n + 2) → Probability)
    (h_nonneg : ∀ j : Fin (n + 2), 0 ≤ mass j)
    (i : Fin k)
    (j : Fin (n + 2)) :
    (prependSourceMassMatrixSplitWidth M mass h_nonneg).entry i ⟨j.1, by omega⟩ =
      mass j * M.entry i 0 := by
  let targetIndex : Fin (n + m + 2) := ⟨j.1, by omega⟩
  let sourceIndex : Fin ((n + 1) + m + 1) := ⟨j.1, by omega⟩
  have h_cast :
      Fin.cast (prependSourceMassMatrix_splitWidth_eq m n).symm targetIndex = sourceIndex := by
    apply Fin.ext
    rfl
  have h_head : sourceIndex.1 < n + 2 := by
    dsimp [sourceIndex]
    exact j.2
  calc
    (prependSourceMassMatrixSplitWidth M mass h_nonneg).entry i targetIndex =
        (prependSourceMassMatrix (n := n + 1) M mass h_nonneg).entry i
          (Fin.cast (prependSourceMassMatrix_splitWidth_eq m n).symm targetIndex) := by
            rw [prependSourceMassMatrixSplitWidth, ConditionalProbabilityMatrix.cast_entry]
    _ = (prependSourceMassMatrix (n := n + 1) M mass h_nonneg).entry i sourceIndex := by
          rw [h_cast]
    _ = mass j * M.entry i 0 := by
          simpa [sourceIndex] using
            prependSourceMassMatrix_entry_of_lt (n := n + 1) M mass h_nonneg i sourceIndex h_head

theorem prependSourceMassMatrixSplitWidth_tail {k m n : Nat}
    (M : ConditionalProbabilityMatrix k (m + 1))
    (mass : Fin (n + 2) → Probability)
    (h_nonneg : ∀ j : Fin (n + 2), 0 ≤ mass j)
    (i : Fin k)
    (j : Fin m) :
    (prependSourceMassMatrixSplitWidth M mass h_nonneg).entry i ⟨n + 2 + j.1, by
      have h_succ : j.1 + 1 < m + 1 := Nat.succ_lt_succ j.2
      omega⟩ =
      M.entry i j.succ := by
  let targetIndex : Fin (n + m + 2) := ⟨n + 2 + j.1, by
    have h_succ : j.1 + 1 < m + 1 := Nat.succ_lt_succ j.2
    omega⟩
  let sourceIndex : Fin ((n + 1) + m + 1) := ⟨n + 2 + j.1, by
    have h_succ : j.1 + 1 < m + 1 := Nat.succ_lt_succ j.2
    omega⟩
  have h_cast :
      Fin.cast (prependSourceMassMatrix_splitWidth_eq m n).symm targetIndex = sourceIndex := by
    apply Fin.ext
    rfl
  calc
    (prependSourceMassMatrixSplitWidth M mass h_nonneg).entry i targetIndex =
        (prependSourceMassMatrix (n := n + 1) M mass h_nonneg).entry i
          (Fin.cast (prependSourceMassMatrix_splitWidth_eq m n).symm targetIndex) := by
            rw [prependSourceMassMatrixSplitWidth, ConditionalProbabilityMatrix.cast_entry]
    _ = (prependSourceMassMatrix (n := n + 1) M mass h_nonneg).entry i sourceIndex := by
          rw [h_cast]
    _ = M.entry i j.succ := by
          simpa [sourceIndex] using
            prependSourceMassMatrix_tail (n := n + 1) M mass h_nonneg i j

theorem prependSourceMassMatrixSplitWidth_succ_zero {k m n : Nat}
    (M : ConditionalProbabilityMatrix k (m + 1))
    (mass : Fin (n + 2) → Probability)
    (h_nonneg : ∀ j : Fin (n + 2), 0 ≤ mass j)
    (i : Fin k) :
    (prependSourceMassMatrixSplitWidth M mass h_nonneg).entry i (0 : Fin (n + m + 1)).succ =
      mass (1 : Fin (n + 2)) * M.entry i 0 := by
  have h_index : ((0 : Fin (n + m + 1)).succ : Fin (n + m + 2)) = 1 := by
    apply Fin.ext
    rfl
  calc
    (prependSourceMassMatrixSplitWidth M mass h_nonneg).entry i (0 : Fin (n + m + 1)).succ =
        (prependSourceMassMatrixSplitWidth M mass h_nonneg).entry i (1 : Fin (n + m + 2)) := by
          rw [h_index]
    _ = mass (1 : Fin (n + 2)) * M.entry i 0 := by
          simpa using prependSourceMassMatrixSplitWidth_head M mass h_nonneg i (1 : Fin (n + 2))

theorem prependSourceMassMatrix_positiveWidth_eq (m w : Nat) (h_pos : 0 < w) :
    (w - 1) + m + 1 = w + m := by
  omega

noncomputable def prependSourceMassMatrixPositiveWidth {k m w : Nat}
    (M : ConditionalProbabilityMatrix k (m + 1))
    (mass : Fin w → Probability)
    (h_nonneg : ∀ j : Fin w, 0 ≤ mass j)
    (h_pos : 0 < w) :
    ConditionalProbabilityMatrix k (w + m) :=
  (prependSourceMassMatrix (n := w - 1)
      M
      (fun j : Fin ((w - 1) + 1) => mass (Fin.cast (by omega) j))
      (fun j => h_nonneg (Fin.cast (by omega) j))).cast
    (prependSourceMassMatrix_positiveWidth_eq m w h_pos)

theorem prependSourceMassMatrixPositiveWidth_head {k m w : Nat}
    (M : ConditionalProbabilityMatrix k (m + 1))
    (mass : Fin w → Probability)
    (h_nonneg : ∀ j : Fin w, 0 ≤ mass j)
    (h_pos : 0 < w)
    (i : Fin k)
    (j : Fin w) :
    (prependSourceMassMatrixPositiveWidth M mass h_nonneg h_pos).entry i ⟨j.1, by
      have h_wm : w ≤ w + m := Nat.le_add_right w m
      exact Nat.lt_of_lt_of_le j.2 h_wm⟩ =
      mass j * M.entry i 0 := by
  let targetIndex : Fin (w + m) := ⟨j.1, by
    have h_wm : w ≤ w + m := Nat.le_add_right w m
    exact Nat.lt_of_lt_of_le j.2 h_wm⟩
  let sourceIndex : Fin ((w - 1) + m + 1) :=
    Fin.cast (prependSourceMassMatrix_positiveWidth_eq m w h_pos).symm targetIndex
  have h_source_eq : sourceIndex = ⟨j.1, by
      have h_head : j.1 < (w - 1) + 1 := by
        have h_wsub : (w - 1) + 1 = w := by omega
        simp [h_wsub]
      have h_le : (w - 1) + 1 ≤ (w - 1) + m + 1 := by
        omega
      exact Nat.lt_of_lt_of_le h_head h_le⟩ := by
    apply Fin.ext
    rfl
  calc
    (prependSourceMassMatrixPositiveWidth M mass h_nonneg h_pos).entry i targetIndex =
        (prependSourceMassMatrix (n := w - 1)
          M
          (fun j : Fin ((w - 1) + 1) => mass (Fin.cast (by omega) j))
          (fun j => h_nonneg (Fin.cast (by omega) j))).entry i sourceIndex := by
            rw [prependSourceMassMatrixPositiveWidth, ConditionalProbabilityMatrix.cast_entry]
    _ = (prependSourceMassMatrix (n := w - 1)
          M
          (fun j : Fin ((w - 1) + 1) => mass (Fin.cast (by omega) j))
          (fun j => h_nonneg (Fin.cast (by omega) j))).entry i ⟨j.1, by
            have h_head : j.1 < (w - 1) + 1 := by
              have h_wsub : (w - 1) + 1 = w := by omega
              simp [h_wsub]
            have h_le : (w - 1) + 1 ≤ (w - 1) + m + 1 := by
              omega
            exact Nat.lt_of_lt_of_le h_head h_le⟩ := by
          rw [h_source_eq]
    _ = mass j * M.entry i 0 := by
          have h_wsub : (w - 1) + 1 = w := by omega
          simpa [h_wsub] using prependSourceMassMatrix_head
            (n := w - 1)
            M
            (fun j : Fin ((w - 1) + 1) => mass (Fin.cast (by omega) j))
            (fun j => h_nonneg (Fin.cast (by omega) j))
            i
            (Fin.cast h_wsub.symm j)

theorem prependSourceMassMatrixPositiveWidth_tail {k m w : Nat}
    (M : ConditionalProbabilityMatrix k (m + 1))
    (mass : Fin w → Probability)
    (h_nonneg : ∀ j : Fin w, 0 ≤ mass j)
    (h_pos : 0 < w)
    (i : Fin k)
    (j : Fin m) :
    (prependSourceMassMatrixPositiveWidth M mass h_nonneg h_pos).entry i ⟨w + j.1, by
      have h_succ : j.1 + 1 < m + 1 := Nat.succ_lt_succ j.2
      omega⟩ =
      M.entry i j.succ := by
  let targetIndex : Fin (w + m) := ⟨w + j.1, by
    have h_succ : j.1 + 1 < m + 1 := Nat.succ_lt_succ j.2
    omega⟩
  let sourceIndex : Fin ((w - 1) + m + 1) :=
    Fin.cast (prependSourceMassMatrix_positiveWidth_eq m w h_pos).symm targetIndex
  have h_source_eq : sourceIndex = ⟨(w - 1) + 1 + j.1, by
      have h_succ : j.1 + 1 < m + 1 := Nat.succ_lt_succ j.2
      omega⟩ := by
    apply Fin.ext
    dsimp [sourceIndex, targetIndex]
    omega
  calc
    (prependSourceMassMatrixPositiveWidth M mass h_nonneg h_pos).entry i targetIndex =
        (prependSourceMassMatrix (n := w - 1)
          M
          (fun j : Fin ((w - 1) + 1) => mass (Fin.cast (by omega) j))
          (fun j => h_nonneg (Fin.cast (by omega) j))).entry i sourceIndex := by
            rw [prependSourceMassMatrixPositiveWidth, ConditionalProbabilityMatrix.cast_entry]
    _ = (prependSourceMassMatrix (n := w - 1)
          M
          (fun j : Fin ((w - 1) + 1) => mass (Fin.cast (by omega) j))
          (fun j => h_nonneg (Fin.cast (by omega) j))).entry i ⟨(w - 1) + 1 + j.1, by
            have h_succ : j.1 + 1 < m + 1 := Nat.succ_lt_succ j.2
            omega⟩ := by
          rw [h_source_eq]
    _ = M.entry i j.succ := by
          have h_succ : j.1 + 1 < m + 1 := Nat.succ_lt_succ j.2
          simpa using prependSourceMassMatrix_tail
            (n := w - 1)
            M
            (fun j : Fin ((w - 1) + 1) => mass (Fin.cast (by omega) j))
            (fun j => h_nonneg (Fin.cast (by omega) j))
            i
            j

def mergeMassZero {n : Nat} (mass : Fin (n + 2) → Probability) :
    Fin (n + 1) → Probability :=
  fun j =>
    if j = 0 then
      mass 0 + mass (0 : Fin (n + 1)).succ
    else
      mass j.succ

theorem mergeMassZero_nonnegative {n : Nat}
    (mass : Fin (n + 2) → Probability)
    (h_nonneg : ∀ j : Fin (n + 2), 0 ≤ mass j) :
    ∀ j : Fin (n + 1), 0 ≤ mergeMassZero mass j := by
  intro j
  by_cases h : j = 0
  · subst j
    simp [mergeMassZero, Rat.add_nonneg, h_nonneg]
  · simp [mergeMassZero, h, h_nonneg]

theorem mergeMassZero_positive {n : Nat}
    (mass : Fin (n + 2) → Probability)
    (h_pos : ∀ j : Fin (n + 2), 0 < mass j) :
    ∀ j : Fin (n + 1), 0 < mergeMassZero mass j := by
  intro j
  by_cases h : j = 0
  · subst j
    have h_lt_sum : mass 0 < mass 0 + mass (0 : Fin (n + 1)).succ := by
      simpa [Rat.add_zero] using
        (Rat.add_lt_add_left (c := mass 0)).2 (h_pos (0 : Fin (n + 1)).succ)
    calc
      0 < mass 0 := h_pos 0
      _ < mass 0 + mass (0 : Fin (n + 1)).succ := h_lt_sum
  · simp [mergeMassZero, h, h_pos]

theorem adjacent_ppm_merge_massMatrix_zero_eq {k n : Nat}
    (mass : Fin (n + 2) → Probability)
    (h_nonneg : ∀ j : Fin (n + 2), 0 ≤ mass j) :
    adjacent_ppm_merge_matrix (massMatrix k (n + 2) mass h_nonneg) 0 =
      massMatrix k (n + 1) (mergeMassZero mass)
        (mergeMassZero_nonnegative mass h_nonneg) := by
  apply ConditionalProbabilityMatrix.ext
  intro i j
  by_cases h_zero : j = 0
  · subst j
    rw [adjacent_ppm_merge_matrix_target]
    simp [massMatrix, mergeMassZero]
  · let oldColumn : ColumnsExceptTwo (0 : Fin (n + 2)) (0 : Fin (n + 1)).succ :=
      ⟨j.succ, by
        constructor
        · intro h_eq
          have h_val : j.1 + 1 = 0 := by
            simpa using congrArg Fin.val h_eq
          exact Nat.succ_ne_zero j.1 h_val
        · intro h_eq
          have h_val : j.1 + 1 = 1 := by
            simpa using congrArg Fin.val h_eq
          apply h_zero
          apply Fin.ext
          simpa using Nat.succ.inj h_val⟩
    have h_j : ((adjacent_ppm_transport 0).forward oldColumn).1 = j := by
      apply Fin.ext
      simp [adjacent_ppm_transport, adjacent_ppm_forward, oldColumn]
    calc
      (adjacent_ppm_merge_matrix (massMatrix k (n + 2) mass h_nonneg) 0).entry i j =
          (adjacent_ppm_merge_matrix (massMatrix k (n + 2) mass h_nonneg) 0).entry i
            ((adjacent_ppm_transport 0).forward oldColumn).1 := by
              rw [h_j]
      _ = (massMatrix k (n + 2) mass h_nonneg).entry i oldColumn.1 := by
            exact adjacent_ppm_merge_matrix_rest (massMatrix k (n + 2) mass h_nonneg) 0 oldColumn i
      _ = mass j.succ := by rfl
      _ = (massMatrix k (n + 1) (mergeMassZero mass)
            (mergeMassZero_nonnegative mass h_nonneg)).entry i j := by
            simp [massMatrix, mergeMassZero, h_zero]

theorem discrete_sum_mergeMassZero {n : Nat}
    (mass : Fin (n + 2) → Probability) :
    discrete_sum (mergeMassZero mass) = discrete_sum mass := by
  have h_tail_fun :
      (fun j : Fin n => mass ((excludeOne_backward (0 : Fin (n + 1)) j).1).succ) =
        (fun j : Fin n => mass j.succ.succ) := by
    funext j
    rw [excludeOne_backward_zero]
  have h_tail :
      discrete_sum (fun j : Fin (n + 1) => mass j.succ) =
        mass (0 : Fin (n + 1)).succ +
          discrete_sum (fun j : Fin n => mass j.succ.succ) := by
    calc
      discrete_sum (fun j : Fin (n + 1) => mass j.succ) =
          mass (0 : Fin (n + 1)).succ +
            discrete_sum (fun j : Fin n =>
              mass ((excludeOne_backward (0 : Fin (n + 1)) j).1).succ) := by
                simpa using discrete_sum_fin_remove
                  (source := (0 : Fin (n + 1)))
                  (f := fun j : Fin (n + 1) => mass j.succ)
      _ = mass (0 : Fin (n + 1)).succ +
            discrete_sum (fun j : Fin n => mass j.succ.succ) := by
              rw [h_tail_fun]
  have h_merge_tail_fun :
      (fun j : Fin n => mergeMassZero mass (excludeOne_backward (0 : Fin (n + 1)) j).1) =
        (fun j : Fin n => mass j.succ.succ) := by
    funext j
    rw [excludeOne_backward_zero]
    have h_succ_ne : j.succ ≠ (0 : Fin (n + 1)) := by
      intro h_eq
      have h_val : j.1 + 1 = 0 := by
        simpa using congrArg Fin.val h_eq
      exact Nat.succ_ne_zero j.1 h_val
    simp [mergeMassZero, h_succ_ne]
  calc
    discrete_sum (mergeMassZero mass) =
        mergeMassZero mass 0 +
          discrete_sum (fun j : Fin n =>
            mergeMassZero mass (excludeOne_backward (0 : Fin (n + 1)) j).1) := by
              simpa using discrete_sum_fin_remove
                (source := (0 : Fin (n + 1)))
                (f := mergeMassZero mass)
    _ = (mass 0 + mass (0 : Fin (n + 1)).succ) +
          discrete_sum (fun j : Fin n => mass j.succ.succ) := by
            rw [h_merge_tail_fun]
            simp [mergeMassZero]
    _ = mass 0 +
          (mass (0 : Fin (n + 1)).succ +
            discrete_sum (fun j : Fin n => mass j.succ.succ)) := by
            rw [Rat.add_assoc]
    _ = mass 0 + discrete_sum (fun j : Fin (n + 1) => mass j.succ) := by
            rw [h_tail]
    _ = discrete_sum mass := by
            symm
            simpa using discrete_sum_fin_remove
              (source := (0 : Fin (n + 2))) (f := mass)

def splitMassZeroAlpha {n : Nat} (mass : Fin (n + 2) → Probability) : Probability :=
  mass 0 / mergeMassZero mass 0

theorem mergeMassZero_zero_pos {n : Nat}
    (mass : Fin (n + 2) → Probability)
    (h_pos : ∀ j : Fin (n + 2), 0 < mass j) :
    0 < mergeMassZero mass 0 := by
  have h_lt_sum : mass 0 < mass 0 + mass (0 : Fin (n + 1)).succ := by
    simpa [Rat.add_zero] using
      (Rat.add_lt_add_left (c := mass 0)).2 (h_pos (0 : Fin (n + 1)).succ)
  calc
    0 < mass 0 := h_pos 0
    _ < mergeMassZero mass 0 := by
          simpa [mergeMassZero] using h_lt_sum

theorem splitMassZeroAlpha_pos {n : Nat}
    (mass : Fin (n + 2) → Probability)
    (h_pos : ∀ j : Fin (n + 2), 0 < mass j) :
    0 < splitMassZeroAlpha mass := by
  have h_den_pos : 0 < mergeMassZero mass 0 := mergeMassZero_zero_pos mass h_pos
  rw [splitMassZeroAlpha]
  exact (Rat.lt_div_iff h_den_pos).2 (by simpa [Rat.zero_mul] using h_pos 0)

theorem splitMassZeroAlpha_lt_one {n : Nat}
    (mass : Fin (n + 2) → Probability)
    (h_pos : ∀ j : Fin (n + 2), 0 < mass j) :
    splitMassZeroAlpha mass < 1 := by
  have h_den_pos : 0 < mergeMassZero mass 0 := mergeMassZero_zero_pos mass h_pos
  have h_lt_sum : mass 0 < mergeMassZero mass 0 := by
    have h_lt : mass 0 < mass 0 + mass (0 : Fin (n + 1)).succ := by
      simpa [Rat.add_zero] using
        (Rat.add_lt_add_left (c := mass 0)).2 (h_pos (0 : Fin (n + 1)).succ)
    simpa [mergeMassZero] using h_lt
  rw [splitMassZeroAlpha]
  exact (Rat.div_lt_iff h_den_pos).2 (by simpa [Rat.one_mul] using h_lt_sum)

theorem splitMassZeroAlpha_mul_mergeMassZero_zero {n : Nat}
    (mass : Fin (n + 2) → Probability)
    (h_pos : ∀ j : Fin (n + 2), 0 < mass j) :
    splitMassZeroAlpha mass * mergeMassZero mass 0 = mass 0 := by
  have h_den_ne : mergeMassZero mass 0 ≠ 0 := by
    intro h_zero
    have h_den_pos : 0 < mergeMassZero mass 0 := mergeMassZero_zero_pos mass h_pos
    have h_zero_pos : 0 < (0 : Probability) := by
      rw [h_zero] at h_den_pos
      exact h_den_pos
    exact (Rat.not_lt.mpr (by decide : (0 : Probability) ≤ 0)) h_zero_pos
  rw [splitMassZeroAlpha]
  exact Rat.div_mul_cancel (a := mass 0) (b := mergeMassZero mass 0)
    h_den_ne

theorem one_sub_splitMassZeroAlpha_mul_mergeMassZero_zero {n : Nat}
    (mass : Fin (n + 2) → Probability)
    (h_pos : ∀ j : Fin (n + 2), 0 < mass j) :
    (1 - splitMassZeroAlpha mass) * mergeMassZero mass 0 = mass (0 : Fin (n + 1)).succ := by
  calc
    (1 - splitMassZeroAlpha mass) * mergeMassZero mass 0 =
        (1 + -(splitMassZeroAlpha mass)) * mergeMassZero mass 0 := by
          rw [Rat.sub_eq_add_neg]
    _ = 1 * mergeMassZero mass 0 + (-(splitMassZeroAlpha mass)) * mergeMassZero mass 0 := by
          rw [Rat.add_mul]
    _ = mergeMassZero mass 0 + - (splitMassZeroAlpha mass * mergeMassZero mass 0) := by
          rw [Rat.one_mul, Rat.neg_mul]
    _ = mergeMassZero mass 0 + - mass 0 := by
          rw [splitMassZeroAlpha_mul_mergeMassZero_zero mass h_pos]
    _ = (mass 0 + mass (0 : Fin (n + 1)).succ) + - mass 0 := by
          simp [mergeMassZero]
    _ = mass (0 : Fin (n + 1)).succ + (mass 0 + - mass 0) := by
          rw [← Rat.add_assoc, Rat.add_comm (mass 0) (mass (0 : Fin (n + 1)).succ), Rat.add_assoc]
    _ = mass (0 : Fin (n + 1)).succ + 0 := by
          rw [Rat.add_neg_cancel]
    _ = mass (0 : Fin (n + 1)).succ := by
          rw [Rat.add_zero]

theorem adjacent_pps_split_prependSourceMassMatrix_zero_eq {k m n : Nat}
    (M : ConditionalProbabilityMatrix k (m + 1))
    (mass : Fin (n + 2) → Probability)
    (h_pos : ∀ j : Fin (n + 2), 0 < mass j) :
    adjacent_pps_split_matrix
      (prependSourceMassMatrix M (mergeMassZero mass)
        (mergeMassZero_nonnegative mass (fun j => Rat.le_of_lt (h_pos j))))
      0
      (splitMassZeroAlpha mass)
      (Rat.le_of_lt (splitMassZeroAlpha_pos mass h_pos))
      (one_sub_nonneg_of_lt_one (splitMassZeroAlpha mass) (splitMassZeroAlpha_lt_one mass h_pos)) =
    prependSourceMassMatrixSplitWidth M mass (fun j => Rat.le_of_lt (h_pos j)) := by
  let mergedNonneg : ∀ j : Fin (n + 1), 0 ≤ mergeMassZero mass j :=
    mergeMassZero_nonnegative mass (fun j => Rat.le_of_lt (h_pos j))
  let sourceMatrix : ConditionalProbabilityMatrix k (n + m + 1) :=
    prependSourceMassMatrix M (mergeMassZero mass) mergedNonneg
  let targetMatrix : ConditionalProbabilityMatrix k (n + m + 2) :=
    prependSourceMassMatrixSplitWidth M mass (fun j => Rat.le_of_lt (h_pos j))
  let α : Probability := splitMassZeroAlpha mass
  let h_alpha_nonneg : 0 ≤ α := Rat.le_of_lt (splitMassZeroAlpha_pos mass h_pos)
  let h_beta_nonneg : 0 ≤ 1 - α :=
    one_sub_nonneg_of_lt_one α (splitMassZeroAlpha_lt_one mass h_pos)
  change adjacent_pps_split_matrix sourceMatrix 0 α h_alpha_nonneg h_beta_nonneg = targetMatrix
  apply ConditionalProbabilityMatrix.ext
  intro i j
  by_cases h_zero : j = 0
  · subst j
    have h_source_zero : sourceMatrix.entry i 0 = mergeMassZero mass 0 * M.entry i 0 := by
      simpa [sourceMatrix, mergedNonneg] using
        prependSourceMassMatrix_head
          (n := n)
          M
          (mergeMassZero mass)
          mergedNonneg
          i
          0
    calc
      (adjacent_pps_split_matrix sourceMatrix 0 α h_alpha_nonneg h_beta_nonneg).entry i 0 =
          α * sourceMatrix.entry i 0 := by
            simpa [α, h_alpha_nonneg, h_beta_nonneg] using
              adjacent_pps_split_matrix_left sourceMatrix 0 α h_alpha_nonneg h_beta_nonneg i
      _ = α * (mergeMassZero mass 0 * M.entry i 0) := by
            rw [h_source_zero]
      _ = mass 0 * M.entry i 0 := by
            dsimp [α]
            rw [← Rat.mul_assoc, splitMassZeroAlpha_mul_mergeMassZero_zero mass h_pos]
      _ = targetMatrix.entry i 0 := by
            symm
            simpa [targetMatrix] using
              prependSourceMassMatrixSplitWidth_head M mass (fun j => Rat.le_of_lt (h_pos j)) i 0
  · by_cases h_one : j = (0 : Fin (n + m + 1)).succ
    · subst j
      have h_source_zero : sourceMatrix.entry i 0 = mergeMassZero mass 0 * M.entry i 0 := by
        simpa [sourceMatrix, mergedNonneg] using
          prependSourceMassMatrix_head
            (n := n)
            M
            (mergeMassZero mass)
            mergedNonneg
            i
            0
      have h_succ_zero_eq_one : ((0 : Fin (n + 1)).succ : Fin (n + 2)) = 1 := by
        apply Fin.ext
        rfl
      calc
        (adjacent_pps_split_matrix sourceMatrix 0 α h_alpha_nonneg h_beta_nonneg).entry i
            (0 : Fin (n + m + 1)).succ =
            (1 - α) * sourceMatrix.entry i 0 := by
              simpa [α, h_alpha_nonneg, h_beta_nonneg] using
                adjacent_pps_split_matrix_right sourceMatrix 0 α h_alpha_nonneg h_beta_nonneg i
        _ = (1 - α) * (mergeMassZero mass 0 * M.entry i 0) := by
              rw [h_source_zero]
        _ = mass (1 : Fin (n + 2)) * M.entry i 0 := by
            dsimp [α]
            rw [← Rat.mul_assoc, one_sub_splitMassZeroAlpha_mul_mergeMassZero_zero mass h_pos]
            exact congrArg (fun x : Fin (n + 2) => mass x * M.entry i 0) h_succ_zero_eq_one
        _ = targetMatrix.entry i (0 : Fin (n + m + 1)).succ := by
              symm
              simpa [targetMatrix] using
                prependSourceMassMatrixSplitWidth_succ_zero M mass (fun j => Rat.le_of_lt (h_pos j)) i
    · have h_j_ne_zero : j.1 ≠ 0 := by
        intro h_val
        apply h_zero
        apply Fin.ext
        exact h_val
      have h_j_ne_one : j.1 ≠ 1 := by
        intro h_val
        apply h_one
        apply Fin.ext
        exact h_val
      have h_j_ge_two : 2 ≤ j.1 := by
        omega
      let t : Fin (n + m) := ⟨j.1 - 2, by
        have h_bound : j.1 < n + m + 2 := j.2
        omega⟩
      have h_j : t.succ.succ = j := by
        apply Fin.ext
        dsimp [t]
        omega
      rw [← h_j]
      by_cases h_head : t.1 < n
      · let mergedIndex : Fin (n + 1) := ⟨t.1 + 1, Nat.succ_lt_succ h_head⟩
        let headIndex : Fin (n + 2) := mergedIndex.succ
        have h_source_head :
            sourceMatrix.entry i t.succ = mergeMassZero mass mergedIndex * M.entry i 0 := by
          have h_old_head : (t.succ : Fin (n + m + 1)).1 < n + 1 := by
            simpa using Nat.succ_lt_succ h_head
          simpa [sourceMatrix, mergedNonneg, mergedIndex] using
            prependSourceMassMatrix_entry_of_lt
              (n := n)
              M
              (mergeMassZero mass)
              mergedNonneg
              i
              t.succ
              h_old_head
        have h_merged_ne : mergedIndex ≠ 0 := by
          intro h_eq
          have h_val : t.1 + 1 = 0 := by
            simpa [mergedIndex] using congrArg Fin.val h_eq
          exact Nat.succ_ne_zero t.1 h_val
        have h_target_index : (⟨headIndex.1, by omega⟩ : Fin (n + m + 2)) = t.succ.succ := by
          apply Fin.ext
          simp [headIndex, mergedIndex]
        calc
          (adjacent_pps_split_matrix sourceMatrix 0 α h_alpha_nonneg h_beta_nonneg).entry i t.succ.succ =
              sourceMatrix.entry i t.succ := by
                simpa [α, h_alpha_nonneg, h_beta_nonneg] using
                  adjacent_pps_split_matrix_tail_shift_zero sourceMatrix α h_alpha_nonneg h_beta_nonneg i t
          _ = mergeMassZero mass mergedIndex * M.entry i 0 := h_source_head
          _ = mass headIndex * M.entry i 0 := by
                simp [mergeMassZero, mergedIndex, headIndex, h_merged_ne]
          _ = targetMatrix.entry i ⟨headIndex.1, by omega⟩ := by
                symm
                simpa [targetMatrix] using
                  prependSourceMassMatrixSplitWidth_head
                    M mass (fun j => Rat.le_of_lt (h_pos j)) i headIndex
          _ = targetMatrix.entry i t.succ.succ := by rw [h_target_index]
      · let tail : Fin m := ⟨t.1 - n, by omega⟩
        let sourceIndex : Fin (n + m + 1) := ⟨n + 1 + tail.1, by
          have h_succ : tail.1 + 1 < m + 1 := Nat.succ_lt_succ tail.2
          omega⟩
        let targetIndex : Fin (n + m + 2) := ⟨n + 2 + tail.1, by
          have h_succ : tail.1 + 1 < m + 1 := Nat.succ_lt_succ tail.2
          omega⟩
        have h_source_index : sourceIndex = t.succ := by
          apply Fin.ext
          dsimp [sourceIndex, tail]
          omega
        have h_target_index : targetIndex = t.succ.succ := by
          apply Fin.ext
          dsimp [targetIndex, tail]
          omega
        calc
          (adjacent_pps_split_matrix sourceMatrix 0 α h_alpha_nonneg h_beta_nonneg).entry i t.succ.succ =
              sourceMatrix.entry i t.succ := by
                simpa [α, h_alpha_nonneg, h_beta_nonneg] using
                  adjacent_pps_split_matrix_tail_shift_zero sourceMatrix α h_alpha_nonneg h_beta_nonneg i t
          _ = sourceMatrix.entry i sourceIndex := by rw [← h_source_index]
          _ = M.entry i tail.succ := by
                simpa [sourceMatrix, mergedNonneg, sourceIndex] using
                  prependSourceMassMatrix_tail
                    (n := n)
                    M
                    (mergeMassZero mass)
                    mergedNonneg
                    i
                    tail
          _ = targetMatrix.entry i targetIndex := by
                symm
                simpa [targetMatrix, targetIndex] using
                  prependSourceMassMatrixSplitWidth_tail
                    M mass (fun j => Rat.le_of_lt (h_pos j)) i tail
          _ = targetMatrix.entry i t.succ.succ := by rw [h_target_index]

theorem adjacent_pps_split_massMatrix_zero_eq {k n : Nat}
    (mass : Fin (n + 2) → Probability)
    (h_pos : ∀ j : Fin (n + 2), 0 < mass j) :
    adjacent_pps_split_matrix
      (massMatrix k (n + 1) (mergeMassZero mass)
        (mergeMassZero_nonnegative mass (fun j => Rat.le_of_lt (h_pos j))))
      0
      (splitMassZeroAlpha mass)
      (Rat.le_of_lt (splitMassZeroAlpha_pos mass h_pos))
      (one_sub_nonneg_of_lt_one (splitMassZeroAlpha mass) (splitMassZeroAlpha_lt_one mass h_pos)) =
    massMatrix k (n + 2) mass (fun j => Rat.le_of_lt (h_pos j)) := by
  apply ConditionalProbabilityMatrix.ext
  intro i j
  by_cases h_zero : j = 0
  · subst j
    calc
      (adjacent_pps_split_matrix
        (massMatrix k (n + 1) (mergeMassZero mass)
          (mergeMassZero_nonnegative mass (fun j => Rat.le_of_lt (h_pos j))))
        0
        (splitMassZeroAlpha mass)
        (Rat.le_of_lt (splitMassZeroAlpha_pos mass h_pos))
        (one_sub_nonneg_of_lt_one (splitMassZeroAlpha mass) (splitMassZeroAlpha_lt_one mass h_pos))).entry i 0 =
          splitMassZeroAlpha mass *
            (massMatrix k (n + 1) (mergeMassZero mass)
              (mergeMassZero_nonnegative mass (fun j => Rat.le_of_lt (h_pos j)))).entry i 0 := by
                simpa using adjacent_pps_split_matrix_left
                  (massMatrix k (n + 1) (mergeMassZero mass)
                    (mergeMassZero_nonnegative mass (fun j => Rat.le_of_lt (h_pos j))))
                  0
                  (splitMassZeroAlpha mass)
                  (Rat.le_of_lt (splitMassZeroAlpha_pos mass h_pos))
                  (one_sub_nonneg_of_lt_one (splitMassZeroAlpha mass) (splitMassZeroAlpha_lt_one mass h_pos))
                  i
      _ = splitMassZeroAlpha mass * mergeMassZero mass 0 := by
            rfl
      _ = mass 0 := splitMassZeroAlpha_mul_mergeMassZero_zero mass h_pos
      _ = (massMatrix k (n + 2) mass (fun j => Rat.le_of_lt (h_pos j))).entry i 0 := by
            rfl
  · by_cases h_one : j = (0 : Fin (n + 1)).succ
    · subst j
      rw [adjacent_pps_split_matrix_right]
      exact one_sub_splitMassZeroAlpha_mul_mergeMassZero_zero mass h_pos
    · let newColumn : ColumnsExceptPair (0 : Fin (n + 2)) (0 : Fin (n + 1)).succ := ⟨j, h_zero, h_one⟩
      let oldColumn : ColumnsExceptOne (0 : Fin (n + 1)) :=
        (adjacent_pps_transport (0 : Fin (n + 1))).backward newColumn
      have h_j : ((adjacent_pps_transport (0 : Fin (n + 1))).forward oldColumn).1 = j := by
        simpa [adjacent_pps_transport, newColumn, oldColumn] using
          congrArg Subtype.val ((adjacent_pps_transport (0 : Fin (n + 1))).right_inv newColumn)
      have h_not_before : ¬ oldColumn.1.1 < (0 : Fin (n + 1)).1 := by
        exact Nat.not_lt_zero _
      have h_old_succ : oldColumn.1.succ = j := by
        simpa [adjacent_pps_transport, adjacent_ppm_backward, oldColumn, h_not_before] using h_j
      calc
        (adjacent_pps_split_matrix
          (massMatrix k (n + 1) (mergeMassZero mass)
            (mergeMassZero_nonnegative mass (fun j => Rat.le_of_lt (h_pos j))))
          0
          (splitMassZeroAlpha mass)
          (Rat.le_of_lt (splitMassZeroAlpha_pos mass h_pos))
          (one_sub_nonneg_of_lt_one (splitMassZeroAlpha mass) (splitMassZeroAlpha_lt_one mass h_pos))).entry i j =
            (adjacent_pps_split_matrix
              (massMatrix k (n + 1) (mergeMassZero mass)
                (mergeMassZero_nonnegative mass (fun j => Rat.le_of_lt (h_pos j))))
              0
              (splitMassZeroAlpha mass)
              (Rat.le_of_lt (splitMassZeroAlpha_pos mass h_pos))
              (one_sub_nonneg_of_lt_one (splitMassZeroAlpha mass) (splitMassZeroAlpha_lt_one mass h_pos))).entry i
                ((adjacent_pps_transport (0 : Fin (n + 1))).forward oldColumn).1 := by
                  rw [h_j]
        _ = (massMatrix k (n + 1) (mergeMassZero mass)
              (mergeMassZero_nonnegative mass (fun j => Rat.le_of_lt (h_pos j)))).entry i oldColumn.1 := by
              exact adjacent_pps_split_matrix_rest
                (massMatrix k (n + 1) (mergeMassZero mass)
                  (mergeMassZero_nonnegative mass (fun j => Rat.le_of_lt (h_pos j))))
                0
                (splitMassZeroAlpha mass)
                (Rat.le_of_lt (splitMassZeroAlpha_pos mass h_pos))
                (one_sub_nonneg_of_lt_one (splitMassZeroAlpha mass) (splitMassZeroAlpha_lt_one mass h_pos))
                oldColumn i
        _ = mergeMassZero mass oldColumn.1 := by
              rfl
        _ = mass oldColumn.1.succ := by
              simp [mergeMassZero, oldColumn.2]
        _ = mass j := by rw [h_old_succ]
        _ = (massMatrix k (n + 2) mass (fun j => Rat.le_of_lt (h_pos j))).entry i j := by
              rfl

theorem one_vector_reachable_to_massMatrix_of_sum_one {k n : Nat}
    (mass : Fin (n + 1) → Probability)
    (h_pos : ∀ j : Fin (n + 1), 0 < mass j)
    (h_sum_one : discrete_sum mass = 1) :
    MatrixReachable (pps_ppm_vpm_step (k := k))
      ⟨1, one_vector_matrix k⟩
      ⟨n + 1,
        massMatrix k (n + 1) mass (fun j => Rat.le_of_lt (h_pos j))⟩ := by
  induction n with
  | zero =>
      have h_tail_zero :
          discrete_sum (fun j : Fin 0 => mass (excludeOne_backward 0 j).1) = 0 := by
        have h_fun :
            (fun j : Fin 0 => mass (excludeOne_backward 0 j).1) = fun _ : Fin 0 => 0 := by
          funext j
          exact False.elim (Nat.not_lt_zero _ j.2)
        rw [h_fun, InfoTheory.discrete_sum_zero]
      have h_mass_one : mass 0 = 1 := by
        calc
          mass 0 = mass 0 + discrete_sum (fun j : Fin 0 => mass (excludeOne_backward 0 j).1) := by
            rw [h_tail_zero, Rat.add_zero]
          _ = discrete_sum mass := by
            symm
            simpa using discrete_sum_fin_remove (source := (0 : Fin 1)) (f := mass)
          _ = 1 := h_sum_one
      have h_eq :
          massMatrix k 1 mass (fun j => Rat.le_of_lt (h_pos j)) = one_vector_matrix k := by
        apply ConditionalProbabilityMatrix.ext
        intro i j
        have h_j : j = 0 := by
          apply Fin.ext
          omega
        subst j
        simp [massMatrix, one_vector_matrix, h_mass_one]
      simpa [h_eq] using
        (MatrixReachable.refl (step := pps_ppm_vpm_step (k := k))
          ⟨1, one_vector_matrix k⟩)
  | succ n ih =>
      let mergedMass := mergeMassZero mass
      have h_prefix :
          MatrixReachable (pps_ppm_vpm_step (k := k))
            ⟨1, one_vector_matrix k⟩
            ⟨n + 1,
              massMatrix k (n + 1) mergedMass
                (mergeMassZero_nonnegative mass (fun j => Rat.le_of_lt (h_pos j)))⟩ := by
        have h_tail_sum : discrete_sum mergedMass = 1 := by
          rw [discrete_sum_mergeMassZero]
          exact h_sum_one
        exact ih mergedMass
          (mergeMassZero_positive mass h_pos)
          h_tail_sum
      have h_split :
          MatrixReachable (pps_ppm_vpm_step (k := k))
            ⟨n + 1,
              massMatrix k (n + 1) mergedMass
                (mergeMassZero_nonnegative mass (fun j => Rat.le_of_lt (h_pos j)))⟩
            ⟨n + 2,
              massMatrix k (n + 2) mass (fun j => Rat.le_of_lt (h_pos j))⟩ := by
        have h_step := adjacent_pps_split_reachable_by_pps_ppm_vpm
          (massMatrix k (n + 1) mergedMass
            (mergeMassZero_nonnegative mass (fun j => Rat.le_of_lt (h_pos j))))
          0
          (splitMassZeroAlpha mass)
          (massMatrix_is_singular mergedMass _)
          (splitMassZeroAlpha_pos mass h_pos)
          (splitMassZeroAlpha_lt_one mass h_pos)
        simpa [mergedMass, adjacent_pps_split_massMatrix_zero_eq mass h_pos] using h_step
      exact MatrixReachable.trans h_prefix h_split

theorem one_vector_reachable_to_massMatrix_of_sum_one_any {k n : Nat}
    (mass : Fin n → Probability)
    (h_pos : ∀ j : Fin n, 0 < mass j)
    (h_sum_one : discrete_sum mass = 1) :
    MatrixReachable (pps_ppm_vpm_step (k := k))
      ⟨1, one_vector_matrix k⟩
      ⟨n,
        massMatrix k n mass (fun j => Rat.le_of_lt (h_pos j))⟩ := by
  cases n with
  | zero =>
      have h_zero : discrete_sum mass = 0 := by
        have h_fun : mass = fun _ : Fin 0 => 0 := by
          funext j
          exact False.elim (Nat.not_lt_zero _ j.2)
        rw [h_fun, InfoTheory.discrete_sum_zero]
      rw [h_zero] at h_sum_one
      simp at h_sum_one
  | succ n =>
      simpa using one_vector_reachable_to_massMatrix_of_sum_one
        (k := k) (n := n) mass h_pos h_sum_one

theorem matrix_reachable_to_prependSourceMassMatrix_of_sum_one {k m n : Nat}
    (M : ConditionalProbabilityMatrix k (m + 1))
    (h_singular : matrix_is_singular M)
    (mass : Fin (n + 1) → Probability)
    (h_pos : ∀ j : Fin (n + 1), 0 < mass j)
    (h_sum_one : discrete_sum mass = 1) :
    MatrixReachable (pps_ppm_vpm_step (k := k))
      ⟨m + 1, M⟩
      ⟨n + m + 1,
        prependSourceMassMatrix M mass (fun j => Rat.le_of_lt (h_pos j))⟩ := by
  induction n with
  | zero =>
      have h_tail_zero :
          discrete_sum (fun j : Fin 0 => mass (excludeOne_backward 0 j).1) = 0 := by
        have h_fun :
            (fun j : Fin 0 => mass (excludeOne_backward 0 j).1) = fun _ : Fin 0 => 0 := by
          funext j
          exact False.elim (Nat.not_lt_zero _ j.2)
        rw [h_fun, InfoTheory.discrete_sum_zero]
      have h_mass_one : mass 0 = 1 := by
        calc
          mass 0 = mass 0 + discrete_sum (fun j : Fin 0 => mass (excludeOne_backward 0 j).1) := by
            rw [h_tail_zero, Rat.add_zero]
          _ = discrete_sum mass := by
            symm
            simpa using discrete_sum_fin_remove (source := (0 : Fin 1)) (f := mass)
          _ = 1 := h_sum_one
      have h_state_eq :
          (⟨0 + m + 1,
            prependSourceMassMatrix (n := 0) M mass (fun j => Rat.le_of_lt (h_pos j))⟩ : MatrixState k) =
          ⟨m + 1, M⟩ := by
        exact prependSourceMassMatrix_singleton_state_eq
          M mass (fun j => Rat.le_of_lt (h_pos j)) h_mass_one
      rw [h_state_eq]
      exact MatrixReachable.refl ⟨m + 1, M⟩
  | succ n ih =>
      let mergedMass := mergeMassZero mass
      let mergedNonneg : ∀ j : Fin (n + 1), 0 ≤ mergedMass j :=
        mergeMassZero_nonnegative mass (fun j => Rat.le_of_lt (h_pos j))
      have h_prefix :
          MatrixReachable (pps_ppm_vpm_step (k := k))
            ⟨m + 1, M⟩
            ⟨n + m + 1,
              prependSourceMassMatrix M mergedMass mergedNonneg⟩ := by
        have h_tail_sum : discrete_sum mergedMass = 1 := by
          rw [discrete_sum_mergeMassZero]
          exact h_sum_one
        exact ih mergedMass
          (mergeMassZero_positive mass h_pos)
          h_tail_sum
      have h_step :
          MatrixReachable (pps_ppm_vpm_step (k := k))
            ⟨n + m + 1,
              prependSourceMassMatrix M mergedMass mergedNonneg⟩
            ⟨n + m + 2,
              prependSourceMassMatrixSplitWidth M mass (fun j => Rat.le_of_lt (h_pos j))⟩ := by
        have h_split := adjacent_pps_split_reachable_by_pps_ppm_vpm
          (prependSourceMassMatrix M mergedMass mergedNonneg)
          0
          (splitMassZeroAlpha mass)
          (prependSourceMassMatrix_is_singular M mergedMass mergedNonneg h_singular)
          (splitMassZeroAlpha_pos mass h_pos)
          (splitMassZeroAlpha_lt_one mass h_pos)
        simpa [mergedMass, adjacent_pps_split_prependSourceMassMatrix_zero_eq M mass h_pos] using h_split
      have h_total := MatrixReachable.trans h_prefix h_step
      have h_finish_eq :
          (⟨n + m + 2,
            prependSourceMassMatrixSplitWidth M mass (fun j => Rat.le_of_lt (h_pos j))⟩ : MatrixState k) =
          ⟨(n + 1) + m + 1,
            prependSourceMassMatrix (n := n + 1) M mass (fun j => Rat.le_of_lt (h_pos j))⟩ := by
        simpa [prependSourceMassMatrixSplitWidth] using
          (MatrixState.cast_eq
            (M := prependSourceMassMatrix (n := n + 1) M mass (fun j => Rat.le_of_lt (h_pos j)))
            (h := prependSourceMassMatrix_splitWidth_eq m n))
      rw [h_finish_eq] at h_total
      simpa [Nat.succ_eq_add_one] using h_total

theorem matrix_reachable_to_prependSourceMassMatrixPositiveWidth_of_sum_one {k m w : Nat}
    (M : ConditionalProbabilityMatrix k (m + 1))
    (h_singular : matrix_is_singular M)
    (mass : Fin w → Probability)
    (h_pos : ∀ j : Fin w, 0 < mass j)
    (h_sum_one : discrete_sum mass = 1)
    (h_wpos : 0 < w) :
    MatrixReachable (pps_ppm_vpm_step (k := k))
      ⟨m + 1, M⟩
      ⟨w + m,
        prependSourceMassMatrixPositiveWidth M mass (fun j => Rat.le_of_lt (h_pos j)) h_wpos⟩ := by
  cases w with
  | zero =>
      exact False.elim (Nat.not_lt_zero _ h_wpos)
  | succ n =>
      have h_reach_raw :
          MatrixReachable (pps_ppm_vpm_step (k := k))
            ⟨m + 1, M⟩
            ⟨n + m + 1,
              prependSourceMassMatrix (n := n) M mass (fun j => Rat.le_of_lt (h_pos j))⟩ := by
        exact matrix_reachable_to_prependSourceMassMatrix_of_sum_one
          (n := n)
          M
          h_singular
          mass
          h_pos
          h_sum_one
      have h_state_eq :
          ((⟨n + 1 + m,
            prependSourceMassMatrixPositiveWidth M mass (fun j => Rat.le_of_lt (h_pos j)) h_wpos⟩ : MatrixState k) =
          ⟨n + m + 1,
            prependSourceMassMatrix (n := n) M mass (fun j => Rat.le_of_lt (h_pos j))⟩) := by
        simpa [prependSourceMassMatrixPositiveWidth] using
          (MatrixState.cast_eq
            (M := prependSourceMassMatrix (n := n) M mass (fun j => Rat.le_of_lt (h_pos j)))
            (h := prependSourceMassMatrix_positiveWidth_eq m (n + 1) h_wpos))
      rw [← h_state_eq] at h_reach_raw
      simpa [Nat.succ_eq_add_one] using h_reach_raw

theorem massMatrix_reachable_to_one_vector_of_sum_one {k n : Nat}
    (mass : Fin (n + 1) → Probability)
    (h_pos : ∀ j : Fin (n + 1), 0 < mass j)
    (h_sum_one : discrete_sum mass = 1) :
    MatrixReachable (pps_ppm_vpm_step (k := k))
      ⟨n + 1,
        massMatrix k (n + 1) mass (fun j => Rat.le_of_lt (h_pos j))⟩
      ⟨1, one_vector_matrix k⟩ := by
  induction n with
  | zero =>
      have h_tail_zero :
          discrete_sum (fun j : Fin 0 => mass (excludeOne_backward 0 j).1) = 0 := by
        have h_fun :
            (fun j : Fin 0 => mass (excludeOne_backward 0 j).1) = fun _ : Fin 0 => 0 := by
          funext j
          exact False.elim (Nat.not_lt_zero _ j.2)
        rw [h_fun, InfoTheory.discrete_sum_zero]
      have h_mass_one : mass 0 = 1 := by
        calc
          mass 0 = mass 0 + discrete_sum (fun j : Fin 0 => mass (excludeOne_backward 0 j).1) := by
            rw [h_tail_zero, Rat.add_zero]
          _ = discrete_sum mass := by
            symm
            simpa using discrete_sum_fin_remove (source := (0 : Fin 1)) (f := mass)
          _ = 1 := h_sum_one
      have h_eq :
          massMatrix k 1 mass (fun j => Rat.le_of_lt (h_pos j)) = one_vector_matrix k := by
        apply ConditionalProbabilityMatrix.ext
        intro i j
        have h_j : j = 0 := by
          apply Fin.ext
          omega
        subst j
        simp [massMatrix, one_vector_matrix, h_mass_one]
      simpa [h_eq] using
        (MatrixReachable.refl (step := pps_ppm_vpm_step (k := k))
          ⟨1, one_vector_matrix k⟩)
  | succ n ih =>
      let M := massMatrix k (n + 2) mass (fun j => Rat.le_of_lt (h_pos j))
      let mergedMass := mergeMassZero mass
      have h_singular : matrix_is_singular M := massMatrix_is_singular mass _
      have h_pattern : column_pattern M 0 = column_pattern M (0 : Fin (n + 1)).succ := by
        rw [massMatrix_column_pattern_true mass _ h_pos 0,
          massMatrix_column_pattern_true mass _ h_pos (0 : Fin (n + 1)).succ]
      have h_step :
          MatrixReachable (pps_ppm_vpm_step (k := k))
            ⟨n + 2, M⟩
            ⟨n + 1,
              massMatrix k (n + 1) mergedMass
                (mergeMassZero_nonnegative mass (fun j => Rat.le_of_lt (h_pos j)))⟩ := by
        have h_merge := adjacent_ppm_merge_reachable_by_pps_ppm_vpm M 0 h_singular h_pattern
        simpa [M, mergedMass, adjacent_ppm_merge_massMatrix_zero_eq mass
          (fun j => Rat.le_of_lt (h_pos j))] using h_merge
      have h_tail_sum : discrete_sum mergedMass = 1 := by
        rw [discrete_sum_mergeMassZero]
        exact h_sum_one
      have h_tail := ih mergedMass
        (mergeMassZero_positive mass h_pos)
        h_tail_sum
      exact MatrixReachable.trans h_step h_tail

theorem massMatrix_reachable_to_one_vector_of_sum_one_any {k n : Nat}
    (mass : Fin n → Probability)
    (h_pos : ∀ j : Fin n, 0 < mass j)
    (h_sum_one : discrete_sum mass = 1) :
    MatrixReachable (pps_ppm_vpm_step (k := k))
      ⟨n,
        massMatrix k n mass (fun j => Rat.le_of_lt (h_pos j))⟩
      ⟨1, one_vector_matrix k⟩ := by
  cases n with
  | zero =>
      have h_zero : discrete_sum mass = 0 := by
        have h_fun : mass = fun _ : Fin 0 => 0 := by
          funext j
          exact False.elim (Nat.not_lt_zero _ j.2)
        rw [h_fun, InfoTheory.discrete_sum_zero]
      rw [h_zero] at h_sum_one
      simp at h_sum_one
  | succ n =>
      simpa using massMatrix_reachable_to_one_vector_of_sum_one
        (k := k) (n := n) mass h_pos h_sum_one

theorem ordered_vpm_merge_reachable_by_vpm {k n : Nat}
    (M : ConditionalProbabilityMatrix k (n + 1))
    (left right : Fin (n + 1))
    (h_lt : left.1 < right.1)
    (h_singular : matrix_is_singular M)
    (h_value : column_value M left = column_value M right)
    (h_disjoint : ∀ i : Fin k, 0 < M.entry i left → M.entry i right = 0) :
    MatrixReachable (vpm_step (k := k))
      ⟨n + 1, M⟩ ⟨n, ordered_vpm_merge_matrix M left right h_lt⟩ := by
  apply MatrixReachable.single
  dsimp [vpm_step]
  exact ordered_vpm_merge_is_vpm_operation M left right h_lt h_singular h_value h_disjoint

theorem ordered_vpm_merge_reachable_by_pps_ppm_vpm {k n : Nat}
    (M : ConditionalProbabilityMatrix k (n + 1))
    (left right : Fin (n + 1))
    (h_lt : left.1 < right.1)
    (h_singular : matrix_is_singular M)
    (h_value : column_value M left = column_value M right)
    (h_disjoint : ∀ i : Fin k, 0 < M.entry i left → M.entry i right = 0) :
    MatrixReachable (pps_ppm_vpm_step (k := k))
      ⟨n + 1, M⟩ ⟨n, ordered_vpm_merge_matrix M left right h_lt⟩ := by
  apply MatrixReachable.single
  dsimp [pps_ppm_vpm_step, pps_step, ppm_step, vpm_step]
  exact Or.inr (Or.inr (ordered_vpm_merge_is_vpm_operation M left right h_lt h_singular h_value h_disjoint))

  theorem ordered_vpm_merge_reachable_by_pps_ppm_vpm_state {k : Nat}
    (start : MatrixState k)
    (left right : Fin start.1)
    (h_lt : left.1 < right.1)
    (h_singular : matrix_is_singular start.2)
    (h_value : column_value start.2 left = column_value start.2 right)
    (h_disjoint : ∀ i : Fin k, 0 < start.2.entry i left → start.2.entry i right = 0) :
    ∃ finish : MatrixState k,
      MatrixReachable (pps_ppm_vpm_step (k := k)) start finish := by
    rcases start with ⟨m, M⟩
    cases m with
    | zero =>
        cases left with
        | mk val isLt =>
          simp at isLt
    | succ n =>
      refine ⟨⟨n, ordered_vpm_merge_matrix M left right h_lt⟩, ?_⟩
      exact ordered_vpm_merge_reachable_by_pps_ppm_vpm M left right h_lt h_singular h_value h_disjoint

def reachable_by_pps_vps_ppm {k m n : Nat}
    (M : ConditionalProbabilityMatrix k m) (M' : ConditionalProbabilityMatrix k n) : Prop :=
  MatrixReachable (pps_vps_ppm_step (k := k)) ⟨m, M⟩ ⟨n, M'⟩

def reachable_by_ordered_pps_vps_ppm {k : Nat} {m : Nat} {n : Nat}
    (M : ConditionalProbabilityMatrix k m) (M' : ConditionalProbabilityMatrix k n) : Prop :=
  ∃ middle₁ middle₂ : MatrixState k,
    MatrixReachable (pps_step (k := k)) ⟨m, M⟩ middle₁ ∧
      MatrixReachable (vps_step (k := k)) middle₁ middle₂ ∧
      MatrixReachable (ppm_step (k := k)) middle₂ ⟨n, M'⟩

-- LEMMA 4: reorder PPS/VPS/PPM cascades into PPS-then-VPS-then-PPM form
axiom ordered_rearrangement_of_pps_vps_ppm_cascade {k : Nat} {m : Nat} {n : Nat}
    (M : ConditionalProbabilityMatrix k m)
    (M' : ConditionalProbabilityMatrix k n)
    (h_reachable : reachable_by_pps_vps_ppm M M') :
    reachable_by_ordered_pps_vps_ppm M M'

theorem lemma_4_operation_reordering {k : Nat} {m : Nat} {n : Nat}
    (M : ConditionalProbabilityMatrix k m)
    (M' : ConditionalProbabilityMatrix k n)
    (h_reachable : reachable_by_pps_vps_ppm M M') :
    reachable_by_ordered_pps_vps_ppm M M' := by
  exact ordered_rearrangement_of_pps_vps_ppm_cascade M M' h_reachable

-- LEMMA 5: PPM, PPS, and VPS preserve perfect representability
theorem ColumnTransport.forward_eq_iff {α β : Type}
    (transport : ColumnTransport α β) (a : α) (b : β) :
    transport.forward a = b ↔ a = transport.backward b := by
  constructor
  · intro h
    calc
      a = transport.backward (transport.forward a) := by
        symm
        exact transport.left_inv a
      _ = transport.backward b := by rw [h]
  · intro h
    calc
      transport.forward a = transport.forward (transport.backward b) := by rw [h]
      _ = b := transport.right_inv b

theorem ppm_operation_preserves_perfect_representability {k m n : Nat}
    (M : ConditionalProbabilityMatrix k m)
    (M' : ConditionalProbabilityMatrix k n)
    (h_op : is_ppm_operation M M')
    (h_repr : matrix_perfectly_representable M) :
    matrix_perfectly_representable M' := by
  classical
  rcases h_op with ⟨_, _, _, source₁, source₂, h_source_ne, _, target, _, transport, h_target, h_rest⟩
  rcases h_repr with ⟨representation, h_representation⟩
  let newRepresentation : CanonicalFunctionalRepresentation (Fin k) (Fin n) :=
    { W := representation.W
      pW := representation.pW
      decode := fun i w =>
        if h₁ : representation.decode i w = source₁ then
          target
        else if h₂ : representation.decode i w = source₂ then
          target
        else
          (transport.forward ⟨representation.decode i w, h₁, h₂⟩).1 }
  refine ⟨newRepresentation, ?_⟩
  intro i y
  by_cases hy_target : y = target
  · subst y
    have h_target_integrand :
        ∀ w : representation.W,
          represented_mass_integrand newRepresentation i target w =
            represented_mass_integrand representation i source₁ w +
              represented_mass_integrand representation i source₂ w := by
      intro w
      by_cases h₁ : representation.decode i w = source₁
      · have h_decode : newRepresentation.decode i w = target := by
          simp [newRepresentation, h₁]
        have h₂ : representation.decode i w ≠ source₂ := by
          intro h₂
          exact h_source_ne (h₁.symm.trans h₂)
        rw [represented_mass_integrand_of_eq newRepresentation i target w h_decode,
          represented_mass_integrand_of_eq representation i source₁ w h₁,
          represented_mass_integrand_of_ne representation i source₂ w h₂]
        rw [Rat.add_zero]
      · by_cases h₂ : representation.decode i w = source₂
        · have h_decode : newRepresentation.decode i w = target := by
            simp [newRepresentation, h₂]
          rw [represented_mass_integrand_of_eq newRepresentation i target w h_decode,
            represented_mass_integrand_of_ne representation i source₁ w h₁,
            represented_mass_integrand_of_eq representation i source₂ w h₂]
          rw [Rat.zero_add]
        · have h_decode : newRepresentation.decode i w ≠ target := by
            intro h_decode
            have h_forward : (transport.forward ⟨representation.decode i w, h₁, h₂⟩).1 = target := by
              simpa [newRepresentation, h₁, h₂] using h_decode
            exact (transport.forward ⟨representation.decode i w, h₁, h₂⟩).2 h_forward
          rw [represented_mass_integrand_of_ne newRepresentation i target w h_decode,
            represented_mass_integrand_of_ne representation i source₁ w h₁,
            represented_mass_integrand_of_ne representation i source₂ w h₂]
          rw [Rat.zero_add]
    calc
      M'.entry i target = M.entry i source₁ + M.entry i source₂ := h_target i
      _ = represented_mass representation i source₁ + represented_mass representation i source₂ := by
            rw [h_representation i source₁, h_representation i source₂]
      _ = discrete_sum (represented_mass_integrand representation i source₁) +
            discrete_sum (represented_mass_integrand representation i source₂) := by
            rw [represented_mass_eq, represented_mass_eq]
      _ = discrete_sum (fun w : representation.W =>
            represented_mass_integrand representation i source₁ w +
              represented_mass_integrand representation i source₂ w) := by
            symm
            exact InfoTheory.discrete_sum_add _ _
      _ = discrete_sum (represented_mass_integrand newRepresentation i target) := by
            symm
            apply InfoTheory.discrete_sum_congr
            intro w
            exact h_target_integrand w
      _ = represented_mass newRepresentation i target := by
            rw [represented_mass_eq]
  · let oldColumn : ColumnsExceptTwo source₁ source₂ :=
        transport.backward ⟨y, hy_target⟩
    have h_y : (transport.forward oldColumn).1 = y := by
      simpa [oldColumn] using congrArg Subtype.val (transport.right_inv ⟨y, hy_target⟩)
    have h_target_ne_y : target ≠ y := fun h => hy_target h.symm
    have h_old_integrand :
        ∀ w : representation.W,
          represented_mass_integrand newRepresentation i y w =
            represented_mass_integrand representation i oldColumn.1 w := by
      intro w
      by_cases h₁ : representation.decode i w = source₁
      · have h_decode : newRepresentation.decode i w = target := by
          simp [newRepresentation, h₁]
        have h_new_ne : newRepresentation.decode i w ≠ y := by
          intro h_new
          exact h_target_ne_y (h_decode.symm.trans h_new)
        have h_old_ne : representation.decode i w ≠ oldColumn.1 := by
          intro h_old
          exact oldColumn.2.1 (h_old.symm.trans h₁)
        rw [represented_mass_integrand_of_ne newRepresentation i y w h_new_ne,
          represented_mass_integrand_of_ne representation i oldColumn.1 w h_old_ne]
      · by_cases h₂ : representation.decode i w = source₂
        · have h_decode : newRepresentation.decode i w = target := by
            simp [newRepresentation, h₂]
          have h_new_ne : newRepresentation.decode i w ≠ y := by
            intro h_new
            exact h_target_ne_y (h_decode.symm.trans h_new)
          have h_old_ne : representation.decode i w ≠ oldColumn.1 := by
            intro h_old
            exact oldColumn.2.2 (h_old.symm.trans h₂)
          rw [represented_mass_integrand_of_ne newRepresentation i y w h_new_ne,
            represented_mass_integrand_of_ne representation i oldColumn.1 w h_old_ne]
        · by_cases h_hit : (transport.forward ⟨representation.decode i w, h₁, h₂⟩).1 = y
          · have h_eq_sub :
                transport.forward ⟨representation.decode i w, h₁, h₂⟩ = ⟨y, hy_target⟩ :=
              Subtype.ext h_hit
            have h_eq_old :
                ⟨representation.decode i w, h₁, h₂⟩ = oldColumn := by
              simpa [oldColumn] using
                (ColumnTransport.forward_eq_iff transport
                  ⟨representation.decode i w, h₁, h₂⟩
                  ⟨y, hy_target⟩).mp h_eq_sub
            have h_old : representation.decode i w = oldColumn.1 :=
              congrArg Subtype.val h_eq_old
            have h_decode : newRepresentation.decode i w = y := by
              simpa [newRepresentation, h₁, h₂] using h_hit
            rw [represented_mass_integrand_of_eq newRepresentation i y w h_decode,
              represented_mass_integrand_of_eq representation i oldColumn.1 w h_old]
          · have h_old_ne : representation.decode i w ≠ oldColumn.1 := by
              intro h_old
              apply h_hit
              calc
                (transport.forward ⟨representation.decode i w, h₁, h₂⟩).1
                    = (transport.forward oldColumn).1 := by
                        have h_eq_old :
                            ⟨representation.decode i w, h₁, h₂⟩ = oldColumn := Subtype.ext h_old
                        rw [h_eq_old]
                _ = y := h_y
            have h_new_ne : newRepresentation.decode i w ≠ y := by
              intro h_new
              apply h_hit
              simpa [newRepresentation, h₁, h₂] using h_new
            rw [represented_mass_integrand_of_ne newRepresentation i y w h_new_ne,
              represented_mass_integrand_of_ne representation i oldColumn.1 w h_old_ne]
    calc
      M'.entry i y = M'.entry i (transport.forward oldColumn).1 := by rw [h_y.symm]
      _ = M.entry i oldColumn.1 := h_rest oldColumn i
      _ = represented_mass representation i oldColumn.1 := h_representation i oldColumn.1
      _ = discrete_sum (represented_mass_integrand representation i oldColumn.1) := by
            rw [represented_mass_eq]
      _ = discrete_sum (represented_mass_integrand newRepresentation i y) := by
            symm
            apply InfoTheory.discrete_sum_congr
            intro w
            exact h_old_integrand w
      _ = represented_mass newRepresentation i y := by
            rw [represented_mass_eq]

theorem vps_operation_preserves_perfect_representability {k m n : Nat}
    (M : ConditionalProbabilityMatrix k m)
    (M' : ConditionalProbabilityMatrix k n)
    (h_op : is_vps_operation M M')
    (h_repr : matrix_perfectly_representable M) :
    matrix_perfectly_representable M' := by
  classical
  rcases h_op with ⟨_, _, _, source, splitter, left, right, h_left_ne_right, _, transport,
    h_left, h_right, h_rest⟩
  rcases h_repr with ⟨representation, h_representation⟩
  let newRepresentation : CanonicalFunctionalRepresentation (Fin k) (Fin n) :=
    { W := representation.W
      pW := representation.pW
      decode := fun i w =>
        if h_source : representation.decode i w = source then
          if splitter i then left else right
        else
          (transport.forward ⟨representation.decode i w, h_source⟩).1 }
  refine ⟨newRepresentation, ?_⟩
  intro i y
  by_cases hy_left : y = left
  · subst y
    by_cases h_split : splitter i
    · have h_left_integrand :
          ∀ w : representation.W,
            represented_mass_integrand newRepresentation i left w =
              represented_mass_integrand representation i source w := by
        intro w
        by_cases h_source : representation.decode i w = source
        · have h_decode : newRepresentation.decode i w = left := by
            simp [newRepresentation, h_source, h_split]
          rw [represented_mass_integrand_of_eq newRepresentation i left w h_decode,
            represented_mass_integrand_of_eq representation i source w h_source]
        · have h_decode : newRepresentation.decode i w ≠ left := by
            intro h_decode
            have h_forward : (transport.forward ⟨representation.decode i w, h_source⟩).1 = left := by
              simpa [newRepresentation, h_source, h_split] using h_decode
            exact (transport.forward ⟨representation.decode i w, h_source⟩).2.1 h_forward
          rw [represented_mass_integrand_of_ne newRepresentation i left w h_decode,
            represented_mass_integrand_of_ne representation i source w h_source]
      calc
        M'.entry i left = M.entry i source := by rw [h_left i, if_pos h_split]
        _ = represented_mass representation i source := h_representation i source
        _ = discrete_sum (represented_mass_integrand representation i source) := by
              rw [represented_mass_eq]
        _ = discrete_sum (represented_mass_integrand newRepresentation i left) := by
              symm
              apply InfoTheory.discrete_sum_congr
              intro w
              exact h_left_integrand w
        _ = represented_mass newRepresentation i left := by
              rw [represented_mass_eq]
    · have h_left_zero : represented_mass newRepresentation i left = 0 := by
        rw [represented_mass_eq]
        calc
          discrete_sum (represented_mass_integrand newRepresentation i left)
              = discrete_sum (fun _ : representation.W => 0) := by
                  apply InfoTheory.discrete_sum_congr
                  intro w
                  by_cases h_source : representation.decode i w = source
                  · have h_decode : newRepresentation.decode i w = right := by
                      simp [newRepresentation, h_source, h_split]
                    have h_ne : newRepresentation.decode i w ≠ left := by
                      intro h_eq
                      exact h_left_ne_right (h_eq.symm.trans h_decode)
                    rw [represented_mass_integrand_of_ne newRepresentation i left w h_ne]
                  · have h_decode : newRepresentation.decode i w ≠ left := by
                      intro h_decode
                      have h_forward : (transport.forward ⟨representation.decode i w, h_source⟩).1 = left := by
                        simpa [newRepresentation, h_source, h_split] using h_decode
                      exact (transport.forward ⟨representation.decode i w, h_source⟩).2.1 h_forward
                    rw [represented_mass_integrand_of_ne newRepresentation i left w h_decode]
          _ = 0 := InfoTheory.discrete_sum_zero
      calc
        M'.entry i left = 0 := by rw [h_left i, if_neg h_split]
        _ = represented_mass newRepresentation i left := h_left_zero.symm
  · by_cases hy_right : y = right
    · subst y
      by_cases h_split : splitter i
      · have h_right_zero : represented_mass newRepresentation i right = 0 := by
          rw [represented_mass_eq]
          calc
            discrete_sum (represented_mass_integrand newRepresentation i right)
                = discrete_sum (fun _ : representation.W => 0) := by
                    apply InfoTheory.discrete_sum_congr
                    intro w
                    by_cases h_source : representation.decode i w = source
                    · have h_decode : newRepresentation.decode i w = left := by
                        simp [newRepresentation, h_source, h_split]
                      have h_ne : newRepresentation.decode i w ≠ right := by
                        intro h_eq
                        exact h_left_ne_right (h_decode.symm.trans h_eq)
                      rw [represented_mass_integrand_of_ne newRepresentation i right w h_ne]
                    · have h_decode : newRepresentation.decode i w ≠ right := by
                        intro h_decode
                        have h_forward : (transport.forward ⟨representation.decode i w, h_source⟩).1 = right := by
                          simpa [newRepresentation, h_source, h_split] using h_decode
                        exact (transport.forward ⟨representation.decode i w, h_source⟩).2.2 h_forward
                      rw [represented_mass_integrand_of_ne newRepresentation i right w h_decode]
            _ = 0 := InfoTheory.discrete_sum_zero
        calc
          M'.entry i right = 0 := by rw [h_right i, if_pos h_split]
          _ = represented_mass newRepresentation i right := h_right_zero.symm
      · have h_right_integrand :
            ∀ w : representation.W,
              represented_mass_integrand newRepresentation i right w =
                represented_mass_integrand representation i source w := by
          intro w
          by_cases h_source : representation.decode i w = source
          · have h_decode : newRepresentation.decode i w = right := by
              simp [newRepresentation, h_source, h_split]
            rw [represented_mass_integrand_of_eq newRepresentation i right w h_decode,
              represented_mass_integrand_of_eq representation i source w h_source]
          · have h_decode : newRepresentation.decode i w ≠ right := by
              intro h_decode
              have h_forward : (transport.forward ⟨representation.decode i w, h_source⟩).1 = right := by
                simpa [newRepresentation, h_source, h_split] using h_decode
              exact (transport.forward ⟨representation.decode i w, h_source⟩).2.2 h_forward
            rw [represented_mass_integrand_of_ne newRepresentation i right w h_decode,
              represented_mass_integrand_of_ne representation i source w h_source]
        calc
          M'.entry i right = M.entry i source := by rw [h_right i, if_neg h_split]
          _ = represented_mass representation i source := h_representation i source
          _ = discrete_sum (represented_mass_integrand representation i source) := by
                rw [represented_mass_eq]
          _ = discrete_sum (represented_mass_integrand newRepresentation i right) := by
                symm
                apply InfoTheory.discrete_sum_congr
                intro w
                exact h_right_integrand w
          _ = represented_mass newRepresentation i right := by
                rw [represented_mass_eq]
    · let oldColumn : ColumnsExceptOne source :=
          transport.backward ⟨y, hy_left, hy_right⟩
      have h_y : (transport.forward oldColumn).1 = y := by
        simpa [oldColumn] using congrArg Subtype.val (transport.right_inv ⟨y, hy_left, hy_right⟩)
      have h_old_integrand :
          ∀ w : representation.W,
            represented_mass_integrand newRepresentation i y w =
              represented_mass_integrand representation i oldColumn.1 w := by
        intro w
        by_cases h_source : representation.decode i w = source
        · have h_new_ne : newRepresentation.decode i w ≠ y := by
            intro h_new
            by_cases h_split : splitter i
            · have h_decode : newRepresentation.decode i w = left := by
                simp [newRepresentation, h_source, h_split]
              exact hy_left (h_new.symm.trans h_decode)
            · have h_decode : newRepresentation.decode i w = right := by
                simp [newRepresentation, h_source, h_split]
              exact hy_right (h_new.symm.trans h_decode)
          have h_old_ne : representation.decode i w ≠ oldColumn.1 := by
            intro h_old
            exact oldColumn.2 (h_old.symm.trans h_source)
          rw [represented_mass_integrand_of_ne newRepresentation i y w h_new_ne,
            represented_mass_integrand_of_ne representation i oldColumn.1 w h_old_ne]
        · by_cases h_hit : (transport.forward ⟨representation.decode i w, h_source⟩).1 = y
          · have h_eq_sub :
                transport.forward ⟨representation.decode i w, h_source⟩ = ⟨y, hy_left, hy_right⟩ :=
              Subtype.ext h_hit
            have h_eq_old :
                ⟨representation.decode i w, h_source⟩ = oldColumn := by
              simpa [oldColumn] using
                (ColumnTransport.forward_eq_iff transport
                  ⟨representation.decode i w, h_source⟩
                  ⟨y, hy_left, hy_right⟩).mp h_eq_sub
            have h_old : representation.decode i w = oldColumn.1 :=
              congrArg Subtype.val h_eq_old
            have h_decode : newRepresentation.decode i w = y := by
              simpa [newRepresentation, h_source] using h_hit
            rw [represented_mass_integrand_of_eq newRepresentation i y w h_decode,
              represented_mass_integrand_of_eq representation i oldColumn.1 w h_old]
          · have h_old_ne : representation.decode i w ≠ oldColumn.1 := by
              intro h_old
              apply h_hit
              calc
                (transport.forward ⟨representation.decode i w, h_source⟩).1
                    = (transport.forward oldColumn).1 := by
                        have h_eq_old : ⟨representation.decode i w, h_source⟩ = oldColumn :=
                          Subtype.ext h_old
                        rw [h_eq_old]
                _ = y := h_y
            have h_new_ne : newRepresentation.decode i w ≠ y := by
              intro h_new
              apply h_hit
              simpa [newRepresentation, h_source] using h_new
            rw [represented_mass_integrand_of_ne newRepresentation i y w h_new_ne,
              represented_mass_integrand_of_ne representation i oldColumn.1 w h_old_ne]
      calc
        M'.entry i y = M'.entry i (transport.forward oldColumn).1 := by rw [h_y.symm]
        _ = M.entry i oldColumn.1 := h_rest oldColumn i
        _ = represented_mass representation i oldColumn.1 := h_representation i oldColumn.1
        _ = discrete_sum (represented_mass_integrand representation i oldColumn.1) := by
              rw [represented_mass_eq]
        _ = discrete_sum (represented_mass_integrand newRepresentation i y) := by
              symm
              apply InfoTheory.discrete_sum_congr
              intro w
              exact h_old_integrand w
        _ = represented_mass newRepresentation i y := by
              rw [represented_mass_eq]

theorem pps_operation_preserves_perfect_representability {k m n : Nat}
    (M : ConditionalProbabilityMatrix k m)
    (M' : ConditionalProbabilityMatrix k n)
    (h_op : is_pps_operation M M')
    (h_repr : matrix_perfectly_representable M) :
    matrix_perfectly_representable M' := by
  classical
  rcases h_op with ⟨_, _, _, source, α, _, _, left, right, h_left_ne_right, _, transport,
    h_left, h_right, h_rest⟩
  rcases h_repr with ⟨representation, h_representation⟩
  let newRepresentation : CanonicalFunctionalRepresentation (Fin k) (Fin n) :=
    { W := Sum representation.W representation.W
      pW := fun
        | .inl w => α * representation.pW w
        | .inr w => (1 - α) * representation.pW w
      decode := fun i sw =>
        match sw with
        | .inl w =>
            if h_source : representation.decode i w = source then
              left
            else
              (transport.forward ⟨representation.decode i w, h_source⟩).1
        | .inr w =>
            if h_source : representation.decode i w = source then
              right
            else
              (transport.forward ⟨representation.decode i w, h_source⟩).1 }
  refine ⟨newRepresentation, ?_⟩
  intro i y
  by_cases hy_left : y = left
  · subst y
    have h_inl_integrand :
        ∀ w : representation.W,
          represented_mass_integrand newRepresentation i left (.inl w) =
            α * represented_mass_integrand representation i source w := by
      intro w
      by_cases h_source : representation.decode i w = source
      · have h_decode : newRepresentation.decode i (.inl w) = left := by
          simp [newRepresentation, h_source]
        rw [represented_mass_integrand_of_eq newRepresentation i left (.inl w) h_decode,
          represented_mass_integrand_of_eq representation i source w h_source]
      · have h_decode : newRepresentation.decode i (.inl w) ≠ left := by
          intro h_decode
          have h_forward : (transport.forward ⟨representation.decode i w, h_source⟩).1 = left := by
            simpa [newRepresentation, h_source] using h_decode
          exact (transport.forward ⟨representation.decode i w, h_source⟩).2.1 h_forward
        rw [represented_mass_integrand_of_ne newRepresentation i left (.inl w) h_decode,
          represented_mass_integrand_of_ne representation i source w h_source]
        simp
    have h_inr_zero_sum :
        discrete_sum (fun w : representation.W =>
          represented_mass_integrand newRepresentation i left (.inr w)) = 0 := by
      calc
        discrete_sum (fun w : representation.W =>
            represented_mass_integrand newRepresentation i left (.inr w))
            = discrete_sum (fun _ : representation.W => 0) := by
                apply InfoTheory.discrete_sum_congr
                intro w
                by_cases h_source : representation.decode i w = source
                · have h_decode : newRepresentation.decode i (.inr w) = right := by
                    simp [newRepresentation, h_source]
                  have h_ne : newRepresentation.decode i (.inr w) ≠ left := by
                    intro h_eq
                    exact h_left_ne_right (h_eq.symm.trans h_decode)
                  rw [represented_mass_integrand_of_ne newRepresentation i left (.inr w) h_ne]
                · have h_decode : newRepresentation.decode i (.inr w) ≠ left := by
                    intro h_decode
                    have h_forward : (transport.forward ⟨representation.decode i w, h_source⟩).1 = left := by
                      simpa [newRepresentation, h_source] using h_decode
                    exact (transport.forward ⟨representation.decode i w, h_source⟩).2.1 h_forward
                  rw [represented_mass_integrand_of_ne newRepresentation i left (.inr w) h_decode]
        _ = 0 := InfoTheory.discrete_sum_zero
    calc
      M'.entry i left = α * M.entry i source := h_left i
      _ = α * represented_mass representation i source := by rw [h_representation i source]
      _ = α * discrete_sum (represented_mass_integrand representation i source) := by
            rw [represented_mass_eq]
      _ = discrete_sum (fun w : representation.W =>
            α * represented_mass_integrand representation i source w) := by
            symm
            exact InfoTheory.discrete_sum_mul_left α _
      _ = discrete_sum (fun w : representation.W =>
            represented_mass_integrand newRepresentation i left (.inl w)) := by
            symm
            apply InfoTheory.discrete_sum_congr
            intro w
            exact h_inl_integrand w
      _ = discrete_sum (fun w : representation.W =>
            represented_mass_integrand newRepresentation i left (.inl w)) +
            discrete_sum (fun w : representation.W =>
              represented_mass_integrand newRepresentation i left (.inr w)) := by
            rw [h_inr_zero_sum, Rat.add_zero]
      _ = discrete_sum (represented_mass_integrand newRepresentation i left) := by
            symm
            exact InfoTheory.discrete_sum_sum (represented_mass_integrand newRepresentation i left)
      _ = represented_mass newRepresentation i left := by
            rw [represented_mass_eq]
  · by_cases hy_right : y = right
    · subst y
      have h_inr_integrand :
          ∀ w : representation.W,
            represented_mass_integrand newRepresentation i right (.inr w) =
              (1 - α) * represented_mass_integrand representation i source w := by
        intro w
        by_cases h_source : representation.decode i w = source
        · have h_decode : newRepresentation.decode i (.inr w) = right := by
            simp [newRepresentation, h_source]
          rw [represented_mass_integrand_of_eq newRepresentation i right (.inr w) h_decode,
            represented_mass_integrand_of_eq representation i source w h_source]
        · have h_decode : newRepresentation.decode i (.inr w) ≠ right := by
            intro h_decode
            have h_forward : (transport.forward ⟨representation.decode i w, h_source⟩).1 = right := by
              simpa [newRepresentation, h_source] using h_decode
            exact (transport.forward ⟨representation.decode i w, h_source⟩).2.2 h_forward
          rw [represented_mass_integrand_of_ne newRepresentation i right (.inr w) h_decode,
            represented_mass_integrand_of_ne representation i source w h_source]
          simp
      have h_inl_zero_sum :
          discrete_sum (fun w : representation.W =>
            represented_mass_integrand newRepresentation i right (.inl w)) = 0 := by
        calc
          discrete_sum (fun w : representation.W =>
              represented_mass_integrand newRepresentation i right (.inl w))
              = discrete_sum (fun _ : representation.W => 0) := by
                  apply InfoTheory.discrete_sum_congr
                  intro w
                  by_cases h_source : representation.decode i w = source
                  · have h_decode : newRepresentation.decode i (.inl w) = left := by
                      simp [newRepresentation, h_source]
                    have h_ne : newRepresentation.decode i (.inl w) ≠ right := by
                      intro h_eq
                      exact h_left_ne_right (h_decode.symm.trans h_eq)
                    rw [represented_mass_integrand_of_ne newRepresentation i right (.inl w) h_ne]
                  · have h_decode : newRepresentation.decode i (.inl w) ≠ right := by
                      intro h_decode
                      have h_forward : (transport.forward ⟨representation.decode i w, h_source⟩).1 = right := by
                        simpa [newRepresentation, h_source] using h_decode
                      exact (transport.forward ⟨representation.decode i w, h_source⟩).2.2 h_forward
                    rw [represented_mass_integrand_of_ne newRepresentation i right (.inl w) h_decode]
          _ = 0 := InfoTheory.discrete_sum_zero
      calc
        M'.entry i right = (1 - α) * M.entry i source := h_right i
        _ = (1 - α) * represented_mass representation i source := by rw [h_representation i source]
        _ = (1 - α) * discrete_sum (represented_mass_integrand representation i source) := by
              rw [represented_mass_eq]
        _ = discrete_sum (fun w : representation.W =>
              (1 - α) * represented_mass_integrand representation i source w) := by
              symm
              exact InfoTheory.discrete_sum_mul_left (1 - α) _
        _ = discrete_sum (fun w : representation.W =>
              represented_mass_integrand newRepresentation i right (.inr w)) := by
              symm
              apply InfoTheory.discrete_sum_congr
              intro w
              exact h_inr_integrand w
        _ = discrete_sum (fun w : representation.W =>
              represented_mass_integrand newRepresentation i right (.inl w)) +
              discrete_sum (fun w : representation.W =>
                represented_mass_integrand newRepresentation i right (.inr w)) := by
              rw [h_inl_zero_sum, Rat.zero_add]
        _ = discrete_sum (represented_mass_integrand newRepresentation i right) := by
              symm
              exact InfoTheory.discrete_sum_sum (represented_mass_integrand newRepresentation i right)
        _ = represented_mass newRepresentation i right := by
              rw [represented_mass_eq]
    · let oldColumn : ColumnsExceptOne source :=
          transport.backward ⟨y, hy_left, hy_right⟩
      have h_y : (transport.forward oldColumn).1 = y := by
        simpa [oldColumn] using congrArg Subtype.val (transport.right_inv ⟨y, hy_left, hy_right⟩)
      have h_inl_old_integrand :
          ∀ w : representation.W,
            represented_mass_integrand newRepresentation i y (.inl w) =
              α * represented_mass_integrand representation i oldColumn.1 w := by
        intro w
        by_cases h_source : representation.decode i w = source
        · have h_new_ne : newRepresentation.decode i (.inl w) ≠ y := by
            intro h_new
            have h_decode : newRepresentation.decode i (.inl w) = left := by
              simp [newRepresentation, h_source]
            exact hy_left (h_new.symm.trans h_decode)
          have h_old_ne : representation.decode i w ≠ oldColumn.1 := by
            intro h_old
            exact oldColumn.2 (h_old.symm.trans h_source)
          rw [represented_mass_integrand_of_ne newRepresentation i y (.inl w) h_new_ne,
            represented_mass_integrand_of_ne representation i oldColumn.1 w h_old_ne]
          simp
        · by_cases h_hit : (transport.forward ⟨representation.decode i w, h_source⟩).1 = y
          · have h_eq_sub :
                transport.forward ⟨representation.decode i w, h_source⟩ = ⟨y, hy_left, hy_right⟩ :=
              Subtype.ext h_hit
            have h_eq_old :
                ⟨representation.decode i w, h_source⟩ = oldColumn := by
              simpa [oldColumn] using
                (ColumnTransport.forward_eq_iff transport
                  ⟨representation.decode i w, h_source⟩
                  ⟨y, hy_left, hy_right⟩).mp h_eq_sub
            have h_old : representation.decode i w = oldColumn.1 :=
              congrArg Subtype.val h_eq_old
            have h_decode : newRepresentation.decode i (.inl w) = y := by
              simpa [newRepresentation, h_source] using h_hit
            rw [represented_mass_integrand_of_eq newRepresentation i y (.inl w) h_decode,
              represented_mass_integrand_of_eq representation i oldColumn.1 w h_old]
          · have h_old_ne : representation.decode i w ≠ oldColumn.1 := by
              intro h_old
              apply h_hit
              calc
                (transport.forward ⟨representation.decode i w, h_source⟩).1
                    = (transport.forward oldColumn).1 := by
                        have h_eq_old : ⟨representation.decode i w, h_source⟩ = oldColumn :=
                          Subtype.ext h_old
                        rw [h_eq_old]
                _ = y := h_y
            have h_new_ne : newRepresentation.decode i (.inl w) ≠ y := by
              intro h_new
              apply h_hit
              simpa [newRepresentation, h_source] using h_new
            rw [represented_mass_integrand_of_ne newRepresentation i y (.inl w) h_new_ne,
              represented_mass_integrand_of_ne representation i oldColumn.1 w h_old_ne]
            simp
      have h_inr_old_integrand :
          ∀ w : representation.W,
            represented_mass_integrand newRepresentation i y (.inr w) =
              (1 - α) * represented_mass_integrand representation i oldColumn.1 w := by
        intro w
        by_cases h_source : representation.decode i w = source
        · have h_new_ne : newRepresentation.decode i (.inr w) ≠ y := by
            intro h_new
            have h_decode : newRepresentation.decode i (.inr w) = right := by
              simp [newRepresentation, h_source]
            exact hy_right (h_new.symm.trans h_decode)
          have h_old_ne : representation.decode i w ≠ oldColumn.1 := by
            intro h_old
            exact oldColumn.2 (h_old.symm.trans h_source)
          rw [represented_mass_integrand_of_ne newRepresentation i y (.inr w) h_new_ne,
            represented_mass_integrand_of_ne representation i oldColumn.1 w h_old_ne]
          simp
        · by_cases h_hit : (transport.forward ⟨representation.decode i w, h_source⟩).1 = y
          · have h_eq_sub :
                transport.forward ⟨representation.decode i w, h_source⟩ = ⟨y, hy_left, hy_right⟩ :=
              Subtype.ext h_hit
            have h_eq_old :
                ⟨representation.decode i w, h_source⟩ = oldColumn := by
              simpa [oldColumn] using
                (ColumnTransport.forward_eq_iff transport
                  ⟨representation.decode i w, h_source⟩
                  ⟨y, hy_left, hy_right⟩).mp h_eq_sub
            have h_old : representation.decode i w = oldColumn.1 :=
              congrArg Subtype.val h_eq_old
            have h_decode : newRepresentation.decode i (.inr w) = y := by
              simpa [newRepresentation, h_source] using h_hit
            rw [represented_mass_integrand_of_eq newRepresentation i y (.inr w) h_decode,
              represented_mass_integrand_of_eq representation i oldColumn.1 w h_old]
          · have h_old_ne : representation.decode i w ≠ oldColumn.1 := by
              intro h_old
              apply h_hit
              calc
                (transport.forward ⟨representation.decode i w, h_source⟩).1
                    = (transport.forward oldColumn).1 := by
                        have h_eq_old : ⟨representation.decode i w, h_source⟩ = oldColumn :=
                          Subtype.ext h_old
                        rw [h_eq_old]
                _ = y := h_y
            have h_new_ne : newRepresentation.decode i (.inr w) ≠ y := by
              intro h_new
              apply h_hit
              simpa [newRepresentation, h_source] using h_new
            rw [represented_mass_integrand_of_ne newRepresentation i y (.inr w) h_new_ne,
              represented_mass_integrand_of_ne representation i oldColumn.1 w h_old_ne]
            simp
      have h_inl_sum :
          discrete_sum (fun w : representation.W =>
            represented_mass_integrand newRepresentation i y (.inl w)) =
              discrete_sum (fun w : representation.W =>
                α * represented_mass_integrand representation i oldColumn.1 w) := by
        apply InfoTheory.discrete_sum_congr
        intro w
        exact h_inl_old_integrand w
      have h_inr_sum :
          discrete_sum (fun w : representation.W =>
            represented_mass_integrand newRepresentation i y (.inr w)) =
              discrete_sum (fun w : representation.W =>
                (1 - α) * represented_mass_integrand representation i oldColumn.1 w) := by
        apply InfoTheory.discrete_sum_congr
        intro w
        exact h_inr_old_integrand w
      calc
        M'.entry i y = M'.entry i (transport.forward oldColumn).1 := by rw [h_y.symm]
        _ = M.entry i oldColumn.1 := h_rest oldColumn i
        _ = represented_mass representation i oldColumn.1 := h_representation i oldColumn.1
        _ = discrete_sum (represented_mass_integrand representation i oldColumn.1) := by
              rw [represented_mass_eq]
        _ = discrete_sum (fun w : representation.W =>
              α * represented_mass_integrand representation i oldColumn.1 w) +
              discrete_sum (fun w : representation.W =>
                (1 - α) * represented_mass_integrand representation i oldColumn.1 w) := by
              symm
              exact InfoTheory.discrete_sum_split_weight α _
        _ = discrete_sum (fun w : representation.W =>
              represented_mass_integrand newRepresentation i y (.inl w)) +
              discrete_sum (fun w : representation.W =>
                represented_mass_integrand newRepresentation i y (.inr w)) := by
              rw [← h_inl_sum, ← h_inr_sum]
        _ = discrete_sum (represented_mass_integrand newRepresentation i y) := by
              symm
              exact InfoTheory.discrete_sum_sum (represented_mass_integrand newRepresentation i y)
        _ = represented_mass newRepresentation i y := by
              rw [represented_mass_eq]

theorem perfect_representability_preserved_by_pps_vps {k m n : Nat}
    (M : ConditionalProbabilityMatrix k m)
    (M' : ConditionalProbabilityMatrix k n)
    (h_op : Or (is_pps_operation M M') (is_vps_operation M M'))
    (h_repr : matrix_perfectly_representable M) :
    matrix_perfectly_representable M' := by
  rcases h_op with h_pps | h_vps
  · exact pps_operation_preserves_perfect_representability M M' h_pps h_repr
  · exact vps_operation_preserves_perfect_representability M M' h_vps h_repr

theorem perfect_representability_preserved_by_ppm_pps_vps {k m n : Nat}
  (M : ConditionalProbabilityMatrix k m)
  (M' : ConditionalProbabilityMatrix k n)
  (h_op : Or (is_ppm_operation M M') (Or (is_pps_operation M M') (is_vps_operation M M')))
  (h_repr : matrix_perfectly_representable M) :
  matrix_perfectly_representable M' := by
  rcases h_op with h_ppm | h_pps_vps
  · exact ppm_operation_preserves_perfect_representability M M' h_ppm h_repr
  · exact perfect_representability_preserved_by_pps_vps M M' h_pps_vps h_repr

theorem lemma_5_preservation_of_perfect_representability {k m n : Nat}
    (M : ConditionalProbabilityMatrix k m)
    (M' : ConditionalProbabilityMatrix k n)
    (h_op : Or (is_ppm_operation M M') (Or (is_pps_operation M M') (is_vps_operation M M')))
    (h_repr : matrix_perfectly_representable M) :
    matrix_perfectly_representable M' := by
  exact perfect_representability_preserved_by_ppm_pps_vps M M' h_op h_repr

theorem pps_operation_reflects_perfect_representability {k m n : Nat}
    (M : ConditionalProbabilityMatrix k m)
    (M' : ConditionalProbabilityMatrix k n)
    (h_op : is_pps_operation M M')
    (h_repr : matrix_perfectly_representable M') :
    matrix_perfectly_representable M := by
  classical
  rcases h_op with ⟨_, _, _, source, α, _, _, left, right, h_left_ne_right, _, transport,
    h_left, h_right, h_rest⟩
  rcases h_repr with ⟨representation, h_representation⟩
  let newRepresentation : CanonicalFunctionalRepresentation (Fin k) (Fin m) :=
    { W := representation.W
      pW := representation.pW
      decode := fun i w =>
        if h_left_decode : representation.decode i w = left then
          source
        else if h_right_decode : representation.decode i w = right then
          source
        else
          (transport.backward ⟨representation.decode i w, h_left_decode, h_right_decode⟩).1 }
  refine ⟨newRepresentation, ?_⟩
  intro i y
  by_cases hy_source : y = source
  · subst y
    have h_source_integrand :
        ∀ w : representation.W,
          represented_mass_integrand newRepresentation i source w =
            represented_mass_integrand representation i left w +
              represented_mass_integrand representation i right w := by
      intro w
      by_cases h_left_decode : representation.decode i w = left
      · have h_decode : newRepresentation.decode i w = source := by
          simp [newRepresentation, h_left_decode]
        have h_right_decode : representation.decode i w ≠ right := by
          intro h_right_decode
          exact h_left_ne_right (h_left_decode.symm.trans h_right_decode)
        rw [represented_mass_integrand_of_eq newRepresentation i source w h_decode,
          represented_mass_integrand_of_eq representation i left w h_left_decode,
          represented_mass_integrand_of_ne representation i right w h_right_decode]
        rw [Rat.add_zero]
      · by_cases h_right_decode : representation.decode i w = right
        · have h_decode : newRepresentation.decode i w = source := by
            simp [newRepresentation, h_right_decode]
          rw [represented_mass_integrand_of_eq newRepresentation i source w h_decode,
            represented_mass_integrand_of_ne representation i left w h_left_decode,
            represented_mass_integrand_of_eq representation i right w h_right_decode]
          rw [Rat.zero_add]
        · have h_decode : newRepresentation.decode i w ≠ source := by
            intro h_decode
            have h_backward :
                (transport.backward ⟨representation.decode i w, h_left_decode, h_right_decode⟩).1 = source := by
              simpa [newRepresentation, h_left_decode, h_right_decode] using h_decode
            exact (transport.backward ⟨representation.decode i w, h_left_decode, h_right_decode⟩).2 h_backward
          rw [represented_mass_integrand_of_ne newRepresentation i source w h_decode,
            represented_mass_integrand_of_ne representation i left w h_left_decode,
            represented_mass_integrand_of_ne representation i right w h_right_decode]
          rw [Rat.zero_add]
    have h_alpha_sum : α + (1 - α) = 1 := by
      rw [Rat.sub_eq_add_neg, Rat.add_comm 1 (-α), ← Rat.add_assoc, Rat.add_neg_cancel, Rat.zero_add]
    calc
      M.entry i source = M'.entry i left + M'.entry i right := by
        rw [h_left i, h_right i]
        calc
          M.entry i source = (α + (1 - α)) * M.entry i source := by
            rw [h_alpha_sum, Rat.one_mul]
          _ = α * M.entry i source + (1 - α) * M.entry i source := by
            rw [Rat.add_mul]
      _ = represented_mass representation i left + represented_mass representation i right := by
            rw [h_representation i left, h_representation i right]
      _ = discrete_sum (represented_mass_integrand representation i left) +
            discrete_sum (represented_mass_integrand representation i right) := by
            rw [represented_mass_eq, represented_mass_eq]
      _ = discrete_sum (fun w : representation.W =>
            represented_mass_integrand representation i left w +
              represented_mass_integrand representation i right w) := by
            symm
            exact InfoTheory.discrete_sum_add _ _
      _ = discrete_sum (represented_mass_integrand newRepresentation i source) := by
            symm
            apply InfoTheory.discrete_sum_congr
            intro w
            exact h_source_integrand w
      _ = represented_mass newRepresentation i source := by
            rw [represented_mass_eq]
  · let oldColumn : ColumnsExceptPair left right :=
        transport.forward ⟨y, hy_source⟩
    have h_y : (transport.backward oldColumn).1 = y := by
      simpa [oldColumn] using congrArg Subtype.val (transport.left_inv ⟨y, hy_source⟩)
    have h_old_integrand :
        ∀ w : representation.W,
          represented_mass_integrand newRepresentation i y w =
            represented_mass_integrand representation i oldColumn.1 w := by
      intro w
      by_cases h_left_decode : representation.decode i w = left
      · have h_decode : newRepresentation.decode i w = source := by
          simp [newRepresentation, h_left_decode]
        have h_new_ne : newRepresentation.decode i w ≠ y := by
          intro h_new
          exact hy_source (h_new.symm.trans h_decode)
        have h_old_ne : representation.decode i w ≠ oldColumn.1 := by
          intro h_old
          exact oldColumn.2.1 (h_old.symm.trans h_left_decode)
        rw [represented_mass_integrand_of_ne newRepresentation i y w h_new_ne,
          represented_mass_integrand_of_ne representation i oldColumn.1 w h_old_ne]
      · by_cases h_right_decode : representation.decode i w = right
        · have h_decode : newRepresentation.decode i w = source := by
            simp [newRepresentation, h_right_decode]
          have h_new_ne : newRepresentation.decode i w ≠ y := by
            intro h_new
            exact hy_source (h_new.symm.trans h_decode)
          have h_old_ne : representation.decode i w ≠ oldColumn.1 := by
            intro h_old
            exact oldColumn.2.2 (h_old.symm.trans h_right_decode)
          rw [represented_mass_integrand_of_ne newRepresentation i y w h_new_ne,
            represented_mass_integrand_of_ne representation i oldColumn.1 w h_old_ne]
        · by_cases h_hit : (transport.backward ⟨representation.decode i w, h_left_decode, h_right_decode⟩).1 = y
          · have h_eq_sub :
                transport.backward ⟨representation.decode i w, h_left_decode, h_right_decode⟩ = ⟨y, hy_source⟩ :=
              Subtype.ext h_hit
            have h_eq_old :
                ⟨representation.decode i w, h_left_decode, h_right_decode⟩ = oldColumn := by
              calc
                ⟨representation.decode i w, h_left_decode, h_right_decode⟩ =
                    transport.forward
                      (transport.backward ⟨representation.decode i w, h_left_decode, h_right_decode⟩) := by
                        symm
                        exact transport.right_inv _
                _ = transport.forward ⟨y, hy_source⟩ := by rw [h_eq_sub]
                _ = oldColumn := by rfl
            have h_old : representation.decode i w = oldColumn.1 :=
              congrArg Subtype.val h_eq_old
            have h_decode : newRepresentation.decode i w = y := by
              simpa [newRepresentation, h_left_decode, h_right_decode] using h_hit
            rw [represented_mass_integrand_of_eq newRepresentation i y w h_decode,
              represented_mass_integrand_of_eq representation i oldColumn.1 w h_old]
          · have h_old_ne : representation.decode i w ≠ oldColumn.1 := by
              intro h_old
              apply h_hit
              calc
                (transport.backward ⟨representation.decode i w, h_left_decode, h_right_decode⟩).1
                    = (transport.backward oldColumn).1 := by
                        have h_eq_old :
                            ⟨representation.decode i w, h_left_decode, h_right_decode⟩ = oldColumn :=
                          Subtype.ext h_old
                        rw [h_eq_old]
                _ = y := h_y
            have h_new_ne : newRepresentation.decode i w ≠ y := by
              intro h_new
              apply h_hit
              simpa [newRepresentation, h_left_decode, h_right_decode] using h_new
            rw [represented_mass_integrand_of_ne newRepresentation i y w h_new_ne,
              represented_mass_integrand_of_ne representation i oldColumn.1 w h_old_ne]
    calc
      M.entry i y = M'.entry i oldColumn.1 := by
        symm
        exact h_rest ⟨y, hy_source⟩ i
      _ = represented_mass representation i oldColumn.1 := h_representation i oldColumn.1
      _ = discrete_sum (represented_mass_integrand representation i oldColumn.1) := by
            rw [represented_mass_eq]
      _ = discrete_sum (represented_mass_integrand newRepresentation i y) := by
            symm
            apply InfoTheory.discrete_sum_congr
            intro w
            exact h_old_integrand w
      _ = represented_mass newRepresentation i y := by
            rw [represented_mass_eq]

theorem pps_operation_preserves_nonrepresentability {k m n : Nat}
    (M : ConditionalProbabilityMatrix k m)
    (M' : ConditionalProbabilityMatrix k n)
    (h_op : is_pps_operation M M')
    (h_not_repr : Not (matrix_perfectly_representable M)) :
    Not (matrix_perfectly_representable M') := by
  intro h_repr
  exact h_not_repr (pps_operation_reflects_perfect_representability M M' h_op h_repr)

theorem vpm_operation_reflects_perfect_representability {k m n : Nat}
    (M : ConditionalProbabilityMatrix k m)
    (M' : ConditionalProbabilityMatrix k n)
    (h_op : is_vpm_operation M M')
    (h_repr : matrix_perfectly_representable M') :
    matrix_perfectly_representable M := by
  classical
  rcases h_op with ⟨_, _, _, source₁, source₂, h_source_ne, _, h_disjoint, target, _, transport,
    h_target, h_rest⟩
  rcases h_repr with ⟨representation, h_representation⟩
  let splitter : Fin k → Bool := fun i => if 0 < M.entry i source₁ then true else false
  let newRepresentation : CanonicalFunctionalRepresentation (Fin k) (Fin m) :=
    { W := representation.W
      pW := representation.pW
      decode := fun i w =>
        if h_target_decode : representation.decode i w = target then
          if splitter i then source₁ else source₂
        else
          (transport.backward ⟨representation.decode i w, h_target_decode⟩).1 }
  refine ⟨newRepresentation, ?_⟩
  intro i y
  by_cases hy_source₁ : y = source₁
  · subst y
    by_cases h_pos : 0 < M.entry i source₁
    · have h_source₁_integrand :
          ∀ w : representation.W,
            represented_mass_integrand newRepresentation i source₁ w =
              represented_mass_integrand representation i target w := by
        intro w
        by_cases h_target_decode : representation.decode i w = target
        · have h_decode : newRepresentation.decode i w = source₁ := by
            simp [newRepresentation, splitter, h_target_decode, h_pos]
          rw [represented_mass_integrand_of_eq newRepresentation i source₁ w h_decode,
            represented_mass_integrand_of_eq representation i target w h_target_decode]
        · have h_decode : newRepresentation.decode i w ≠ source₁ := by
            intro h_decode
            have h_backward : (transport.backward ⟨representation.decode i w, h_target_decode⟩).1 = source₁ := by
              simpa [newRepresentation, splitter, h_target_decode, h_pos] using h_decode
            exact (transport.backward ⟨representation.decode i w, h_target_decode⟩).2.1 h_backward
          rw [represented_mass_integrand_of_ne newRepresentation i source₁ w h_decode,
            represented_mass_integrand_of_ne representation i target w h_target_decode]

      have h_zero₂ : M.entry i source₂ = 0 := h_disjoint i h_pos
      calc
        M.entry i source₁ = M'.entry i target := by
          calc
            M.entry i source₁ = M.entry i source₁ + M.entry i source₂ := by rw [h_zero₂, Rat.add_zero]
            _ = M'.entry i target := by symm; exact h_target i
        _ = represented_mass representation i target := h_representation i target
        _ = discrete_sum (represented_mass_integrand representation i target) := by
              rw [represented_mass_eq]
        _ = discrete_sum (represented_mass_integrand newRepresentation i source₁) := by
              symm
              apply InfoTheory.discrete_sum_congr
              intro w
              exact h_source₁_integrand w
        _ = represented_mass newRepresentation i source₁ := by
              rw [represented_mass_eq]
    · have h_zero₁ : M.entry i source₁ = 0 :=
        Rat.le_antisymm (Rat.not_lt.mp h_pos) (M.nonnegative i source₁)
      have h_source₁_zero : represented_mass newRepresentation i source₁ = 0 := by
        rw [represented_mass_eq]
        calc
          discrete_sum (represented_mass_integrand newRepresentation i source₁)
              = discrete_sum (fun _ : representation.W => 0) := by
                  apply InfoTheory.discrete_sum_congr
                  intro w
                  by_cases h_target_decode : representation.decode i w = target
                  · have h_decode : newRepresentation.decode i w = source₂ := by
                      simp [newRepresentation, splitter, h_target_decode, h_pos]
                    have h_ne : newRepresentation.decode i w ≠ source₁ := by
                      intro h_eq
                      exact h_source_ne (h_eq.symm.trans h_decode)
                    rw [represented_mass_integrand_of_ne newRepresentation i source₁ w h_ne]
                  · have h_decode : newRepresentation.decode i w ≠ source₁ := by
                      intro h_decode
                      have h_backward : (transport.backward ⟨representation.decode i w, h_target_decode⟩).1 = source₁ := by
                        simpa [newRepresentation, splitter, h_target_decode, h_pos] using h_decode
                      exact (transport.backward ⟨representation.decode i w, h_target_decode⟩).2.1 h_backward
                    rw [represented_mass_integrand_of_ne newRepresentation i source₁ w h_decode]
          _ = 0 := InfoTheory.discrete_sum_zero
      calc
        M.entry i source₁ = 0 := h_zero₁
        _ = represented_mass newRepresentation i source₁ := h_source₁_zero.symm
  · by_cases hy_source₂ : y = source₂
    · subst y
      by_cases h_pos : 0 < M.entry i source₁
      · have h_source₂_zero : represented_mass newRepresentation i source₂ = 0 := by
          rw [represented_mass_eq]
          calc
            discrete_sum (represented_mass_integrand newRepresentation i source₂)
                = discrete_sum (fun _ : representation.W => 0) := by
                    apply InfoTheory.discrete_sum_congr
                    intro w
                    by_cases h_target_decode : representation.decode i w = target
                    · have h_decode : newRepresentation.decode i w = source₁ := by
                        simp [newRepresentation, splitter, h_target_decode, h_pos]
                      have h_source_ne' : source₂ ≠ source₁ := by
                        intro h
                        exact h_source_ne h.symm
                      have h_ne : newRepresentation.decode i w ≠ source₂ := by
                        intro h_eq
                        exact h_source_ne' (h_eq.symm.trans h_decode)
                      rw [represented_mass_integrand_of_ne newRepresentation i source₂ w h_ne]
                    · have h_decode : newRepresentation.decode i w ≠ source₂ := by
                        intro h_decode
                        have h_backward : (transport.backward ⟨representation.decode i w, h_target_decode⟩).1 = source₂ := by
                          simpa [newRepresentation, splitter, h_target_decode, h_pos] using h_decode
                        exact (transport.backward ⟨representation.decode i w, h_target_decode⟩).2.2 h_backward
                      rw [represented_mass_integrand_of_ne newRepresentation i source₂ w h_decode]
            _ = 0 := InfoTheory.discrete_sum_zero
        have h_zero₂ : M.entry i source₂ = 0 := h_disjoint i h_pos
        calc
          M.entry i source₂ = 0 := h_zero₂
          _ = represented_mass newRepresentation i source₂ := h_source₂_zero.symm
      · have h_zero₁ : M.entry i source₁ = 0 :=
          Rat.le_antisymm (Rat.not_lt.mp h_pos) (M.nonnegative i source₁)
        have h_source₂_integrand :
            ∀ w : representation.W,
              represented_mass_integrand newRepresentation i source₂ w =
                represented_mass_integrand representation i target w := by
          intro w
          by_cases h_target_decode : representation.decode i w = target
          · have h_decode : newRepresentation.decode i w = source₂ := by
              simp [newRepresentation, splitter, h_target_decode, h_pos]
            rw [represented_mass_integrand_of_eq newRepresentation i source₂ w h_decode,
              represented_mass_integrand_of_eq representation i target w h_target_decode]
          · have h_decode : newRepresentation.decode i w ≠ source₂ := by
              intro h_decode
              have h_backward : (transport.backward ⟨representation.decode i w, h_target_decode⟩).1 = source₂ := by
                simpa [newRepresentation, splitter, h_target_decode, h_pos] using h_decode
              exact (transport.backward ⟨representation.decode i w, h_target_decode⟩).2.2 h_backward
            rw [represented_mass_integrand_of_ne newRepresentation i source₂ w h_decode,
              represented_mass_integrand_of_ne representation i target w h_target_decode]
        calc
          M.entry i source₂ = M'.entry i target := by
            calc
              M.entry i source₂ = M.entry i source₁ + M.entry i source₂ := by rw [h_zero₁, Rat.zero_add]
              _ = M'.entry i target := by symm; exact h_target i
          _ = represented_mass representation i target := h_representation i target
          _ = discrete_sum (represented_mass_integrand representation i target) := by
                rw [represented_mass_eq]
          _ = discrete_sum (represented_mass_integrand newRepresentation i source₂) := by
                symm
                apply InfoTheory.discrete_sum_congr
                intro w
                exact h_source₂_integrand w
          _ = represented_mass newRepresentation i source₂ := by
                rw [represented_mass_eq]
    · let oldColumn : ColumnsExceptTarget target :=
          transport.forward ⟨y, hy_source₁, hy_source₂⟩
      have h_y : (transport.backward oldColumn).1 = y := by
        simpa [oldColumn] using congrArg Subtype.val (transport.left_inv ⟨y, hy_source₁, hy_source₂⟩)
      have h_old_integrand :
          ∀ w : representation.W,
            represented_mass_integrand newRepresentation i y w =
              represented_mass_integrand representation i oldColumn.1 w := by
        intro w
        by_cases h_target_decode : representation.decode i w = target
        · have h_new_ne : newRepresentation.decode i w ≠ y := by
            intro h_new
            by_cases h_pos : 0 < M.entry i source₁
            · have h_decode : newRepresentation.decode i w = source₁ := by
                simp [newRepresentation, splitter, h_target_decode, h_pos]
              exact hy_source₁ (h_new.symm.trans h_decode)
            · have h_decode : newRepresentation.decode i w = source₂ := by
                simp [newRepresentation, splitter, h_target_decode, h_pos]
              exact hy_source₂ (h_new.symm.trans h_decode)
          have h_old_ne : representation.decode i w ≠ oldColumn.1 := by
            intro h_old
            exact oldColumn.2 (h_old.symm.trans h_target_decode)
          rw [represented_mass_integrand_of_ne newRepresentation i y w h_new_ne,
            represented_mass_integrand_of_ne representation i oldColumn.1 w h_old_ne]
        · by_cases h_hit : (transport.backward ⟨representation.decode i w, h_target_decode⟩).1 = y
          · have h_eq_sub :
                transport.backward ⟨representation.decode i w, h_target_decode⟩ = ⟨y, hy_source₁, hy_source₂⟩ :=
              Subtype.ext h_hit
            have h_eq_old :
                ⟨representation.decode i w, h_target_decode⟩ = oldColumn := by
              calc
                ⟨representation.decode i w, h_target_decode⟩ =
                    transport.forward (transport.backward ⟨representation.decode i w, h_target_decode⟩) := by
                      symm
                      exact transport.right_inv _
                _ = transport.forward ⟨y, hy_source₁, hy_source₂⟩ := by rw [h_eq_sub]
                _ = oldColumn := by rfl
            have h_old : representation.decode i w = oldColumn.1 :=
              congrArg Subtype.val h_eq_old
            have h_decode : newRepresentation.decode i w = y := by
              simpa [newRepresentation, h_target_decode] using h_hit
            rw [represented_mass_integrand_of_eq newRepresentation i y w h_decode,
              represented_mass_integrand_of_eq representation i oldColumn.1 w h_old]
          · have h_old_ne : representation.decode i w ≠ oldColumn.1 := by
              intro h_old
              apply h_hit
              calc
                (transport.backward ⟨representation.decode i w, h_target_decode⟩).1
                    = (transport.backward oldColumn).1 := by
                        have h_eq_old : ⟨representation.decode i w, h_target_decode⟩ = oldColumn :=
                          Subtype.ext h_old
                        rw [h_eq_old]
                _ = y := h_y
            have h_new_ne : newRepresentation.decode i w ≠ y := by
              intro h_new
              apply h_hit
              simpa [newRepresentation, h_target_decode] using h_new
            rw [represented_mass_integrand_of_ne newRepresentation i y w h_new_ne,
              represented_mass_integrand_of_ne representation i oldColumn.1 w h_old_ne]
      calc
        M.entry i y = M'.entry i oldColumn.1 := by
          symm
          exact h_rest ⟨y, hy_source₁, hy_source₂⟩ i
        _ = represented_mass representation i oldColumn.1 := h_representation i oldColumn.1
        _ = discrete_sum (represented_mass_integrand representation i oldColumn.1) := by
              rw [represented_mass_eq]
        _ = discrete_sum (represented_mass_integrand newRepresentation i y) := by
              symm
              apply InfoTheory.discrete_sum_congr
              intro w
              exact h_old_integrand w
        _ = represented_mass newRepresentation i y := by
              rw [represented_mass_eq]

theorem vpm_operation_preserves_nonrepresentability {k m n : Nat}
    (M : ConditionalProbabilityMatrix k m)
    (M' : ConditionalProbabilityMatrix k n)
    (h_op : is_vpm_operation M M')
    (h_not_repr : Not (matrix_perfectly_representable M)) :
    Not (matrix_perfectly_representable M') := by
  intro h_repr
  exact h_not_repr (vpm_operation_reflects_perfect_representability M M' h_op h_repr)

theorem ppm_operation_reflects_perfect_representability {k m n : Nat}
    (M : ConditionalProbabilityMatrix k m)
    (M' : ConditionalProbabilityMatrix k n)
    (h_op : is_ppm_operation M M')
    (h_repr : matrix_perfectly_representable M') :
    matrix_perfectly_representable M := by
  classical
  rcases h_op with ⟨h_singular, _, _, source₁, source₂, h_source_ne, h_pattern, target, _, transport,
    h_target, h_rest⟩
  rcases h_repr with ⟨representation, h_representation⟩
  have h_pattern_pos : ∀ i : Fin k, 0 < M.entry i source₁ ↔ 0 < M.entry i source₂ := by
    intro i
    constructor
    · intro h_pos₁
      have h_bool : column_pattern M source₂ i = true := by
        simpa [column_pattern, h_pos₁] using (congrArg (fun f => f i) h_pattern).symm
      by_cases h_pos₂ : 0 < M.entry i source₂
      · exact h_pos₂
      · simp [column_pattern, h_pos₂] at h_bool
    · intro h_pos₂
      have h_bool : column_pattern M source₁ i = true := by
        simpa [column_pattern, h_pos₂] using congrArg (fun f => f i) h_pattern
      by_cases h_pos₁ : 0 < M.entry i source₁
      · exact h_pos₁
      · simp [column_pattern, h_pos₁] at h_bool
  let α : Probability :=
    if h_exists : ∃ i : Fin k, 0 < M.entry i source₁ then
      column_value M source₁ / (column_value M source₁ + column_value M source₂)
    else
      0
  have h_scale₁ : ∀ i : Fin k, M.entry i source₁ = α * M'.entry i target := by
    intro i
    by_cases h_pos₁ : 0 < M.entry i source₁
    · have h_exists : ∃ i : Fin k, 0 < M.entry i source₁ := ⟨i, h_pos₁⟩
      have h_pos₂ : 0 < M.entry i source₂ := (h_pattern_pos i).1 h_pos₁
      have h_eq₁ : M.entry i source₁ = column_value M source₁ := by
        rw [entry_eq_column_value_or_zero M h_singular i source₁,
          show column_pattern M source₁ i = true by simp [column_pattern, h_pos₁]]
        simp
      have h_eq₂ : M.entry i source₂ = column_value M source₂ := by
        rw [entry_eq_column_value_or_zero M h_singular i source₂,
          show column_pattern M source₂ i = true by simp [column_pattern, h_pos₂]]
        simp
      have h_value_pos₁ : 0 < column_value M source₁ := by
        rw [← h_eq₁]
        exact h_pos₁
      have h_exists₂ : ∃ i : Fin k, 0 < M.entry i source₂ := ⟨i, h_pos₂⟩
      have h_value_pos₂ : 0 < column_value M source₂ := by
        rw [← h_eq₂]
        exact h_pos₂
      have h_value_lt_sum : column_value M source₁ < column_value M source₁ + column_value M source₂ := by
        simpa [Rat.add_zero] using
          (Rat.add_lt_add_left (c := column_value M source₁)).2 h_value_pos₂
      have h_sum_ne : column_value M source₁ + column_value M source₂ ≠ 0 := by
        intro h_sum_zero
        have h_lt_zero : column_value M source₁ < 0 := by
          simpa [h_sum_zero] using h_value_lt_sum
        exact (Rat.not_lt.mpr (Rat.le_of_lt h_value_pos₁)) h_lt_zero
      have h_target_eq : M'.entry i target = column_value M source₁ + column_value M source₂ := by
        rw [h_target i, h_eq₁, h_eq₂]
      calc
        M.entry i source₁ = column_value M source₁ := h_eq₁
        _ = (column_value M source₁ / (column_value M source₁ + column_value M source₂)) * M'.entry i target := by
              rw [h_target_eq]
              exact (Rat.div_mul_cancel (a := column_value M source₁)
                (b := column_value M source₁ + column_value M source₂) h_sum_ne).symm
        _ = α * M'.entry i target := by
              simp [α, h_exists]
    · have h_not_pos₂ : ¬ 0 < M.entry i source₂ := by
        intro h_pos₂
        exact h_pos₁ ((h_pattern_pos i).2 h_pos₂)
      have h_zero₁ : M.entry i source₁ = 0 :=
        Rat.le_antisymm (Rat.not_lt.mp h_pos₁) (M.nonnegative i source₁)
      have h_zero₂ : M.entry i source₂ = 0 :=
        Rat.le_antisymm (Rat.not_lt.mp h_not_pos₂) (M.nonnegative i source₂)
      have h_target_zero : M'.entry i target = 0 := by
        simpa [h_zero₁, h_zero₂, Rat.zero_add] using h_target i
      calc
        M.entry i source₁ = 0 := h_zero₁
        _ = α * M'.entry i target := by rw [h_target_zero, Rat.mul_zero]
  have h_scale₂ : ∀ i : Fin k, M.entry i source₂ = (1 - α) * M'.entry i target := by
    intro i
    have h_target_sub : M.entry i source₂ = M'.entry i target - M.entry i source₁ := by
      have h_eq : M'.entry i target - M.entry i source₁ = M.entry i source₂ := by
        rw [h_target i, Rat.sub_eq_add_neg, Rat.add_assoc,
          Rat.add_comm (M.entry i source₂) (-M.entry i source₁),
          ← Rat.add_assoc, Rat.add_neg_cancel, Rat.zero_add]
      exact h_eq.symm
    calc
      M.entry i source₂ = M'.entry i target - M.entry i source₁ := h_target_sub
      _ = M'.entry i target - α * M'.entry i target := by rw [h_scale₁ i]
      _ = M'.entry i target + -(α * M'.entry i target) := by
        rw [Rat.sub_eq_add_neg]
      _ = M'.entry i target + (-α) * M'.entry i target := by
        rw [← Rat.neg_mul]
      _ = 1 * M'.entry i target + (-α) * M'.entry i target := by
        exact congrArg (fun t => t + (-α) * M'.entry i target)
          (Rat.one_mul (M'.entry i target)).symm
      _ = (1 + -α) * M'.entry i target := by
            exact (Rat.add_mul 1 (-α) (M'.entry i target)).symm
      _ = (1 - α) * M'.entry i target := by
        rw [Rat.sub_eq_add_neg]
  let newRepresentation : CanonicalFunctionalRepresentation (Fin k) (Fin m) :=
    { W := Sum representation.W representation.W
      pW := fun
        | .inl w => α * representation.pW w
        | .inr w => (1 - α) * representation.pW w
      decode := fun i sw =>
        match sw with
        | .inl w =>
            if h_target_decode : representation.decode i w = target then
              source₁
            else
              (transport.backward ⟨representation.decode i w, h_target_decode⟩).1
        | .inr w =>
            if h_target_decode : representation.decode i w = target then
              source₂
            else
              (transport.backward ⟨representation.decode i w, h_target_decode⟩).1 }
  refine ⟨newRepresentation, ?_⟩
  intro i y
  by_cases hy_source₁ : y = source₁
  · subst y
    have h_inl_integrand :
        ∀ w : representation.W,
          represented_mass_integrand newRepresentation i source₁ (.inl w) =
            α * represented_mass_integrand representation i target w := by
      intro w
      by_cases h_target_decode : representation.decode i w = target
      · have h_decode : newRepresentation.decode i (.inl w) = source₁ := by
          simp [newRepresentation, h_target_decode]
        rw [represented_mass_integrand_of_eq newRepresentation i source₁ (.inl w) h_decode,
          represented_mass_integrand_of_eq representation i target w h_target_decode]
      · have h_decode : newRepresentation.decode i (.inl w) ≠ source₁ := by
          intro h_decode
          have h_backward : (transport.backward ⟨representation.decode i w, h_target_decode⟩).1 = source₁ := by
            simpa [newRepresentation, h_target_decode] using h_decode
          exact (transport.backward ⟨representation.decode i w, h_target_decode⟩).2.1 h_backward
        rw [represented_mass_integrand_of_ne newRepresentation i source₁ (.inl w) h_decode,
          represented_mass_integrand_of_ne representation i target w h_target_decode]
        rw [Rat.mul_zero]
    have h_inr_zero_sum :
        discrete_sum (fun w : representation.W =>
          represented_mass_integrand newRepresentation i source₁ (.inr w)) = 0 := by
      calc
        discrete_sum (fun w : representation.W =>
            represented_mass_integrand newRepresentation i source₁ (.inr w))
            = discrete_sum (fun _ : representation.W => 0) := by
                apply InfoTheory.discrete_sum_congr
                intro w
                by_cases h_target_decode : representation.decode i w = target
                · have h_decode : newRepresentation.decode i (.inr w) = source₂ := by
                    simp [newRepresentation, h_target_decode]
                  have h_ne : newRepresentation.decode i (.inr w) ≠ source₁ := by
                    intro h_eq
                    exact h_source_ne (h_eq.symm.trans h_decode)
                  rw [represented_mass_integrand_of_ne newRepresentation i source₁ (.inr w) h_ne]
                · have h_decode : newRepresentation.decode i (.inr w) ≠ source₁ := by
                    intro h_decode
                    have h_backward : (transport.backward ⟨representation.decode i w, h_target_decode⟩).1 = source₁ := by
                      simpa [newRepresentation, h_target_decode] using h_decode
                    exact (transport.backward ⟨representation.decode i w, h_target_decode⟩).2.1 h_backward
                  rw [represented_mass_integrand_of_ne newRepresentation i source₁ (.inr w) h_decode]
        _ = 0 := InfoTheory.discrete_sum_zero
    calc
      M.entry i source₁ = α * M'.entry i target := h_scale₁ i
      _ = α * represented_mass representation i target := by rw [h_representation i target]
      _ = α * discrete_sum (represented_mass_integrand representation i target) := by
            rw [represented_mass_eq]
      _ = discrete_sum (fun w : representation.W =>
            α * represented_mass_integrand representation i target w) := by
            symm
            exact InfoTheory.discrete_sum_mul_left α _
      _ = discrete_sum (fun w : representation.W =>
            represented_mass_integrand newRepresentation i source₁ (.inl w)) := by
            symm
            apply InfoTheory.discrete_sum_congr
            intro w
            exact h_inl_integrand w
      _ = discrete_sum (fun w : representation.W =>
            represented_mass_integrand newRepresentation i source₁ (.inl w)) +
            discrete_sum (fun w : representation.W =>
              represented_mass_integrand newRepresentation i source₁ (.inr w)) := by
            rw [h_inr_zero_sum, Rat.add_zero]
      _ = discrete_sum (represented_mass_integrand newRepresentation i source₁) := by
            symm
            exact InfoTheory.discrete_sum_sum (represented_mass_integrand newRepresentation i source₁)
      _ = represented_mass newRepresentation i source₁ := by
            rw [represented_mass_eq]
  · by_cases hy_source₂ : y = source₂
    · subst y
      have h_source_ne' : source₂ ≠ source₁ := by
        intro h
        exact h_source_ne h.symm
      have h_inr_integrand :
          ∀ w : representation.W,
            represented_mass_integrand newRepresentation i source₂ (.inr w) =
              (1 - α) * represented_mass_integrand representation i target w := by
        intro w
        by_cases h_target_decode : representation.decode i w = target
        · have h_decode : newRepresentation.decode i (.inr w) = source₂ := by
            simp [newRepresentation, h_target_decode]
          rw [represented_mass_integrand_of_eq newRepresentation i source₂ (.inr w) h_decode,
            represented_mass_integrand_of_eq representation i target w h_target_decode]
        · have h_decode : newRepresentation.decode i (.inr w) ≠ source₂ := by
            intro h_decode
            have h_backward : (transport.backward ⟨representation.decode i w, h_target_decode⟩).1 = source₂ := by
              simpa [newRepresentation, h_target_decode] using h_decode
            exact (transport.backward ⟨representation.decode i w, h_target_decode⟩).2.2 h_backward
          rw [represented_mass_integrand_of_ne newRepresentation i source₂ (.inr w) h_decode,
            represented_mass_integrand_of_ne representation i target w h_target_decode]
          rw [Rat.mul_zero]
      have h_inl_zero_sum :
          discrete_sum (fun w : representation.W =>
            represented_mass_integrand newRepresentation i source₂ (.inl w)) = 0 := by
        calc
          discrete_sum (fun w : representation.W =>
              represented_mass_integrand newRepresentation i source₂ (.inl w))
              = discrete_sum (fun _ : representation.W => 0) := by
                  apply InfoTheory.discrete_sum_congr
                  intro w
                  by_cases h_target_decode : representation.decode i w = target
                  · have h_decode : newRepresentation.decode i (.inl w) = source₁ := by
                      simp [newRepresentation, h_target_decode]
                    have h_ne : newRepresentation.decode i (.inl w) ≠ source₂ := by
                      intro h_eq
                      exact h_source_ne' (h_eq.symm.trans h_decode)
                    rw [represented_mass_integrand_of_ne newRepresentation i source₂ (.inl w) h_ne]
                  · have h_decode : newRepresentation.decode i (.inl w) ≠ source₂ := by
                      intro h_decode
                      have h_backward : (transport.backward ⟨representation.decode i w, h_target_decode⟩).1 = source₂ := by
                        simpa [newRepresentation, h_target_decode] using h_decode
                      exact (transport.backward ⟨representation.decode i w, h_target_decode⟩).2.2 h_backward
                    rw [represented_mass_integrand_of_ne newRepresentation i source₂ (.inl w) h_decode]
          _ = 0 := InfoTheory.discrete_sum_zero
      calc
        M.entry i source₂ = (1 - α) * M'.entry i target := h_scale₂ i
        _ = (1 - α) * represented_mass representation i target := by rw [h_representation i target]
        _ = (1 - α) * discrete_sum (represented_mass_integrand representation i target) := by
              rw [represented_mass_eq]
        _ = discrete_sum (fun w : representation.W =>
              (1 - α) * represented_mass_integrand representation i target w) := by
              symm
              exact InfoTheory.discrete_sum_mul_left (1 - α) _
        _ = discrete_sum (fun w : representation.W =>
              represented_mass_integrand newRepresentation i source₂ (.inr w)) := by
              symm
              apply InfoTheory.discrete_sum_congr
              intro w
              exact h_inr_integrand w
        _ = discrete_sum (fun w : representation.W =>
              represented_mass_integrand newRepresentation i source₂ (.inl w)) +
              discrete_sum (fun w : representation.W =>
                represented_mass_integrand newRepresentation i source₂ (.inr w)) := by
              rw [h_inl_zero_sum, Rat.zero_add]
        _ = discrete_sum (represented_mass_integrand newRepresentation i source₂) := by
              symm
              exact InfoTheory.discrete_sum_sum (represented_mass_integrand newRepresentation i source₂)
        _ = represented_mass newRepresentation i source₂ := by
              rw [represented_mass_eq]
    · let oldColumn : ColumnsExceptTarget target :=
          transport.forward ⟨y, hy_source₁, hy_source₂⟩
      have h_y : (transport.backward oldColumn).1 = y := by
        simpa [oldColumn] using congrArg Subtype.val (transport.left_inv ⟨y, hy_source₁, hy_source₂⟩)
      have h_inl_old_integrand :
          ∀ w : representation.W,
            represented_mass_integrand newRepresentation i y (.inl w) =
              α * represented_mass_integrand representation i oldColumn.1 w := by
        intro w
        by_cases h_target_decode : representation.decode i w = target
        · have h_new_ne : newRepresentation.decode i (.inl w) ≠ y := by
            intro h_new
            have h_decode : newRepresentation.decode i (.inl w) = source₁ := by
              simp [newRepresentation, h_target_decode]
            exact hy_source₁ (h_new.symm.trans h_decode)
          have h_old_ne : representation.decode i w ≠ oldColumn.1 := by
            intro h_old
            exact oldColumn.2 (h_old.symm.trans h_target_decode)
          rw [represented_mass_integrand_of_ne newRepresentation i y (.inl w) h_new_ne,
            represented_mass_integrand_of_ne representation i oldColumn.1 w h_old_ne]
          rw [Rat.mul_zero]
        · by_cases h_hit : (transport.backward ⟨representation.decode i w, h_target_decode⟩).1 = y
          · have h_eq_sub :
                transport.backward ⟨representation.decode i w, h_target_decode⟩ = ⟨y, hy_source₁, hy_source₂⟩ :=
              Subtype.ext h_hit
            have h_eq_old :
                ⟨representation.decode i w, h_target_decode⟩ = oldColumn := by
              calc
                ⟨representation.decode i w, h_target_decode⟩ =
                    transport.forward (transport.backward ⟨representation.decode i w, h_target_decode⟩) := by
                      symm
                      exact transport.right_inv _
                _ = transport.forward ⟨y, hy_source₁, hy_source₂⟩ := by rw [h_eq_sub]
                _ = oldColumn := by rfl
            have h_old : representation.decode i w = oldColumn.1 :=
              congrArg Subtype.val h_eq_old
            have h_decode : newRepresentation.decode i (.inl w) = y := by
              simpa [newRepresentation, h_target_decode] using h_hit
            rw [represented_mass_integrand_of_eq newRepresentation i y (.inl w) h_decode,
              represented_mass_integrand_of_eq representation i oldColumn.1 w h_old]
          · have h_old_ne : representation.decode i w ≠ oldColumn.1 := by
              intro h_old
              apply h_hit
              calc
                (transport.backward ⟨representation.decode i w, h_target_decode⟩).1
                    = (transport.backward oldColumn).1 := by
                        have h_eq_old : ⟨representation.decode i w, h_target_decode⟩ = oldColumn :=
                          Subtype.ext h_old
                        rw [h_eq_old]
                _ = y := h_y
            have h_new_ne : newRepresentation.decode i (.inl w) ≠ y := by
              intro h_new
              apply h_hit
              simpa [newRepresentation, h_target_decode] using h_new
            rw [represented_mass_integrand_of_ne newRepresentation i y (.inl w) h_new_ne,
              represented_mass_integrand_of_ne representation i oldColumn.1 w h_old_ne]
            rw [Rat.mul_zero]
      have h_inr_old_integrand :
          ∀ w : representation.W,
            represented_mass_integrand newRepresentation i y (.inr w) =
              (1 - α) * represented_mass_integrand representation i oldColumn.1 w := by
        intro w
        by_cases h_target_decode : representation.decode i w = target
        · have h_new_ne : newRepresentation.decode i (.inr w) ≠ y := by
            intro h_new
            have h_decode : newRepresentation.decode i (.inr w) = source₂ := by
              simp [newRepresentation, h_target_decode]
            exact hy_source₂ (h_new.symm.trans h_decode)
          have h_old_ne : representation.decode i w ≠ oldColumn.1 := by
            intro h_old
            exact oldColumn.2 (h_old.symm.trans h_target_decode)
          rw [represented_mass_integrand_of_ne newRepresentation i y (.inr w) h_new_ne,
            represented_mass_integrand_of_ne representation i oldColumn.1 w h_old_ne]
          rw [Rat.mul_zero]
        · by_cases h_hit : (transport.backward ⟨representation.decode i w, h_target_decode⟩).1 = y
          · have h_eq_sub :
                transport.backward ⟨representation.decode i w, h_target_decode⟩ = ⟨y, hy_source₁, hy_source₂⟩ :=
              Subtype.ext h_hit
            have h_eq_old :
                ⟨representation.decode i w, h_target_decode⟩ = oldColumn := by
              calc
                ⟨representation.decode i w, h_target_decode⟩ =
                    transport.forward (transport.backward ⟨representation.decode i w, h_target_decode⟩) := by
                      symm
                      exact transport.right_inv _
                _ = transport.forward ⟨y, hy_source₁, hy_source₂⟩ := by rw [h_eq_sub]
                _ = oldColumn := by rfl
            have h_old : representation.decode i w = oldColumn.1 :=
              congrArg Subtype.val h_eq_old
            have h_decode : newRepresentation.decode i (.inr w) = y := by
              simpa [newRepresentation, h_target_decode] using h_hit
            rw [represented_mass_integrand_of_eq newRepresentation i y (.inr w) h_decode,
              represented_mass_integrand_of_eq representation i oldColumn.1 w h_old]
          · have h_old_ne : representation.decode i w ≠ oldColumn.1 := by
              intro h_old
              apply h_hit
              calc
                (transport.backward ⟨representation.decode i w, h_target_decode⟩).1
                    = (transport.backward oldColumn).1 := by
                        have h_eq_old : ⟨representation.decode i w, h_target_decode⟩ = oldColumn :=
                          Subtype.ext h_old
                        rw [h_eq_old]
                _ = y := h_y
            have h_new_ne : newRepresentation.decode i (.inr w) ≠ y := by
              intro h_new
              apply h_hit
              simpa [newRepresentation, h_target_decode] using h_new
            rw [represented_mass_integrand_of_ne newRepresentation i y (.inr w) h_new_ne,
              represented_mass_integrand_of_ne representation i oldColumn.1 w h_old_ne]
            rw [Rat.mul_zero]
      have h_inl_sum :
          discrete_sum (fun w : representation.W =>
            represented_mass_integrand newRepresentation i y (.inl w)) =
              discrete_sum (fun w : representation.W =>
                α * represented_mass_integrand representation i oldColumn.1 w) := by
        apply InfoTheory.discrete_sum_congr
        intro w
        exact h_inl_old_integrand w
      have h_inr_sum :
          discrete_sum (fun w : representation.W =>
            represented_mass_integrand newRepresentation i y (.inr w)) =
              discrete_sum (fun w : representation.W =>
                (1 - α) * represented_mass_integrand representation i oldColumn.1 w) := by
        apply InfoTheory.discrete_sum_congr
        intro w
        exact h_inr_old_integrand w
      calc
        M.entry i y = M'.entry i oldColumn.1 := by
          symm
          exact h_rest ⟨y, hy_source₁, hy_source₂⟩ i
        _ = represented_mass representation i oldColumn.1 := h_representation i oldColumn.1
        _ = discrete_sum (represented_mass_integrand representation i oldColumn.1) := by
              rw [represented_mass_eq]
        _ = discrete_sum (fun w : representation.W =>
              α * represented_mass_integrand representation i oldColumn.1 w) +
              discrete_sum (fun w : representation.W =>
                (1 - α) * represented_mass_integrand representation i oldColumn.1 w) := by
              symm
              exact InfoTheory.discrete_sum_split_weight α _
        _ = discrete_sum (fun w : representation.W =>
              represented_mass_integrand newRepresentation i y (.inl w)) +
              discrete_sum (fun w : representation.W =>
                represented_mass_integrand newRepresentation i y (.inr w)) := by
              rw [← h_inl_sum, ← h_inr_sum]
        _ = discrete_sum (represented_mass_integrand newRepresentation i y) := by
              symm
              exact InfoTheory.discrete_sum_sum (represented_mass_integrand newRepresentation i y)
        _ = represented_mass newRepresentation i y := by
              rw [represented_mass_eq]

-- LEMMA 6: PPM, PPS, and VPM preserve non-perfect-representability
theorem nonrepresentability_preserved_by_ppm {k m n : Nat}
    (M : ConditionalProbabilityMatrix k m)
    (M' : ConditionalProbabilityMatrix k n)
  (h_op : is_ppm_operation M M')
    (h_not_repr : Not (matrix_perfectly_representable M)) :
    Not (matrix_perfectly_representable M') := by
  intro h_repr
  exact h_not_repr (ppm_operation_reflects_perfect_representability M M' h_op h_repr)

theorem nonrepresentability_preserved_by_ppm_pps_vpm {k m n : Nat}
  (M : ConditionalProbabilityMatrix k m)
  (M' : ConditionalProbabilityMatrix k n)
  (h_op : Or (is_ppm_operation M M') (Or (is_pps_operation M M') (is_vpm_operation M M')))
  (h_not_repr : Not (matrix_perfectly_representable M)) :
  Not (matrix_perfectly_representable M') := by
  rcases h_op with h_ppm | h_pps_vpm
  · exact nonrepresentability_preserved_by_ppm M M' h_ppm h_not_repr
  · rcases h_pps_vpm with h_pps | h_vpm
    · exact pps_operation_preserves_nonrepresentability M M' h_pps h_not_repr
    · exact vpm_operation_preserves_nonrepresentability M M' h_vpm h_not_repr

theorem lemma_6_preservation_of_nonrepresentability {k m n : Nat}
    (M : ConditionalProbabilityMatrix k m)
    (M' : ConditionalProbabilityMatrix k n)
    (h_op : Or (is_ppm_operation M M') (Or (is_pps_operation M M') (is_vpm_operation M M')))
    (h_not_repr : Not (matrix_perfectly_representable M)) :
    Not (matrix_perfectly_representable M') := by
  exact nonrepresentability_preserved_by_ppm_pps_vpm M M' h_op h_not_repr

def reducible_to_one_vector {k m : Nat}
    (M : ConditionalProbabilityMatrix k m) : Prop :=
  MatrixReachable (pps_ppm_vpm_step (k := k)) ⟨m, M⟩ ⟨1, one_vector_matrix k⟩

theorem one_vector_matrix_perfectly_representable (k : Nat) :
    matrix_perfectly_representable (one_vector_matrix k) := by
  let representation : CanonicalFunctionalRepresentation (Fin k) (Fin 1) :=
    { W := PUnit
      pW := fun _ => 1
      decode := fun _ _ => 0 }
  refine Exists.intro representation ?_
  intro i y
  cases y with
  | mk val isLt =>
      have hval : val = 0 := by omega
      cases hval
      rw [represented_mass_eq, discrete_sum_punit]
      simp [representation, represented_mass_integrand, one_vector_matrix]

theorem reachable_by_pps_ppm_vpm_preserves_nonrepresentability {k : Nat}
    {start finish : MatrixState k}
    (h_reachable : MatrixReachable (pps_ppm_vpm_step (k := k)) start finish)
    (h_not_repr : Not (matrix_perfectly_representable start.2)) :
    Not (matrix_perfectly_representable finish.2) := by
    induction h_reachable with
    | refl state =>
      simpa using h_not_repr
    | @tail start next finish h_step h_tail ih =>
      cases start with
      | mk m M =>
          cases next with
          | mk n M' =>
              have h_next_not_repr : Not (matrix_perfectly_representable M') := by
                dsimp [pps_ppm_vpm_step, pps_step, ppm_step, vpm_step] at h_step
                dsimp at h_not_repr
                rcases h_step with h_pps | h_ppm_vpm
                · exact pps_operation_preserves_nonrepresentability M M' h_pps h_not_repr
                · rcases h_ppm_vpm with h_ppm | h_vpm
                  · exact nonrepresentability_preserved_by_ppm M M' h_ppm h_not_repr
                  · exact vpm_operation_preserves_nonrepresentability M M' h_vpm h_not_repr
              exact ih h_next_not_repr

theorem reducible_to_one_vector_implies_perfectly_representable {k m : Nat}
    (M : ConditionalProbabilityMatrix k m)
    (h_reducible : reducible_to_one_vector M) :
    matrix_perfectly_representable M := by
  classical
  by_cases h_repr : matrix_perfectly_representable M
  · exact h_repr
  · have h_not_repr_one : Not (matrix_perfectly_representable (one_vector_matrix k)) :=
        reachable_by_pps_ppm_vpm_preserves_nonrepresentability h_reducible h_repr
    exact False.elim (h_not_repr_one (one_vector_matrix_perfectly_representable k))

structure FinitePositiveMatrixRepresentation {k m : Nat}
    (M : ConditionalProbabilityMatrix k m) where
  width : Nat
  pW : Fin width → Probability
  decode : Fin k → Fin width → Fin m
  positive : ∀ w : Fin width, 0 < pW w
  normalized : discrete_sum pW = 1
  pW_given_Y : Fin m → Fin width → Probability
  conditional_normalized : ∀ y : Fin m, discrete_sum (pW_given_Y y) = 1
  conditional_factorization : ∀ i y w,
    (if decode i w = y then pW w else 0) = pW_given_Y y w * M.entry i y

def FinitePositiveMatrixRepresentation.toCanonical {k m : Nat}
    {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M) :
    CanonicalFunctionalRepresentation (Fin k) (Fin m) :=
  { W := Fin representation.width
    pW := representation.pW
    decode := representation.decode }

theorem FinitePositiveMatrixRepresentation.represents {k m : Nat}
    {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (i : Fin k) (y : Fin m) :
    M.entry i y = discrete_sum (fun w : Fin representation.width =>
  if representation.decode i w = y then representation.pW w else 0) := by
  calc
    M.entry i y = M.entry i y * 1 := by rw [Rat.mul_one]
    _ = M.entry i y * discrete_sum (representation.pW_given_Y y) := by
      rw [representation.conditional_normalized y]
    _ = discrete_sum (fun w : Fin representation.width =>
      M.entry i y * representation.pW_given_Y y w) := by
      symm
      exact InfoTheory.discrete_sum_mul_left (M.entry i y) _
    _ = discrete_sum (fun w : Fin representation.width =>
      representation.pW_given_Y y w * M.entry i y) := by
      apply InfoTheory.discrete_sum_congr
      intro w
      rw [Rat.mul_comm]
    _ = discrete_sum (fun w : Fin representation.width =>
      if representation.decode i w = y then representation.pW w else 0) := by
      apply InfoTheory.discrete_sum_congr
      intro w
      symm
      exact representation.conditional_factorization i y w

theorem FinitePositiveMatrixRepresentation.perfectly_representable {k m : Nat}
    {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M) :
    matrix_perfectly_representable M := by
  refine Exists.intro representation.toCanonical ?_
  intro i y
  have h_integrand :
      represented_mass_integrand representation.toCanonical i y =
        (fun w : Fin representation.width =>
          if representation.decode i w = y then representation.pW w else 0) := by
    funext w
    simp [FinitePositiveMatrixRepresentation.toCanonical, represented_mass_integrand]
  rw [represented_mass_eq]
  rw [h_integrand]
  exact representation.represents i y

def FinitePositiveMatrixRepresentation.liftedChannel {k m : Nat}
    {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M) :
    Channel (Fin k) (Fin m × Fin representation.width) :=
  fun i yw => if representation.decode i yw.2 = yw.1 then representation.pW yw.2 else 0

theorem FinitePositiveMatrixRepresentation.liftedChannel_eq {k m : Nat}
    {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (i : Fin k) (y : Fin m) (w : Fin representation.width) :
    representation.liftedChannel i (y, w) =
      if representation.decode i w = y then representation.pW w else 0 := by
  rfl

theorem FinitePositiveMatrixRepresentation.liftedChannel_marginalizes {k m : Nat}
    {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (i : Fin k) (y : Fin m) :
    M.entry i y = discrete_sum (fun w : Fin representation.width =>
      representation.liftedChannel i (y, w)) := by
  simpa [FinitePositiveMatrixRepresentation.liftedChannel] using representation.represents i y

theorem FinitePositiveMatrixRepresentation.liftedChannel_positive_iff_decode {k m : Nat}
    {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (i : Fin k) (y : Fin m) (w : Fin representation.width) :
    0 < representation.liftedChannel i (y, w) ↔ representation.decode i w = y := by
  by_cases h_decode : representation.decode i w = y
  · simp [FinitePositiveMatrixRepresentation.liftedChannel, h_decode, representation.positive w]
  · simp [FinitePositiveMatrixRepresentation.liftedChannel, h_decode]

theorem FinitePositiveMatrixRepresentation.liftedChannel_eq_conditional_weight {k m : Nat}
    {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (i : Fin k) (y : Fin m) (w : Fin representation.width) :
    representation.liftedChannel i (y, w) =
      representation.pW_given_Y y w * M.entry i y := by
  simpa [FinitePositiveMatrixRepresentation.liftedChannel] using
    representation.conditional_factorization i y w

theorem FinitePositiveMatrixRepresentation.decode_eq_implies_positive_entry
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (i : Fin k) (y : Fin m) (w : Fin representation.width)
    (h_decode : representation.decode i w = y) :
    0 < M.entry i y := by
  by_cases h_pos : 0 < M.entry i y
  · exact h_pos
  · have h_entry_zero : M.entry i y = 0 := by
      exact Rat.le_antisymm (Rat.not_lt.mp h_pos) (M.nonnegative i y)
    have h_pw_zero : representation.pW w = 0 := by
      calc
        representation.pW w = representation.pW_given_Y y w * M.entry i y := by
          simpa [h_decode] using representation.conditional_factorization i y w
        _ = 0 := by rw [h_entry_zero, Rat.mul_zero]
    have h_pw_pos : 0 < representation.pW w := representation.positive w
    rw [h_pw_zero] at h_pw_pos
    simp at h_pw_pos

theorem FinitePositiveMatrixRepresentation.positive_entry_has_decode
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (i : Fin k) (y : Fin m)
    (h_pos : 0 < M.entry i y) :
    ∃ w : Fin representation.width, representation.decode i w = y := by
  classical
  by_cases h_exists : ∃ w : Fin representation.width, representation.decode i w = y
  · exact h_exists
  · have h_zero_integrand :
        (fun w : Fin representation.width => if representation.decode i w = y then representation.pW w else 0) =
          fun _ : Fin representation.width => 0 := by
      funext w
      by_cases h_decode : representation.decode i w = y
      · exact False.elim (h_exists ⟨w, h_decode⟩)
      · simp [h_decode]
    have h_zero : M.entry i y = 0 := by
      calc
        M.entry i y = discrete_sum (fun w : Fin representation.width =>
            if representation.decode i w = y then representation.pW w else 0) := by
              exact representation.represents i y
        _ = discrete_sum (fun _ : Fin representation.width => 0) := by rw [h_zero_integrand]
        _ = 0 := InfoTheory.discrete_sum_zero
    rw [h_zero] at h_pos
    simp at h_pos

theorem FinitePositiveMatrixRepresentation.decode_eq_iff_positive_entry_of_conditional_positive
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (i : Fin k) (y : Fin m) (w : Fin representation.width)
    (h_cond : 0 < representation.pW_given_Y y w) :
    representation.decode i w = y ↔ 0 < M.entry i y := by
  constructor
  · intro h_decode
    exact representation.decode_eq_implies_positive_entry i y w h_decode
  · intro h_pos
    by_cases h_decode : representation.decode i w = y
    · exact h_decode
    · have h_product_zero : representation.pW_given_Y y w * M.entry i y = 0 := by
        simpa [h_decode] using (representation.conditional_factorization i y w).symm
      have h_product_pos : 0 < representation.pW_given_Y y w * M.entry i y := by
        exact Rat.mul_pos h_cond h_pos
      rw [h_product_zero] at h_product_pos
      simp at h_product_pos

theorem FinitePositiveMatrixRepresentation.liftedChannel_positive_iff_matrix_positive
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (i : Fin k) (y : Fin m) (w : Fin representation.width)
    (h_cond : 0 < representation.pW_given_Y y w) :
    0 < representation.liftedChannel i (y, w) ↔ 0 < M.entry i y := by
  rw [representation.liftedChannel_positive_iff_decode]
  exact representation.decode_eq_iff_positive_entry_of_conditional_positive i y w h_cond

theorem FinitePositiveMatrixRepresentation.column_pattern_eq_of_conditional_positive
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (y : Fin m) (w : Fin representation.width)
    (h_cond : 0 < representation.pW_given_Y y w) :
    column_pattern M y = fun i => if representation.decode i w = y then true else false := by
  funext i
  by_cases h_decode : representation.decode i w = y
  · have h_pos : 0 < M.entry i y :=
        (representation.decode_eq_iff_positive_entry_of_conditional_positive i y w h_cond).mp h_decode
    simp [column_pattern, h_decode, h_pos]
  · have h_not_pos : ¬ 0 < M.entry i y := by
      intro h_pos
      exact h_decode
        ((representation.decode_eq_iff_positive_entry_of_conditional_positive i y w h_cond).mpr h_pos)
    simp [column_pattern, h_decode, h_not_pos]

def FinitePositiveMatrixRepresentation.allLiftedOutputs {k m : Nat}
    {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M) :
    List (Fin m × Fin representation.width) :=
  List.foldr
    (fun y acc =>
      List.foldr (fun w acc' => (y, w) :: acc') acc (List.finRange representation.width))
    []
    (List.finRange m)

def FinitePositiveMatrixRepresentation.liftedOutputUsed {k m : Nat}
    {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (yw : Fin m × Fin representation.width) : Prop :=
  ∃ i : Fin k, representation.decode i yw.2 = yw.1

theorem FinitePositiveMatrixRepresentation.mem_allLiftedOutputs {k m : Nat}
    {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (y : Fin m) (w : Fin representation.width) :
    (y, w) ∈ representation.allLiftedOutputs := by
  simp [FinitePositiveMatrixRepresentation.allLiftedOutputs]
  refine ⟨List.map (Prod.mk y) (List.finRange representation.width), ?_⟩
  refine ⟨⟨y, rfl⟩, ?_⟩
  exact List.mem_map_of_mem (f := Prod.mk y) (by simp)

noncomputable def FinitePositiveMatrixRepresentation.activeLiftedOutputs {k m : Nat}
    {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M) :
    List (Fin m × Fin representation.width) := by
  classical
  exact representation.allLiftedOutputs.filter fun yw => decide (representation.liftedOutputUsed yw)

noncomputable def FinitePositiveMatrixRepresentation.activeLiftedWidth {k m : Nat}
    {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M) : Nat :=
  representation.activeLiftedOutputs.length

noncomputable def FinitePositiveMatrixRepresentation.activeLiftedOutput {k m : Nat}
    {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (j : Fin representation.activeLiftedWidth) :
    Fin m × Fin representation.width :=
  let hlt : j.1 < representation.activeLiftedOutputs.length := by
    change j.1 < representation.activeLiftedWidth
    exact j.2
  representation.activeLiftedOutputs.get ⟨j.1, hlt⟩

theorem FinitePositiveMatrixRepresentation.activeLiftedOutput_eq {k m : Nat}
    {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (j : Fin representation.activeLiftedWidth) :
    let hlt : j.1 < representation.activeLiftedOutputs.length := by
      change j.1 < representation.activeLiftedWidth
      exact j.2
    representation.activeLiftedOutputs.get ⟨j.1, hlt⟩ = representation.activeLiftedOutput j := by
  simp [FinitePositiveMatrixRepresentation.activeLiftedOutput]

theorem FinitePositiveMatrixRepresentation.activeLiftedOutput_used {k m : Nat}
    {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (j : Fin representation.activeLiftedWidth) :
    representation.liftedOutputUsed (representation.activeLiftedOutput j) := by
  classical
  have h_mem : representation.activeLiftedOutput j ∈ representation.activeLiftedOutputs := by
    unfold FinitePositiveMatrixRepresentation.activeLiftedOutput
    simp
  have h_filter :
      representation.activeLiftedOutput j ∈ representation.allLiftedOutputs ∧
        representation.liftedOutputUsed (representation.activeLiftedOutput j) := by
    simpa [FinitePositiveMatrixRepresentation.activeLiftedOutputs] using h_mem
  exact h_filter.2

theorem FinitePositiveMatrixRepresentation.allLiftedOutputs_nodup {k m : Nat}
    {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M) :
    representation.allLiftedOutputs.Nodup := by
  let block : Fin m → List (Fin m × Fin representation.width) :=
    fun y => (List.finRange representation.width).map (Prod.mk y)
  have h_foldr_nodup :
      (List.foldr (fun y acc => block y ++ acc) [] (List.finRange m)).Nodup := by
    apply List.foldr_append_blocks_nodup (block := block)
    · intro y
      apply List.map_nodup_of_injective (f := Prod.mk y)
      · intro w₁ w₂ h_eq
        exact congrArg Prod.snd h_eq
      · exact List.finRange_nodup representation.width
    · intro y₁ y₂ h_ne yw₁ hyw₁ yw₂ hyw₂
      intro h_eq
      have hyw₁_fst : yw₁.1 = y₁ := by
        unfold block at hyw₁
        rcases List.mem_map.mp hyw₁ with ⟨w, _, rfl⟩
        rfl
      have hyw₂_fst : yw₂.1 = y₂ := by
        unfold block at hyw₂
        rcases List.mem_map.mp hyw₂ with ⟨w, _, rfl⟩
        rfl
      apply h_ne
      calc
        y₁ = yw₁.1 := hyw₁_fst.symm
        _ = yw₂.1 := congrArg Prod.fst h_eq
        _ = y₂ := hyw₂_fst
    · exact List.finRange_nodup m
  simpa [FinitePositiveMatrixRepresentation.allLiftedOutputs, block,
    List.foldr_cons_map_eq_append] using h_foldr_nodup

theorem FinitePositiveMatrixRepresentation.activeLiftedOutputs_nodup {k m : Nat}
    {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M) :
    representation.activeLiftedOutputs.Nodup := by
  classical
  unfold FinitePositiveMatrixRepresentation.activeLiftedOutputs
  exact List.filter_nodup_of_nodup
    (p := fun yw => decide (representation.liftedOutputUsed yw))
    representation.allLiftedOutputs_nodup

theorem FinitePositiveMatrixRepresentation.activeLiftedOutput_injective {k m : Nat}
    {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M) :
    Function.Injective representation.activeLiftedOutput := by
  intro j₁ j₂ h_eq
  let n₁ : Fin representation.activeLiftedOutputs.length :=
    ⟨j₁.1, by
      change j₁.1 < representation.activeLiftedWidth
      exact j₁.2⟩
  let n₂ : Fin representation.activeLiftedOutputs.length :=
    ⟨j₂.1, by
      change j₂.1 < representation.activeLiftedWidth
      exact j₂.2⟩
  have h_get_eq : representation.activeLiftedOutputs.get n₁ = representation.activeLiftedOutputs.get n₂ := by
    simpa [FinitePositiveMatrixRepresentation.activeLiftedOutput, n₁, n₂] using h_eq
  have h_indices : n₁ = n₂ :=
    List.nodup_get_eq representation.activeLiftedOutputs_nodup h_get_eq
  apply Fin.ext
  simpa [n₁, n₂] using congrArg Fin.val h_indices

theorem FinitePositiveMatrixRepresentation.same_w_activeLiftedOutputs_base_ne {k m : Nat}
    {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (j₁ j₂ : Fin representation.activeLiftedWidth)
    (h_w : (representation.activeLiftedOutput j₁).2 = (representation.activeLiftedOutput j₂).2)
    (h_ne : j₁ ≠ j₂) :
    (representation.activeLiftedOutput j₁).1 ≠ (representation.activeLiftedOutput j₂).1 := by
  intro h_base
  apply h_ne
  apply representation.activeLiftedOutput_injective
  exact Prod.ext h_base h_w

theorem FinitePositiveMatrixRepresentation.exists_ordered_duplicate_activeLiftedWitness_of_width_lt_activeLiftedWidth
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (h_lt : representation.width < representation.activeLiftedWidth) :
    ∃ j₁ j₂ : Fin representation.activeLiftedWidth,
      j₁.1 < j₂.1 ∧
        (representation.activeLiftedOutput j₁).2 = (representation.activeLiftedOutput j₂).2 := by
  exact exists_ordered_duplicate_of_lt
    (f := fun j => (representation.activeLiftedOutput j).2) h_lt

theorem FinitePositiveMatrixRepresentation.liftedOutputUsed_conditional_positive
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (yw : Fin m × Fin representation.width)
    (h_used : representation.liftedOutputUsed yw) :
    0 < representation.pW_given_Y yw.1 yw.2 := by
  rcases h_used with ⟨i, h_decode⟩
  have h_entry_pos : 0 < M.entry i yw.1 :=
    representation.decode_eq_implies_positive_entry i yw.1 yw.2 h_decode
  have h_product_pos : 0 < representation.pW_given_Y yw.1 yw.2 * M.entry i yw.1 := by
    calc
      0 < representation.pW yw.2 := representation.positive yw.2
      _ = representation.pW_given_Y yw.1 yw.2 * M.entry i yw.1 := by
            simpa [h_decode] using representation.conditional_factorization i yw.1 yw.2
  exact (Rat.mul_pos_iff_of_pos_right h_entry_pos).mp h_product_pos

theorem FinitePositiveMatrixRepresentation.positive_entry_has_used_lifted_output
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (i : Fin k) (y : Fin m)
    (h_pos : 0 < M.entry i y) :
    ∃ w : Fin representation.width, representation.liftedOutputUsed (y, w) := by
  rcases representation.positive_entry_has_decode i y h_pos with ⟨w, h_decode⟩
  exact ⟨w, i, h_decode⟩

theorem FinitePositiveMatrixRepresentation.base_output_has_used_lifted_output_iff_positive_column
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (y : Fin m) :
    (∃ w : Fin representation.width, representation.liftedOutputUsed (y, w)) ↔
      ∃ i : Fin k, 0 < M.entry i y := by
  constructor
  · intro h_used
    rcases h_used with ⟨w, i, h_decode⟩
    exact ⟨i, representation.decode_eq_implies_positive_entry i y w h_decode⟩
  · intro h_pos
    rcases h_pos with ⟨i, h_pos⟩
    exact representation.positive_entry_has_used_lifted_output i y h_pos

noncomputable def FinitePositiveMatrixRepresentation.conditionalSupportWitnesses
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (y : Fin m) : List (Fin representation.width) := by
  classical
  exact (List.finRange representation.width).filter fun w =>
    decide (representation.liftedOutputUsed (y, w))

noncomputable def FinitePositiveMatrixRepresentation.conditionalSupportWidth
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (y : Fin m) : Nat :=
  (representation.conditionalSupportWitnesses y).length

noncomputable def FinitePositiveMatrixRepresentation.conditionalSupportWitness
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (y : Fin m)
    (j : Fin (representation.conditionalSupportWidth y)) :
    Fin representation.width :=
  let hlt : j.1 < (representation.conditionalSupportWitnesses y).length := by
    change j.1 < representation.conditionalSupportWidth y
    exact j.2
  (representation.conditionalSupportWitnesses y).get ⟨j.1, hlt⟩

theorem FinitePositiveMatrixRepresentation.conditionalSupportWitness_used
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (y : Fin m)
    (j : Fin (representation.conditionalSupportWidth y)) :
    representation.liftedOutputUsed (y, representation.conditionalSupportWitness y j) := by
  classical
  have h_mem : representation.conditionalSupportWitness y j ∈ representation.conditionalSupportWitnesses y := by
    unfold FinitePositiveMatrixRepresentation.conditionalSupportWitness
    simp
  have h_filter :
      representation.conditionalSupportWitness y j ∈ List.finRange representation.width ∧
        representation.liftedOutputUsed (y, representation.conditionalSupportWitness y j) := by
    simpa [FinitePositiveMatrixRepresentation.conditionalSupportWitnesses] using h_mem
  exact h_filter.2

theorem FinitePositiveMatrixRepresentation.conditionalSupportWitness_positive
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (y : Fin m)
    (j : Fin (representation.conditionalSupportWidth y)) :
    0 < representation.pW_given_Y y (representation.conditionalSupportWitness y j) := by
  exact representation.liftedOutputUsed_conditional_positive _
    (representation.conditionalSupportWitness_used y j)

theorem FinitePositiveMatrixRepresentation.conditionalSupportWitnesses_nodup
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (y : Fin m) :
    (representation.conditionalSupportWitnesses y).Nodup := by
  classical
  unfold FinitePositiveMatrixRepresentation.conditionalSupportWitnesses
  exact List.filter_nodup_of_nodup
    (p := fun w => decide (representation.liftedOutputUsed (y, w)))
    (List.finRange_nodup representation.width)

theorem FinitePositiveMatrixRepresentation.conditionalSupportWitness_injective
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (y : Fin m) :
    Function.Injective (representation.conditionalSupportWitness y) := by
  intro j₁ j₂ h_eq
  let n₁ : Fin (representation.conditionalSupportWitnesses y).length := ⟨j₁.1, by
    change j₁.1 < representation.conditionalSupportWidth y
    exact j₁.2⟩
  let n₂ : Fin (representation.conditionalSupportWitnesses y).length := ⟨j₂.1, by
    change j₂.1 < representation.conditionalSupportWidth y
    exact j₂.2⟩
  have h_get_eq : (representation.conditionalSupportWitnesses y).get n₁ =
      (representation.conditionalSupportWitnesses y).get n₂ := by
    simpa [FinitePositiveMatrixRepresentation.conditionalSupportWitness, n₁, n₂] using h_eq
  have h_idx : n₁ = n₂ :=
    List.nodup_get_eq (representation.conditionalSupportWitnesses_nodup y) h_get_eq
  apply Fin.ext
  simpa [n₁, n₂] using congrArg Fin.val h_idx

theorem FinitePositiveMatrixRepresentation.conditionalSupportWitness_cast
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    {y₁ y₂ : Fin m}
    (h : y₁ = y₂)
    (j : Fin (representation.conditionalSupportWidth y₁)) :
    representation.conditionalSupportWitness y₂
    (Fin.cast (by cases h; rfl) j) =
      representation.conditionalSupportWitness y₁ j := by
  cases h
  simp [FinitePositiveMatrixRepresentation.conditionalSupportWitness]

theorem FinitePositiveMatrixRepresentation.conditional_weight_zero_of_not_used
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (y : Fin m)
    (h_pos : ∃ i : Fin k, 0 < M.entry i y)
    (w : Fin representation.width)
    (h_not_used : ¬ representation.liftedOutputUsed (y, w)) :
    representation.pW_given_Y y w = 0 := by
  rcases h_pos with ⟨i, h_entry_pos⟩
  have h_decode_ne : representation.decode i w ≠ y := by
    intro h_decode
    exact h_not_used ⟨i, h_decode⟩
  have h_product_zero : representation.pW_given_Y y w * M.entry i y = 0 := by
    simpa [h_decode_ne] using (representation.conditional_factorization i y w).symm
  by_cases h_neg : representation.pW_given_Y y w < 0
  · have h_product_neg : representation.pW_given_Y y w * M.entry i y < 0 := by
      exact (Rat.mul_neg_iff_of_pos_right h_entry_pos).2 h_neg
    rw [h_product_zero] at h_product_neg
    simp at h_product_neg
  · by_cases h_pos_weight : 0 < representation.pW_given_Y y w
    · have h_product_pos : 0 < representation.pW_given_Y y w * M.entry i y := by
        exact Rat.mul_pos h_pos_weight h_entry_pos
      rw [h_product_zero] at h_product_pos
      simp at h_product_pos
    · exact Rat.le_antisymm (Rat.not_lt.mp h_pos_weight) (Rat.not_lt.mp h_neg)

theorem FinitePositiveMatrixRepresentation.conditionalSupportWidth_pos_of_positive_column
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (y : Fin m)
    (h_pos : ∃ i : Fin k, 0 < M.entry i y) :
    0 < representation.conditionalSupportWidth y := by
  rcases (representation.base_output_has_used_lifted_output_iff_positive_column y).mpr h_pos with
    ⟨w, h_used⟩
  have h_mem : w ∈ representation.conditionalSupportWitnesses y := by
    simp [FinitePositiveMatrixRepresentation.conditionalSupportWitnesses, h_used]
  rcases List.get_of_mem h_mem with ⟨n, hn⟩
  have h_idx : n < representation.conditionalSupportWidth y := by
    simp [FinitePositiveMatrixRepresentation.conditionalSupportWidth]
  omega

theorem FinitePositiveMatrixRepresentation.conditionalSupportWitness_exists_of_used
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (y : Fin m)
    (w : Fin representation.width)
    (h_used : representation.liftedOutputUsed (y, w)) :
    ∃ j : Fin (representation.conditionalSupportWidth y),
      representation.conditionalSupportWitness y j = w := by
  classical
  have h_mem : w ∈ representation.conditionalSupportWitnesses y := by
    have h_filter : w ∈ List.finRange representation.width ∧ representation.liftedOutputUsed (y, w) := by
      exact ⟨by simp, h_used⟩
    simpa [FinitePositiveMatrixRepresentation.conditionalSupportWitnesses] using h_filter
  rcases List.get_of_mem h_mem with ⟨n, hn⟩
  let j : Fin (representation.conditionalSupportWidth y) := ⟨n.1, by
    change n.1 < representation.conditionalSupportWidth y
    simp [FinitePositiveMatrixRepresentation.conditionalSupportWidth]⟩
  refine ⟨j, ?_⟩
  change (representation.conditionalSupportWitnesses y).get n = w
  exact hn

theorem FinitePositiveMatrixRepresentation.conditionalSupportWitness_sum
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (y : Fin m)
    (h_pos : ∃ i : Fin k, 0 < M.entry i y) :
    discrete_sum (fun j : Fin (representation.conditionalSupportWidth y) =>
      representation.pW_given_Y y (representation.conditionalSupportWitness y j)) = 1 := by
  calc
    discrete_sum (fun j : Fin (representation.conditionalSupportWidth y) =>
        representation.pW_given_Y y (representation.conditionalSupportWitness y j)) =
          discrete_sum (representation.pW_given_Y y) := by
            exact discrete_sum_fin_reindex_injective_of_zero_off_range
              (representation.pW_given_Y y)
              (representation.conditionalSupportWitness y)
              (representation.conditionalSupportWitness_injective y)
              (fun w h_off =>
                representation.conditional_weight_zero_of_not_used y h_pos w (by
                  intro h_used
                  rcases representation.conditionalSupportWitness_exists_of_used y w h_used with ⟨j, hj⟩
                  exact h_off j hj))
    _ = 1 := representation.conditional_normalized y

theorem FinitePositiveMatrixRepresentation.conditionalSupportWitnesses_eq_nil_of_no_positive_column
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (y : Fin m)
    (h_none : ¬ ∃ i : Fin k, 0 < M.entry i y) :
    representation.conditionalSupportWitnesses y = [] := by
  classical
  unfold FinitePositiveMatrixRepresentation.conditionalSupportWitnesses
  have h_no_used : ∀ w : Fin representation.width, ¬ representation.liftedOutputUsed (y, w) := by
    intro w h_used
    exact h_none ((representation.base_output_has_used_lifted_output_iff_positive_column y).mp ⟨w, h_used⟩)
  have h_filter_nil :
      ∀ l : List (Fin representation.width),
        List.filter (fun w => decide (representation.liftedOutputUsed (y, w))) l = [] := by
    intro l
    induction l with
    | nil => simp
    | cons w l ih =>
        by_cases h_used : representation.liftedOutputUsed (y, w)
        · exact False.elim (h_no_used w h_used)
        · simp [h_used, ih]
  exact h_filter_nil (List.finRange representation.width)

theorem FinitePositiveMatrixRepresentation.activeLiftedOutputs_filter_base_eq
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (y : Fin m) :
    (representation.activeLiftedOutputs.filter fun yw => decide (yw.1 = y)) =
      (representation.conditionalSupportWitnesses y).map (Prod.mk y) := by
  classical
  let rawBlock : Fin m → List (Fin m × Fin representation.width) := fun y' =>
    List.filter (fun yw => decide (yw.1 = y))
      (List.filter (fun yw => decide (representation.liftedOutputUsed yw))
        (List.map (Prod.mk y') (List.finRange representation.width)))
  let block : Fin m → List (Fin m × Fin representation.width) := fun y' =>
    List.filter (fun yw => decide (yw.1 = y) && decide (representation.liftedOutputUsed yw))
      ((List.finRange representation.width).map (Prod.mk y'))
  have h_raw_block_eq : ∀ y', rawBlock y' = block y' := by
    intro y'
    unfold rawBlock block
    have h_filter_eq :
        ∀ l : List (Fin representation.width),
          List.filter (fun yw => decide (yw.1 = y))
              (List.filter (fun yw => decide (representation.liftedOutputUsed yw))
                (List.map (Prod.mk y') l)) =
            List.filter (fun yw => decide (yw.1 = y) && decide (representation.liftedOutputUsed yw))
              (List.map (Prod.mk y') l) := by
      intro l
      induction l with
      | nil => simp
      | cons w l ih =>
          by_cases h_used : representation.liftedOutputUsed (y', w)
          · by_cases h_eq : y' = y
            · subst h_eq
              simp [h_used, ih]
            · simp [h_used, h_eq, ih]
          · by_cases h_eq : y' = y
            · subst h_eq
              simp [h_used, ih]
            · simp [h_used, h_eq, ih]
    exact h_filter_eq (List.finRange representation.width)
  have h_raw_block_fun : rawBlock = block := by
    funext y'
    exact h_raw_block_eq y'
  have h_mem_y : y ∈ List.finRange m := by
    simp
  have h_block_zero :
      ∀ y', y' ∈ List.finRange m -> y' ≠ y -> block y' = [] := by
    intro y' _ h_ne
    unfold block
    simp [h_ne]
  have h_block_y : block y = (representation.conditionalSupportWitnesses y).map (Prod.mk y) := by
    unfold block FinitePositiveMatrixRepresentation.conditionalSupportWitnesses
    have h_map_filter :
        ∀ l : List (Fin representation.width),
          List.filter (fun a => decide (a.1 = y) && decide (representation.liftedOutputUsed a))
              (List.map (Prod.mk y) l) =
            List.map (Prod.mk y)
              (List.filter (fun w => decide (representation.liftedOutputUsed (y, w))) l) := by
      intro l
      induction l with
      | nil => simp
      | cons w l ih =>
          by_cases h_used : representation.liftedOutputUsed (y, w)
          · simp [h_used, ih]
          · simp [h_used, ih]
    exact h_map_filter (List.finRange representation.width)
  have h_flatten_blocks :
      List.filter (fun yw => decide (yw.1 = y))
          (List.filter (fun yw => decide (representation.liftedOutputUsed yw))
            (List.foldr
              (fun y acc =>
                List.foldr (fun w acc' => (y, w) :: acc') acc (List.finRange representation.width))
              []
              (List.finRange m))) =
        (List.map block (List.finRange m)).flatten := by
    have h_fun :
        ((List.filter fun yw => decide (yw.1 = y)) ∘
            (List.filter fun yw => decide (representation.liftedOutputUsed yw)) ∘
              fun x1 => List.map (Prod.mk x1) (List.finRange representation.width)) = block := by
      funext y'
      exact h_raw_block_eq y'
    simpa using congrArg List.flatten
      (congrArg (fun f => List.map f (List.finRange m)) h_fun)
  unfold FinitePositiveMatrixRepresentation.activeLiftedOutputs
  unfold FinitePositiveMatrixRepresentation.allLiftedOutputs
  calc
    List.filter (fun yw => decide (yw.1 = y))
        (List.filter (fun yw => decide (representation.liftedOutputUsed yw))
          (List.foldr
            (fun y acc =>
              List.foldr (fun w acc' => (y, w) :: acc') acc (List.finRange representation.width))
            []
            (List.finRange m))) = (List.map block (List.finRange m)).flatten := h_flatten_blocks
    _ = block y := by
      exact List.flatten_map_eq_of_nodup_mem block (List.finRange_nodup m) h_mem_y h_block_zero
    _ = (representation.conditionalSupportWitnesses y).map (Prod.mk y) := h_block_y

theorem FinitePositiveMatrixRepresentation.activeLiftedOutputs_eq_blocks
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M) :
    representation.activeLiftedOutputs =
      (List.map (fun y => (representation.conditionalSupportWitnesses y).map (Prod.mk y))
        (List.finRange m)).flatten := by
  classical
  let block : Fin m → List (Fin m × Fin representation.width) := fun y =>
    List.filter (fun yw => decide (representation.liftedOutputUsed yw))
      ((List.finRange representation.width).map (Prod.mk y))
  have h_block_eq :
      ∀ y, block y = (representation.conditionalSupportWitnesses y).map (Prod.mk y) := by
    intro y
    unfold block FinitePositiveMatrixRepresentation.conditionalSupportWitnesses
    have h_map_filter :
        ∀ l : List (Fin representation.width),
          List.filter (fun a => decide (representation.liftedOutputUsed a))
              (List.map (Prod.mk y) l) =
            List.map (Prod.mk y)
              (List.filter (fun w => decide (representation.liftedOutputUsed (y, w))) l) := by
      intro l
      induction l with
      | nil => simp
      | cons w l ih =>
          by_cases h_used : representation.liftedOutputUsed (y, w)
          · simp [h_used, ih]
          · simp [h_used, ih]
    exact h_map_filter (List.finRange representation.width)
  have h_block_fun :
      block = fun y => (representation.conditionalSupportWitnesses y).map (Prod.mk y) := by
    funext y
    exact h_block_eq y
  have h_flatten_blocks :
      List.filter (fun yw => decide (representation.liftedOutputUsed yw))
          (List.foldr
            (fun y acc =>
              List.foldr (fun w acc' => (y, w) :: acc') acc (List.finRange representation.width))
            []
            (List.finRange m)) =
        (List.map block (List.finRange m)).flatten := by
    have h_fun :
        ((List.filter fun yw => decide (representation.liftedOutputUsed yw)) ∘
          fun x1 => List.map (Prod.mk x1) (List.finRange representation.width)) = block := by
      funext y
      rfl
    simpa using congrArg List.flatten
      (congrArg (fun f => List.map f (List.finRange m)) h_fun)
  unfold FinitePositiveMatrixRepresentation.activeLiftedOutputs
  unfold FinitePositiveMatrixRepresentation.allLiftedOutputs
  calc
    List.filter (fun yw => decide (representation.liftedOutputUsed yw))
        (List.foldr
          (fun y acc =>
            List.foldr (fun w acc' => (y, w) :: acc') acc (List.finRange representation.width))
          []
          (List.finRange m)) = (List.map block (List.finRange m)).flatten := h_flatten_blocks
    _ = (List.map (fun y => (representation.conditionalSupportWitnesses y).map (Prod.mk y))
          (List.finRange m)).flatten := by
            rw [h_block_fun]

theorem FinitePositiveMatrixRepresentation.used_lifted_output_has_active_index
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (yw : Fin m × Fin representation.width)
    (h_used : representation.liftedOutputUsed yw) :
    ∃ j : Fin representation.activeLiftedWidth, representation.activeLiftedOutput j = yw := by
  classical
  have h_mem : yw ∈ representation.activeLiftedOutputs := by
    have h_all : yw ∈ representation.allLiftedOutputs :=
      representation.mem_allLiftedOutputs yw.1 yw.2
    have h_filter : yw ∈ representation.allLiftedOutputs ∧ representation.liftedOutputUsed yw :=
      ⟨h_all, h_used⟩
    simpa [FinitePositiveMatrixRepresentation.activeLiftedOutputs] using h_filter
  rcases List.get_of_mem h_mem with ⟨n, hn⟩
  let j : Fin representation.activeLiftedWidth := ⟨n.1, by
    change n.1 < representation.activeLiftedWidth
    exact n.2⟩
  refine ⟨j, ?_⟩
  change representation.activeLiftedOutputs.get n = yw
  exact hn

theorem FinitePositiveMatrixRepresentation.conditionalSupportWitness_has_active_index
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (y : Fin m)
    (j : Fin (representation.conditionalSupportWidth y)) :
    ∃ t : Fin representation.activeLiftedWidth,
      representation.activeLiftedOutput t = (y, representation.conditionalSupportWitness y j) := by
  exact representation.used_lifted_output_has_active_index
    (y, representation.conditionalSupportWitness y j)
    (representation.conditionalSupportWitness_used y j)

theorem FinitePositiveMatrixRepresentation.witness_has_activeLiftedIndex
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (i : Fin k)
    (w : Fin representation.width) :
    ∃ j : Fin representation.activeLiftedWidth,
      representation.activeLiftedOutput j = (representation.decode i w, w) := by
  let yw : Fin m × Fin representation.width := (representation.decode i w, w)
  have h_used : representation.liftedOutputUsed yw := by
    exact ⟨i, rfl⟩
  exact representation.used_lifted_output_has_active_index yw h_used

theorem FinitePositiveMatrixRepresentation.width_le_activeLiftedWidth_of_row
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (i : Fin k) :
    representation.width ≤ representation.activeLiftedWidth := by
  classical
  by_cases h_le : representation.width ≤ representation.activeLiftedWidth
  · exact h_le
  · have h_lt : representation.activeLiftedWidth < representation.width := Nat.lt_of_not_ge h_le
    let pick : Fin representation.width → Fin representation.activeLiftedWidth :=
      fun w => Classical.choose (representation.witness_has_activeLiftedIndex i w)
    have h_pick :
        ∀ w : Fin representation.width,
          representation.activeLiftedOutput (pick w) = (representation.decode i w, w) := by
      intro w
      exact Classical.choose_spec (representation.witness_has_activeLiftedIndex i w)
    rcases exists_duplicate_of_lt (f := pick) h_lt with ⟨w₁, w₂, h_ne, h_eq⟩
    apply False.elim
    apply h_ne
    calc
      w₁ = (representation.activeLiftedOutput (pick w₁)).2 := by
        simpa using congrArg Prod.snd (h_pick w₁).symm
      _ = (representation.activeLiftedOutput (pick w₂)).2 := by rw [h_eq]
      _ = w₂ := by
        simpa using congrArg Prod.snd (h_pick w₂)

theorem FinitePositiveMatrixRepresentation.activeLiftedOutput_conditional_positive
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (j : Fin representation.activeLiftedWidth) :
    0 < representation.pW_given_Y
      (representation.activeLiftedOutput j).1 (representation.activeLiftedOutput j).2 := by
  exact representation.liftedOutputUsed_conditional_positive _
    (representation.activeLiftedOutput_used j)

theorem FinitePositiveMatrixRepresentation.activeLiftedOutput_base_has_positive_entry
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (j : Fin representation.activeLiftedWidth) :
    ∃ i : Fin k, 0 < M.entry i (representation.activeLiftedOutput j).1 := by
  rcases representation.activeLiftedOutput_used j with ⟨i, h_decode⟩
  exact ⟨i, representation.decode_eq_implies_positive_entry i _ _ h_decode⟩

theorem FinitePositiveMatrixRepresentation.activeLiftedOutput_has_conditionalSupportWitness
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (j : Fin representation.activeLiftedWidth) :
    ∃ t : Fin (representation.conditionalSupportWidth (representation.activeLiftedOutput j).1),
      representation.conditionalSupportWitness (representation.activeLiftedOutput j).1 t =
        (representation.activeLiftedOutput j).2 := by
  exact representation.conditionalSupportWitness_exists_of_used
    (representation.activeLiftedOutput j).1
    (representation.activeLiftedOutput j).2
    (representation.activeLiftedOutput_used j)

theorem FinitePositiveMatrixRepresentation.base_output_has_active_lifted_index_iff_positive_column
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (y : Fin m) :
    (∃ j : Fin representation.activeLiftedWidth, (representation.activeLiftedOutput j).1 = y) ↔
      ∃ i : Fin k, 0 < M.entry i y := by
  constructor
  · intro h_active
    rcases h_active with ⟨j, hj⟩
    rcases representation.activeLiftedOutput_base_has_positive_entry j with ⟨i, h_pos⟩
    exact ⟨i, by simpa [hj] using h_pos⟩
  · intro h_pos
    rcases (representation.base_output_has_used_lifted_output_iff_positive_column y).mpr h_pos with
      ⟨w, h_used⟩
    rcases representation.used_lifted_output_has_active_index (y, w) h_used with ⟨j, hj⟩
    exact ⟨j, by simp [hj]⟩

noncomputable def FinitePositiveMatrixRepresentation.activeLiftedRepresentative
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (y : Fin m)
    (h_pos : ∃ i : Fin k, 0 < M.entry i y) :
    Fin representation.activeLiftedWidth :=
  Classical.choose ((representation.base_output_has_active_lifted_index_iff_positive_column y).mpr h_pos)

theorem FinitePositiveMatrixRepresentation.activeLiftedRepresentative_base
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (y : Fin m)
    (h_pos : ∃ i : Fin k, 0 < M.entry i y) :
    (representation.activeLiftedOutput (representation.activeLiftedRepresentative y h_pos)).1 = y := by
  exact Classical.choose_spec
    ((representation.base_output_has_active_lifted_index_iff_positive_column y).mpr h_pos)

noncomputable def FinitePositiveMatrixRepresentation.liftedMatrix {k m : Nat}
    {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M) :
    ConditionalProbabilityMatrix k representation.activeLiftedWidth :=
  { entry := fun i j => representation.liftedChannel i (representation.activeLiftedOutput j)
    nonnegative := by
      intro i j
      let yw := representation.activeLiftedOutput j
      by_cases h_decode :
          representation.decode i yw.2 = yw.1
      · have h_nonneg : 0 ≤ representation.pW (representation.activeLiftedOutput j).2 :=
          Rat.le_of_lt (representation.positive yw.2)
        simpa [yw, FinitePositiveMatrixRepresentation.liftedChannel, h_decode] using h_nonneg
      · simp [yw, FinitePositiveMatrixRepresentation.liftedChannel, h_decode] }

theorem FinitePositiveMatrixRepresentation.liftedMatrix_entry_eq {k m : Nat}
    {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (i : Fin k) (j : Fin representation.activeLiftedWidth) :
    representation.liftedMatrix.entry i j =
      representation.liftedChannel i (representation.activeLiftedOutput j) := by
  rfl

theorem FinitePositiveMatrixRepresentation.liftedMatrix_entry_eq_conditional_weight
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (i : Fin k) (j : Fin representation.activeLiftedWidth) :
    representation.liftedMatrix.entry i j =
      representation.pW_given_Y (representation.activeLiftedOutput j).1
        (representation.activeLiftedOutput j).2 *
          M.entry i (representation.activeLiftedOutput j).1 := by
  let yw := representation.activeLiftedOutput j
  calc
    representation.liftedMatrix.entry i j = representation.liftedChannel i yw := by
      simpa [yw] using representation.liftedMatrix_entry_eq i j
    _ = representation.pW_given_Y yw.1 yw.2 * M.entry i yw.1 := by
      simpa [yw] using representation.liftedChannel_eq_conditional_weight i yw.1 yw.2

theorem FinitePositiveMatrixRepresentation.activeLiftedOutput_column_pattern
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (j : Fin representation.activeLiftedWidth) :
    column_pattern representation.liftedMatrix j =
      column_pattern M (representation.activeLiftedOutput j).1 := by
  let yw := representation.activeLiftedOutput j
  have h_cond : 0 < representation.pW_given_Y yw.1 yw.2 :=
    representation.activeLiftedOutput_conditional_positive j
  calc
    column_pattern representation.liftedMatrix j =
        (fun i => if representation.decode i yw.2 = yw.1 then true else false) := by
          funext i
          by_cases h_decode : representation.decode i yw.2 = yw.1
          · have h_pos : 0 < representation.liftedChannel i yw :=
              (representation.liftedChannel_positive_iff_decode i yw.1 yw.2).mpr h_decode
            simp [column_pattern, representation.liftedMatrix_entry_eq, yw, h_decode, h_pos]
          · have h_not_pos : ¬ 0 < representation.liftedChannel i yw := by
              intro h_pos
              exact h_decode
                ((representation.liftedChannel_positive_iff_decode i yw.1 yw.2).mp h_pos)
            simp [column_pattern, representation.liftedMatrix_entry_eq, yw, h_decode, h_not_pos]
    _ = column_pattern M yw.1 := by
          symm
          exact representation.column_pattern_eq_of_conditional_positive yw.1 yw.2 h_cond

theorem FinitePositiveMatrixRepresentation.activeLiftedOutputs_same_base_same_pattern
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (j₁ j₂ : Fin representation.activeLiftedWidth)
    (h_base : (representation.activeLiftedOutput j₁).1 = (representation.activeLiftedOutput j₂).1) :
    column_pattern representation.liftedMatrix j₁ =
      column_pattern representation.liftedMatrix j₂ := by
  rw [representation.activeLiftedOutput_column_pattern j₁,
    representation.activeLiftedOutput_column_pattern j₂, h_base]

theorem FinitePositiveMatrixRepresentation.liftedMatrix_is_singular
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (h_singular : matrix_is_singular M) :
    matrix_is_singular representation.liftedMatrix := by
  intro j i₁ i₂ h_pos₁ h_pos₂
  let yw := representation.activeLiftedOutput j
  have h_entry₁ : 0 < representation.liftedChannel i₁ yw := by
    simpa [yw] using h_pos₁
  have h_entry₂ : 0 < representation.liftedChannel i₂ yw := by
    simpa [yw] using h_pos₂
  have h_decode₁ : representation.decode i₁ yw.2 = yw.1 :=
    (representation.liftedChannel_positive_iff_decode i₁ yw.1 yw.2).mp h_entry₁
  have h_decode₂ : representation.decode i₂ yw.2 = yw.1 :=
    (representation.liftedChannel_positive_iff_decode i₂ yw.1 yw.2).mp h_entry₂
  have h_Mpos₁ : 0 < M.entry i₁ yw.1 :=
    representation.decode_eq_implies_positive_entry i₁ yw.1 yw.2 h_decode₁
  have h_Mpos₂ : 0 < M.entry i₂ yw.1 :=
    representation.decode_eq_implies_positive_entry i₂ yw.1 yw.2 h_decode₂
  have h_Meq : M.entry i₁ yw.1 = M.entry i₂ yw.1 :=
    h_singular yw.1 i₁ i₂ h_Mpos₁ h_Mpos₂
  calc
    representation.liftedMatrix.entry i₁ j =
        representation.pW_given_Y yw.1 yw.2 * M.entry i₁ yw.1 := by
          simpa [yw] using representation.liftedMatrix_entry_eq_conditional_weight i₁ j
    _ = representation.pW_given_Y yw.1 yw.2 * M.entry i₂ yw.1 := by rw [h_Meq]
    _ = representation.liftedMatrix.entry i₂ j := by
          symm
          simpa [yw] using representation.liftedMatrix_entry_eq_conditional_weight i₂ j

theorem FinitePositiveMatrixRepresentation.activeLiftedOutput_column_value
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (h_singular : matrix_is_singular M)
    (j : Fin representation.activeLiftedWidth) :
    column_value representation.liftedMatrix j =
      representation.pW (representation.activeLiftedOutput j).2 := by
  let yw := representation.activeLiftedOutput j
  rcases representation.activeLiftedOutput_used j with ⟨i, h_decode⟩
  have h_entry_pos : 0 < representation.liftedMatrix.entry i j := by
    have h_pos : 0 < representation.liftedChannel i yw :=
      (representation.liftedChannel_positive_iff_decode i yw.1 yw.2).mpr h_decode
    simpa [yw] using h_pos
  have h_col : column_pattern representation.liftedMatrix j i = true := by
    simp [column_pattern, h_entry_pos]
  have h_entry_eq_value : representation.liftedMatrix.entry i j = column_value representation.liftedMatrix j := by
    rw [entry_eq_column_value_or_zero representation.liftedMatrix
      (representation.liftedMatrix_is_singular h_singular) i j, h_col]
    simp
  have h_entry_eq_pw : representation.liftedMatrix.entry i j = representation.pW yw.2 := by
    calc
      representation.liftedMatrix.entry i j = representation.liftedChannel i yw := by
        simpa [yw] using representation.liftedMatrix_entry_eq i j
      _ = representation.pW yw.2 := by
        simp [FinitePositiveMatrixRepresentation.liftedChannel, yw, h_decode]
  calc
    column_value representation.liftedMatrix j = representation.liftedMatrix.entry i j := by
      symm
      exact h_entry_eq_value
    _ = representation.pW yw.2 := h_entry_eq_pw

theorem FinitePositiveMatrixRepresentation.same_w_activeLiftedOutputs_equal_column_value
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (h_singular : matrix_is_singular M)
    (j₁ j₂ : Fin representation.activeLiftedWidth)
    (h_w : (representation.activeLiftedOutput j₁).2 = (representation.activeLiftedOutput j₂).2) :
    column_value representation.liftedMatrix j₁ = column_value representation.liftedMatrix j₂ := by
  rw [representation.activeLiftedOutput_column_value h_singular j₁,
    representation.activeLiftedOutput_column_value h_singular j₂, h_w]

theorem FinitePositiveMatrixRepresentation.same_w_activeLiftedOutputs_disjoint_support
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (j₁ j₂ : Fin representation.activeLiftedWidth)
    (h_w : (representation.activeLiftedOutput j₁).2 = (representation.activeLiftedOutput j₂).2)
    (h_base_ne : (representation.activeLiftedOutput j₁).1 ≠ (representation.activeLiftedOutput j₂).1) :
    ∀ i : Fin k,
      0 < representation.liftedMatrix.entry i j₁ →
      representation.liftedMatrix.entry i j₂ = 0 := by
  intro i h_pos₁
  let yw₁ := representation.activeLiftedOutput j₁
  let yw₂ := representation.activeLiftedOutput j₂
  have h_decode₁ : representation.decode i yw₁.2 = yw₁.1 := by
    have h_pos_lifted : 0 < representation.liftedChannel i yw₁ := by
      simpa [yw₁] using h_pos₁
    exact (representation.liftedChannel_positive_iff_decode i yw₁.1 yw₁.2).mp h_pos_lifted
  have h_not_pos₂ : ¬ 0 < representation.liftedMatrix.entry i j₂ := by
    intro h_pos₂
    have h_decode₂ : representation.decode i yw₂.2 = yw₂.1 := by
      have h_pos_lifted : 0 < representation.liftedChannel i yw₂ := by
        simpa [yw₂] using h_pos₂
      exact (representation.liftedChannel_positive_iff_decode i yw₂.1 yw₂.2).mp h_pos_lifted
    apply h_base_ne
    calc
      yw₁.1 = representation.decode i yw₁.2 := h_decode₁.symm
      _ = representation.decode i yw₂.2 := by rw [h_w]
      _ = yw₂.1 := h_decode₂
  exact Rat.le_antisymm (Rat.not_lt.mp h_not_pos₂) (representation.liftedMatrix.nonnegative i j₂)

theorem FinitePositiveMatrixRepresentation.same_w_activeLiftedOutputs_reachable_by_pps_ppm_vpm
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (h_singular : matrix_is_singular M)
    (j₁ j₂ : Fin representation.activeLiftedWidth)
    (h_base_ne : (representation.activeLiftedOutput j₁).1 ≠ (representation.activeLiftedOutput j₂).1)
    (h_w : (representation.activeLiftedOutput j₁).2 = (representation.activeLiftedOutput j₂).2) :
    ∃ next : MatrixState k,
      MatrixReachable (pps_ppm_vpm_step (k := k))
        ⟨representation.activeLiftedWidth, representation.liftedMatrix⟩ next := by
  by_cases h_lt : j₁.1 < j₂.1
  · exact ordered_vpm_merge_reachable_by_pps_ppm_vpm_state
      ⟨representation.activeLiftedWidth, representation.liftedMatrix⟩ j₁ j₂ h_lt
      (representation.liftedMatrix_is_singular h_singular)
      (representation.same_w_activeLiftedOutputs_equal_column_value h_singular j₁ j₂ h_w)
      (representation.same_w_activeLiftedOutputs_disjoint_support j₁ j₂ h_w h_base_ne)
  · have h_ne_idx : j₁ ≠ j₂ := by
      intro h_eq
      apply h_base_ne
      simp [h_eq]
    have h_ne_val : j₁.1 ≠ j₂.1 := by
      intro h_eq
      apply h_ne_idx
      apply Fin.ext
      simpa using h_eq
    have h_gt : j₂.1 < j₁.1 := by
      omega
    exact ordered_vpm_merge_reachable_by_pps_ppm_vpm_state
      ⟨representation.activeLiftedWidth, representation.liftedMatrix⟩ j₂ j₁ h_gt
      (representation.liftedMatrix_is_singular h_singular)
      (representation.same_w_activeLiftedOutputs_equal_column_value h_singular j₂ j₁ h_w.symm)
      (representation.same_w_activeLiftedOutputs_disjoint_support j₂ j₁ h_w.symm h_base_ne.symm)

theorem FinitePositiveMatrixRepresentation.activeLiftedRepresentative_same_pattern
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (y : Fin m)
    (h_pos : ∃ i : Fin k, 0 < M.entry i y)
    (j : Fin representation.activeLiftedWidth)
    (h_base : (representation.activeLiftedOutput j).1 = y) :
    column_pattern representation.liftedMatrix j =
      column_pattern representation.liftedMatrix (representation.activeLiftedRepresentative y h_pos) := by
  apply representation.activeLiftedOutputs_same_base_same_pattern j
    (representation.activeLiftedRepresentative y h_pos)
  rw [h_base, representation.activeLiftedRepresentative_base y h_pos]

noncomputable def supportedOutputs {k m : Nat}
    (M : ConditionalProbabilityMatrix k m) : List (Fin m) := by
  classical
  exact (List.finRange m).filter fun y => decide (∃ i : Fin k, 0 < M.entry i y)

noncomputable def supportedWidth {k m : Nat}
    (M : ConditionalProbabilityMatrix k m) : Nat :=
  (supportedOutputs M).length

noncomputable def supportedOutput {k m : Nat}
    (M : ConditionalProbabilityMatrix k m)
    (j : Fin (supportedWidth M)) : Fin m :=
  let hlt : j.1 < (supportedOutputs M).length := by
    change j.1 < supportedWidth M
    exact j.2
  (supportedOutputs M).get ⟨j.1, hlt⟩

theorem supportedOutput_has_positive_entry {k m : Nat}
    (M : ConditionalProbabilityMatrix k m)
    (j : Fin (supportedWidth M)) :
    ∃ i : Fin k, 0 < M.entry i (supportedOutput M j) := by
  classical
  have h_mem : supportedOutput M j ∈ supportedOutputs M := by
    unfold supportedOutput
    simp
  have h_filter : supportedOutput M j ∈ List.finRange m ∧ ∃ i : Fin k, 0 < M.entry i (supportedOutput M j) := by
    simpa [supportedOutputs] using h_mem
  exact h_filter.2

theorem supportedOutputs_nodup {k m : Nat}
    (M : ConditionalProbabilityMatrix k m) :
    (supportedOutputs M).Nodup := by
  classical
  unfold supportedOutputs
  exact List.filter_nodup_of_nodup
    (p := fun y => decide (∃ i : Fin k, 0 < M.entry i y))
    (List.finRange_nodup m)

theorem supportedOutput_injective {k m : Nat}
    (M : ConditionalProbabilityMatrix k m) :
    Function.Injective (supportedOutput M) := by
  intro j₁ j₂ h_eq
  have h_n₁ : j₁.1 < (supportedOutputs M).length := by
    change j₁.1 < supportedWidth M
    exact j₁.2
  have h_n₂ : j₂.1 < (supportedOutputs M).length := by
    change j₂.1 < supportedWidth M
    exact j₂.2
  let n₁ : Fin (supportedOutputs M).length := ⟨j₁.1, h_n₁⟩
  let n₂ : Fin (supportedOutputs M).length := ⟨j₂.1, h_n₂⟩
  have h_get_eq : (supportedOutputs M).get n₁ = (supportedOutputs M).get n₂ := by
    simpa [supportedOutput, n₁, n₂] using h_eq
  have h_idx : n₁ = n₂ :=
    List.nodup_get_eq (supportedOutputs_nodup M) h_get_eq
  have h_val : j₁.1 = j₂.1 := by
    simpa [n₁, n₂] using congrArg Fin.val h_idx
  exact Fin.ext h_val

theorem FinitePositiveMatrixRepresentation.decode_mem_supportedOutputs
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (i : Fin k) (w : Fin representation.width) :
    representation.decode i w ∈ supportedOutputs M := by
  have h_pos : 0 < M.entry i (representation.decode i w) :=
    representation.decode_eq_implies_positive_entry i _ w rfl
  have h_filter :
      representation.decode i w ∈ List.finRange m ∧
        ∃ i' : Fin k, 0 < M.entry i' (representation.decode i w) := by
    exact ⟨by simp, ⟨i, h_pos⟩⟩
  simpa [supportedOutputs] using h_filter

theorem FinitePositiveMatrixRepresentation.decode_has_supportedOutput
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (i : Fin k) (w : Fin representation.width) :
    ∃ y : Fin (supportedWidth M), supportedOutput M y = representation.decode i w := by
  classical
  have h_mem : representation.decode i w ∈ supportedOutputs M :=
    representation.decode_mem_supportedOutputs i w
  rcases List.get_of_mem h_mem with ⟨n, hn⟩
  have h_lt : n.1 < supportedWidth M := by
    change n.1 < (supportedOutputs M).length
    exact n.2
  refine ⟨⟨n.1, h_lt⟩, ?_⟩
  change (supportedOutputs M).get n = representation.decode i w
  exact hn

noncomputable def FinitePositiveMatrixRepresentation.supportedDecode
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (i : Fin k) (w : Fin representation.width) : Fin (supportedWidth M) :=
  Classical.choose (representation.decode_has_supportedOutput i w)

theorem FinitePositiveMatrixRepresentation.supportedDecode_spec
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (i : Fin k) (w : Fin representation.width) :
    supportedOutput M (representation.supportedDecode i w) = representation.decode i w := by
  exact Classical.choose_spec (representation.decode_has_supportedOutput i w)

theorem FinitePositiveMatrixRepresentation.supportedDecode_eq_iff
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (i : Fin k) (w : Fin representation.width)
    (y : Fin (supportedWidth M)) :
    representation.supportedDecode i w = y ↔
      representation.decode i w = supportedOutput M y := by
  constructor
  · intro h_eq
    calc
      representation.decode i w = supportedOutput M (representation.supportedDecode i w) :=
        (representation.supportedDecode_spec i w).symm
      _ = supportedOutput M y := by simp [h_eq]
  · intro h_eq
    apply supportedOutput_injective M
    calc
      supportedOutput M (representation.supportedDecode i w) = representation.decode i w :=
        representation.supportedDecode_spec i w
      _ = supportedOutput M y := h_eq

theorem FinitePositiveMatrixRepresentation.activeLiftedOutputs_eq_supportedBlocks
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M) :
    representation.activeLiftedOutputs =
      (List.map (fun y => (representation.conditionalSupportWitnesses y).map (Prod.mk y))
        (supportedOutputs M)).flatten := by
  classical
  let block : Fin m → List (Fin m × Fin representation.width) :=
    fun y => (representation.conditionalSupportWitnesses y).map (Prod.mk y)
  let supported : Fin m → Bool := fun y => decide (∃ i : Fin k, 0 < M.entry i y)
  let paddedBlock : Fin m → List (Fin m × Fin representation.width) :=
    fun y => if supported y then block y else []
  have h_block_padded : ∀ y, block y = paddedBlock y := by
    intro y
    by_cases h_pos : ∃ i : Fin k, 0 < M.entry i y
    · simp [block, paddedBlock, supported, h_pos]
    · have h_nil := representation.conditionalSupportWitnesses_eq_nil_of_no_positive_column y h_pos
      simp [block, paddedBlock, supported, h_pos, h_nil]
  have h_block_padded_fun : block = paddedBlock := by
    funext y
    exact h_block_padded y
  calc
    representation.activeLiftedOutputs = (List.map block (List.finRange m)).flatten := by
      simpa [block] using representation.activeLiftedOutputs_eq_blocks
    _ = (List.map paddedBlock (List.finRange m)).flatten := by
      rw [h_block_padded_fun]
    _ = (List.map block ((List.finRange m).filter fun y => supported y)).flatten := by
      exact List.flatten_map_filter_eq block supported (List.finRange m)
    _ = (List.map block (supportedOutputs M)).flatten := by
      simp [supportedOutputs, supported]
    _ = (List.map (fun y => (representation.conditionalSupportWitnesses y).map (Prod.mk y))
          (supportedOutputs M)).flatten := by
            simp [block]

theorem FinitePositiveMatrixRepresentation.supportedOutput_conditionalSupportWidth_pos
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (j : Fin (supportedWidth M)) :
    0 < representation.conditionalSupportWidth (supportedOutput M j) := by
  exact representation.conditionalSupportWidth_pos_of_positive_column
    (supportedOutput M j)
    (supportedOutput_has_positive_entry M j)

theorem FinitePositiveMatrixRepresentation.activeLiftedOutputs_eq_first_supported_block_append
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (h_support : 0 < supportedWidth M) :
    ∃ tail : List (Fin m × Fin representation.width),
      representation.activeLiftedOutputs =
        (representation.conditionalSupportWitnesses (supportedOutput M ⟨0, h_support⟩)).map
          (Prod.mk (supportedOutput M ⟨0, h_support⟩)) ++ tail := by
  classical
  let j0 : Fin (supportedWidth M) := ⟨0, h_support⟩
  cases h_list : supportedOutputs M with
  | nil =>
      unfold supportedWidth at h_support
      simp [h_list] at h_support
  | cons y0 ys =>
      have h_head : supportedOutput M j0 = y0 := by
        unfold supportedOutput supportedWidth
        simp [j0, h_list]
      refine ⟨(List.map (fun y => (representation.conditionalSupportWitnesses y).map (Prod.mk y)) ys).flatten, ?_⟩
      calc
        representation.activeLiftedOutputs =
            (List.map (fun y => (representation.conditionalSupportWitnesses y).map (Prod.mk y))
              (supportedOutputs M)).flatten := representation.activeLiftedOutputs_eq_supportedBlocks
        _ = (representation.conditionalSupportWitnesses y0).map (Prod.mk y0) ++
              (List.map (fun y => (representation.conditionalSupportWitnesses y).map (Prod.mk y)) ys).flatten := by
              simp [h_list]
          _ = (representation.conditionalSupportWitnesses (supportedOutput M j0)).map
            (Prod.mk (supportedOutput M j0)) ++
              (List.map (fun y => (representation.conditionalSupportWitnesses y).map (Prod.mk y)) ys).flatten := by
            simp [h_head]

  theorem FinitePositiveMatrixRepresentation.firstSupportedBlockIndex_lt_activeLiftedWidth
      {k m : Nat} {M : ConditionalProbabilityMatrix k m}
      (representation : FinitePositiveMatrixRepresentation M)
      (h_support : 0 < supportedWidth M)
      (j : Fin (representation.conditionalSupportWidth (supportedOutput M ⟨0, h_support⟩))) :
      j.1 < representation.activeLiftedWidth := by
    classical
    rcases representation.activeLiftedOutputs_eq_first_supported_block_append h_support with ⟨tail, h_append⟩
    have h_block_lt :
        j.1 < ((representation.conditionalSupportWitnesses (supportedOutput M ⟨0, h_support⟩)).map
          (Prod.mk (supportedOutput M ⟨0, h_support⟩))).length := by
      simp [FinitePositiveMatrixRepresentation.conditionalSupportWidth]
    rw [FinitePositiveMatrixRepresentation.activeLiftedWidth, h_append]
    simp [List.length_append] at h_block_lt ⊢
    omega

  theorem FinitePositiveMatrixRepresentation.activeLiftedOutput_eq_first_supported_block
      {k m : Nat} {M : ConditionalProbabilityMatrix k m}
      (representation : FinitePositiveMatrixRepresentation M)
      (h_support : 0 < supportedWidth M)
      (j : Fin (representation.conditionalSupportWidth (supportedOutput M ⟨0, h_support⟩))) :
      representation.activeLiftedOutput
          ⟨j.1, representation.firstSupportedBlockIndex_lt_activeLiftedWidth h_support j⟩ =
        (supportedOutput M ⟨0, h_support⟩,
          representation.conditionalSupportWitness (supportedOutput M ⟨0, h_support⟩) j) := by
    classical
    let base : Fin m := supportedOutput M ⟨0, h_support⟩
    let jActive : Fin representation.activeLiftedWidth :=
      ⟨j.1, representation.firstSupportedBlockIndex_lt_activeLiftedWidth h_support j⟩
    let jBlock : Fin (((representation.conditionalSupportWitnesses base).map (Prod.mk base)).length) :=
      ⟨j.1, by
        simp [base, FinitePositiveMatrixRepresentation.conditionalSupportWidth]⟩
    rcases representation.activeLiftedOutputs_eq_first_supported_block_append h_support with ⟨tail, h_append⟩
    have hltActive : j.1 < representation.activeLiftedOutputs.length := by
      change j.1 < representation.activeLiftedWidth
      exact representation.firstSupportedBlockIndex_lt_activeLiftedWidth h_support j
    have h_get_prefix :
        representation.activeLiftedOutputs.get
          ⟨j.1, hltActive⟩ =
          ((representation.conditionalSupportWitnesses base).map (Prod.mk base)).get jBlock := by
      simpa [h_append, jBlock, base, hltActive] using List.get_append_left_eq (l₂ := tail) jBlock
    have h_block_get :
        ((representation.conditionalSupportWitnesses base).map (Prod.mk base)).get jBlock =
          (base, representation.conditionalSupportWitness base j) := by
      unfold FinitePositiveMatrixRepresentation.conditionalSupportWitness
      simp [jBlock, base]
    calc
      representation.activeLiftedOutput jActive =
          representation.activeLiftedOutputs.get ⟨j.1, hltActive⟩ := by
            symm
            simpa [jActive, hltActive] using representation.activeLiftedOutput_eq jActive
      _ = ((representation.conditionalSupportWitnesses base).map (Prod.mk base)).get jBlock := h_get_prefix
      _ = (base, representation.conditionalSupportWitness base j) := h_block_get

  theorem FinitePositiveMatrixRepresentation.liftedMatrix_entry_eq_first_supported_block
      {k m : Nat} {M : ConditionalProbabilityMatrix k m}
      (representation : FinitePositiveMatrixRepresentation M)
      (h_support : 0 < supportedWidth M)
      (i : Fin k)
      (j : Fin (representation.conditionalSupportWidth (supportedOutput M ⟨0, h_support⟩))) :
      representation.liftedMatrix.entry i
          ⟨j.1, representation.firstSupportedBlockIndex_lt_activeLiftedWidth h_support j⟩ =
        representation.pW_given_Y (supportedOutput M ⟨0, h_support⟩)
          (representation.conditionalSupportWitness (supportedOutput M ⟨0, h_support⟩) j) *
            M.entry i (supportedOutput M ⟨0, h_support⟩) := by
    let base : Fin m := supportedOutput M ⟨0, h_support⟩
    let jActive : Fin representation.activeLiftedWidth :=
      ⟨j.1, representation.firstSupportedBlockIndex_lt_activeLiftedWidth h_support j⟩
    calc
      representation.liftedMatrix.entry i jActive =
          representation.pW_given_Y (representation.activeLiftedOutput jActive).1
            (representation.activeLiftedOutput jActive).2 *
              M.entry i (representation.activeLiftedOutput jActive).1 := by
            simpa [jActive] using representation.liftedMatrix_entry_eq_conditional_weight i jActive
      _ = representation.pW_given_Y base (representation.conditionalSupportWitness base j) *
            M.entry i base := by
            simp [base, jActive, representation.activeLiftedOutput_eq_first_supported_block h_support j]

noncomputable def FinitePositiveMatrixRepresentation.firstSupportedBase
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (h_support : 0 < supportedWidth M) : Fin m :=
  let _ := representation.activeLiftedWidth
  supportedOutput M ⟨0, h_support⟩

theorem FinitePositiveMatrixRepresentation.firstSupportedBase_conditionalSupportWidth_le_activeLiftedWidth
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (h_support : 0 < supportedWidth M) :
    representation.conditionalSupportWidth (representation.firstSupportedBase h_support) ≤
      representation.activeLiftedWidth := by
  classical
  rcases representation.activeLiftedOutputs_eq_first_supported_block_append h_support with ⟨tail, h_append⟩
  rw [FinitePositiveMatrixRepresentation.activeLiftedWidth, h_append]
  simp [FinitePositiveMatrixRepresentation.firstSupportedBase,
    FinitePositiveMatrixRepresentation.conditionalSupportWidth, List.length_append]

theorem FinitePositiveMatrixRepresentation.firstSupportedBase_conditionalSupportWidth_pos
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (h_support : 0 < supportedWidth M) :
    0 < representation.conditionalSupportWidth (representation.firstSupportedBase h_support) := by
  simpa [FinitePositiveMatrixRepresentation.firstSupportedBase] using
    representation.supportedOutput_conditionalSupportWidth_pos
      (j := ⟨0, h_support⟩)

noncomputable def FinitePositiveMatrixRepresentation.firstSupportedTailWidth
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (h_support : 0 < supportedWidth M) : Nat :=
  representation.activeLiftedWidth -
    representation.conditionalSupportWidth (representation.firstSupportedBase h_support)

theorem FinitePositiveMatrixRepresentation.firstSupportedWidths_add
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (h_support : 0 < supportedWidth M) :
    representation.conditionalSupportWidth (representation.firstSupportedBase h_support) +
      representation.firstSupportedTailWidth h_support = representation.activeLiftedWidth := by
  unfold FinitePositiveMatrixRepresentation.firstSupportedTailWidth
  have h_le :=
    representation.firstSupportedBase_conditionalSupportWidth_le_activeLiftedWidth h_support
  omega

noncomputable def FinitePositiveMatrixRepresentation.firstSupportedMass
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (h_support : 0 < supportedWidth M) :
    Fin (representation.conditionalSupportWidth (representation.firstSupportedBase h_support)) → Probability :=
  fun j => representation.pW_given_Y (representation.firstSupportedBase h_support)
    (representation.conditionalSupportWitness (representation.firstSupportedBase h_support) j)

theorem FinitePositiveMatrixRepresentation.firstSupportedMass_positive
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (h_support : 0 < supportedWidth M)
    (j : Fin (representation.conditionalSupportWidth (representation.firstSupportedBase h_support))) :
    0 < representation.firstSupportedMass h_support j := by
  exact representation.conditionalSupportWitness_positive _ j

theorem FinitePositiveMatrixRepresentation.firstSupportedMass_nonnegative
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (h_support : 0 < supportedWidth M)
    (j : Fin (representation.conditionalSupportWidth (representation.firstSupportedBase h_support))) :
    0 ≤ representation.firstSupportedMass h_support j := by
  exact Rat.le_of_lt (representation.firstSupportedMass_positive h_support j)

theorem FinitePositiveMatrixRepresentation.firstSupportedMass_sum_one
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (h_support : 0 < supportedWidth M) :
    discrete_sum (representation.firstSupportedMass h_support) = 1 := by
  simpa [FinitePositiveMatrixRepresentation.firstSupportedMass,
    FinitePositiveMatrixRepresentation.firstSupportedBase] using
    representation.conditionalSupportWitness_sum
      (supportedOutput M ⟨0, h_support⟩)
      (supportedOutput_has_positive_entry M ⟨0, h_support⟩)

noncomputable def FinitePositiveMatrixRepresentation.firstSupportedCollapsedMatrix
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (h_support : 0 < supportedWidth M) :
    ConditionalProbabilityMatrix k (representation.firstSupportedTailWidth h_support + 1) :=
  { entry := fun i j =>
      if h_zero : j.1 = 0 then
        M.entry i (representation.firstSupportedBase h_support)
      else
        representation.liftedMatrix.entry i ⟨
          representation.conditionalSupportWidth (representation.firstSupportedBase h_support) + (j.1 - 1), by
            have h_front_le :=
              representation.firstSupportedBase_conditionalSupportWidth_le_activeLiftedWidth h_support
            have h_lt : j.1 < representation.firstSupportedTailWidth h_support + 1 := j.2
            unfold FinitePositiveMatrixRepresentation.firstSupportedTailWidth at h_lt
            omega⟩
    nonnegative := by
      intro i j
      by_cases h_zero : j.1 = 0
      · dsimp
        rw [dif_pos h_zero]
        exact M.nonnegative i (representation.firstSupportedBase h_support)
      · dsimp
        rw [dif_neg h_zero]
        exact representation.liftedMatrix.nonnegative i ⟨
          representation.conditionalSupportWidth (representation.firstSupportedBase h_support) + (j.1 - 1), by
            have h_lt : j.1 < representation.firstSupportedTailWidth h_support + 1 := j.2
            have h_pos : 1 ≤ j.1 := Nat.succ_le_of_lt (Nat.pos_of_ne_zero h_zero)
            have h_tail : j.1 - 1 < representation.firstSupportedTailWidth h_support := by
              omega
            have h_sum :
                representation.conditionalSupportWidth (representation.firstSupportedBase h_support) +
                  representation.firstSupportedTailWidth h_support = representation.activeLiftedWidth :=
              representation.firstSupportedWidths_add h_support
            have h_bound :
                representation.conditionalSupportWidth (representation.firstSupportedBase h_support) + (j.1 - 1) <
                  representation.conditionalSupportWidth (representation.firstSupportedBase h_support) +
                    representation.firstSupportedTailWidth h_support := by
              exact Nat.add_lt_add_left h_tail _
            simpa [h_sum] using h_bound⟩ }

theorem FinitePositiveMatrixRepresentation.firstSupportedCollapsedMatrix_head
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (h_support : 0 < supportedWidth M)
    (i : Fin k) :
    (representation.firstSupportedCollapsedMatrix h_support).entry i 0 =
      M.entry i (representation.firstSupportedBase h_support) := by
  simp [FinitePositiveMatrixRepresentation.firstSupportedCollapsedMatrix,
    FinitePositiveMatrixRepresentation.firstSupportedBase]

theorem FinitePositiveMatrixRepresentation.firstSupportedCollapsedMatrix_tail
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (h_support : 0 < supportedWidth M)
    (i : Fin k)
    (j : Fin (representation.firstSupportedTailWidth h_support)) :
    (representation.firstSupportedCollapsedMatrix h_support).entry i j.succ =
      representation.liftedMatrix.entry i ⟨
        representation.conditionalSupportWidth (representation.firstSupportedBase h_support) + j.1, by
          have h_front_le :=
            representation.firstSupportedBase_conditionalSupportWidth_le_activeLiftedWidth h_support
          have h_lt : j.1 < representation.firstSupportedTailWidth h_support := j.2
          unfold FinitePositiveMatrixRepresentation.firstSupportedTailWidth at h_lt
          omega⟩ := by
  let base : Fin m := representation.firstSupportedBase h_support
  let tailIndex : Fin representation.activeLiftedWidth := ⟨
    representation.conditionalSupportWidth base + j.1, by
      have h_lt : j.1 < representation.firstSupportedTailWidth h_support := j.2
      have h_sum := representation.firstSupportedWidths_add h_support
      have h_bound :
          representation.conditionalSupportWidth base + j.1 <
            representation.conditionalSupportWidth base + representation.firstSupportedTailWidth h_support := by
        exact Nat.add_lt_add_left h_lt _
      simpa [base, h_sum] using h_bound⟩
  have h_zero : ¬ ((j.succ : Fin (representation.firstSupportedTailWidth h_support + 1)).1 = 0) := by
    simp
  have h_zero_fin : (j.succ : Fin (representation.firstSupportedTailWidth h_support + 1)) ≠ 0 := by
    intro h_eq
    apply h_zero
    simpa using congrArg Fin.val h_eq
  have h_sub : ((j.succ : Fin (representation.firstSupportedTailWidth h_support + 1)).1 - 1) = j.1 := by
    simp
  calc
    (representation.firstSupportedCollapsedMatrix h_support).entry i j.succ =
        representation.liftedMatrix.entry i ⟨
          representation.conditionalSupportWidth base + ((j.succ : Fin (representation.firstSupportedTailWidth h_support + 1)).1 - 1), by
            have h_tail : ((j.succ : Fin (representation.firstSupportedTailWidth h_support + 1)).1 - 1) <
                representation.firstSupportedTailWidth h_support := by
              simp
            have h_sum := representation.firstSupportedWidths_add h_support
            have h_bound :
                representation.conditionalSupportWidth base +
                    ((j.succ : Fin (representation.firstSupportedTailWidth h_support + 1)).1 - 1) <
                  representation.conditionalSupportWidth base +
                    representation.firstSupportedTailWidth h_support := by
              exact Nat.add_lt_add_left h_tail _
            simpa [base, h_sum] using h_bound⟩ := by
          dsimp [FinitePositiveMatrixRepresentation.firstSupportedCollapsedMatrix]
    _ = representation.liftedMatrix.entry i tailIndex := by
          apply congrArg (representation.liftedMatrix.entry i)
          apply Fin.ext
          simp [tailIndex]
    _ = representation.liftedMatrix.entry i ⟨
          representation.conditionalSupportWidth (representation.firstSupportedBase h_support) + j.1, by
            have h_front_le :=
              representation.firstSupportedBase_conditionalSupportWidth_le_activeLiftedWidth h_support
            have h_lt : j.1 < representation.firstSupportedTailWidth h_support := j.2
            unfold FinitePositiveMatrixRepresentation.firstSupportedTailWidth at h_lt
            omega⟩ := by
          rfl

theorem FinitePositiveMatrixRepresentation.firstSupportedCollapsedMatrix_is_singular
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (h_support : 0 < supportedWidth M)
    (h_singular : matrix_is_singular M) :
    matrix_is_singular (representation.firstSupportedCollapsedMatrix h_support) := by
  intro j i₁ i₂ h_pos₁ h_pos₂
  by_cases h_zero : j.1 = 0
  · have h_j0 : j = 0 := by
      apply Fin.ext
      exact h_zero
    subst j
    have h_base₁ : 0 < M.entry i₁ (representation.firstSupportedBase h_support) := by
      simpa [representation.firstSupportedCollapsedMatrix_head h_support i₁] using h_pos₁
    have h_base₂ : 0 < M.entry i₂ (representation.firstSupportedBase h_support) := by
      simpa [representation.firstSupportedCollapsedMatrix_head h_support i₂] using h_pos₂
    simpa [representation.firstSupportedCollapsedMatrix_head h_support i₁,
      representation.firstSupportedCollapsedMatrix_head h_support i₂] using
        h_singular (representation.firstSupportedBase h_support) i₁ i₂ h_base₁ h_base₂
  · let tail : Fin (representation.firstSupportedTailWidth h_support) := ⟨j.1 - 1, by
      have h_lt : j.1 < representation.firstSupportedTailWidth h_support + 1 := j.2
      have h_pos : 1 ≤ j.1 := Nat.succ_le_of_lt (Nat.pos_of_ne_zero h_zero)
      omega⟩
    have h_jsucc : j = tail.succ := by
      apply Fin.ext
      dsimp [tail]
      exact (Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.pos_of_ne_zero h_zero))).symm
    let tailIndex : Fin representation.activeLiftedWidth := ⟨
      representation.conditionalSupportWidth (representation.firstSupportedBase h_support) + tail.1, by
        have h_lt : tail.1 < representation.firstSupportedTailWidth h_support := tail.2
        have h_sum := representation.firstSupportedWidths_add h_support
        have h_bound :
            representation.conditionalSupportWidth (representation.firstSupportedBase h_support) + tail.1 <
              representation.conditionalSupportWidth (representation.firstSupportedBase h_support) +
                representation.firstSupportedTailWidth h_support := by
          exact Nat.add_lt_add_left h_lt _
        simpa [h_sum] using h_bound⟩
    have h_pos₁' : 0 < (representation.firstSupportedCollapsedMatrix h_support).entry i₁ tail.succ := by
      simpa [h_jsucc] using h_pos₁
    have h_pos₂' : 0 < (representation.firstSupportedCollapsedMatrix h_support).entry i₂ tail.succ := by
      simpa [h_jsucc] using h_pos₂
    have h_tail₁ : 0 < representation.liftedMatrix.entry i₁ tailIndex := by
      rw [representation.firstSupportedCollapsedMatrix_tail h_support i₁ tail] at h_pos₁'
      simpa [tailIndex] using h_pos₁'
    have h_tail₂ : 0 < representation.liftedMatrix.entry i₂ tailIndex := by
      rw [representation.firstSupportedCollapsedMatrix_tail h_support i₂ tail] at h_pos₂'
      simpa [tailIndex] using h_pos₂'
    calc
      (representation.firstSupportedCollapsedMatrix h_support).entry i₁ j =
          (representation.firstSupportedCollapsedMatrix h_support).entry i₁ tail.succ := by
        rw [h_jsucc]
      _ =
          representation.liftedMatrix.entry i₁ tailIndex := by
            simpa [tailIndex] using representation.firstSupportedCollapsedMatrix_tail h_support i₁ tail
      _ = representation.liftedMatrix.entry i₂ tailIndex := by
            exact representation.liftedMatrix_is_singular h_singular tailIndex i₁ i₂ h_tail₁ h_tail₂
      _ = (representation.firstSupportedCollapsedMatrix h_support).entry i₂ tail.succ := by
            symm
            simpa [tailIndex] using representation.firstSupportedCollapsedMatrix_tail h_support i₂ tail
      _ = (representation.firstSupportedCollapsedMatrix h_support).entry i₂ j := by
        rw [h_jsucc]

theorem FinitePositiveMatrixRepresentation.liftedMatrix_entry_eq_firstSupportedMass_mul_collapsedHead
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (h_support : 0 < supportedWidth M)
    (i : Fin k)
    (j : Fin (representation.conditionalSupportWidth (representation.firstSupportedBase h_support))) :
    representation.liftedMatrix.entry i
        ⟨j.1, representation.firstSupportedBlockIndex_lt_activeLiftedWidth h_support j⟩ =
      representation.firstSupportedMass h_support j *
        (representation.firstSupportedCollapsedMatrix h_support).entry i 0 := by
  calc
    representation.liftedMatrix.entry i
        ⟨j.1, representation.firstSupportedBlockIndex_lt_activeLiftedWidth h_support j⟩ =
          representation.firstSupportedMass h_support j *
            M.entry i (representation.firstSupportedBase h_support) := by
              simpa [FinitePositiveMatrixRepresentation.firstSupportedMass,
                FinitePositiveMatrixRepresentation.firstSupportedBase] using
                representation.liftedMatrix_entry_eq_first_supported_block h_support i j
    _ = representation.firstSupportedMass h_support j *
          (representation.firstSupportedCollapsedMatrix h_support).entry i 0 := by
            rw [representation.firstSupportedCollapsedMatrix_head h_support i]

theorem FinitePositiveMatrixRepresentation.liftedMatrix_entry_eq_firstSupportedCollapsedMatrix_tail
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (h_support : 0 < supportedWidth M)
    (i : Fin k)
    (j : Fin (representation.firstSupportedTailWidth h_support)) :
    representation.liftedMatrix.entry i ⟨
      representation.conditionalSupportWidth (representation.firstSupportedBase h_support) + j.1, by
        have h_front_le :=
          representation.firstSupportedBase_conditionalSupportWidth_le_activeLiftedWidth h_support
        have h_lt : j.1 < representation.firstSupportedTailWidth h_support := j.2
        unfold FinitePositiveMatrixRepresentation.firstSupportedTailWidth at h_lt
        omega⟩ =
      (representation.firstSupportedCollapsedMatrix h_support).entry i j.succ := by
  symm
  exact representation.firstSupportedCollapsedMatrix_tail h_support i j

noncomputable def FinitePositiveMatrixRepresentation.firstSupportedPrependedMatrix
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (h_support : 0 < supportedWidth M) :
    ConditionalProbabilityMatrix k representation.activeLiftedWidth :=
  (prependSourceMassMatrixPositiveWidth
      (representation.firstSupportedCollapsedMatrix h_support)
      (representation.firstSupportedMass h_support)
      (representation.firstSupportedMass_nonnegative h_support)
      (representation.firstSupportedBase_conditionalSupportWidth_pos h_support)).cast
    (representation.firstSupportedWidths_add h_support)

theorem FinitePositiveMatrixRepresentation.liftedMatrix_eq_firstSupportedPrependedMatrix
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (h_support : 0 < supportedWidth M) :
    representation.liftedMatrix = representation.firstSupportedPrependedMatrix h_support := by
  let front : Nat := representation.conditionalSupportWidth (representation.firstSupportedBase h_support)
  let tail : Nat := representation.firstSupportedTailWidth h_support
  apply ConditionalProbabilityMatrix.ext
  intro i j
  by_cases h_head : j.1 < front
  · let head : Fin front := ⟨j.1, h_head⟩
    let activeHeadIndex : Fin representation.activeLiftedWidth := ⟨head.1, by
      simpa [front] using representation.firstSupportedBlockIndex_lt_activeLiftedWidth h_support head⟩
    let prepHeadIndex : Fin (front + tail) := ⟨head.1, by
      have h_le : front ≤ front + tail := Nat.le_add_right front tail
      exact Nat.lt_of_lt_of_le head.2 h_le⟩
    have h_j_eq : j = activeHeadIndex := by
      apply Fin.ext
      rfl
    have h_cast_eq : Fin.cast (representation.firstSupportedWidths_add h_support).symm j = prepHeadIndex := by
      apply Fin.ext
      rfl
    calc
      representation.liftedMatrix.entry i j = representation.liftedMatrix.entry i activeHeadIndex := by
        rw [h_j_eq]
      _ = representation.firstSupportedMass h_support head *
            (representation.firstSupportedCollapsedMatrix h_support).entry i 0 := by
              simpa [front, activeHeadIndex] using
                representation.liftedMatrix_entry_eq_firstSupportedMass_mul_collapsedHead h_support i head
      _ = (representation.firstSupportedPrependedMatrix h_support).entry i j := by
            rw [FinitePositiveMatrixRepresentation.firstSupportedPrependedMatrix,
              ConditionalProbabilityMatrix.cast_entry, h_cast_eq]
            symm
            simpa [front, tail, prepHeadIndex] using
              prependSourceMassMatrixPositiveWidth_head
                (representation.firstSupportedCollapsedMatrix h_support)
                (representation.firstSupportedMass h_support)
                (representation.firstSupportedMass_nonnegative h_support)
                (representation.firstSupportedBase_conditionalSupportWidth_pos h_support)
                i
                head
  · let tailIndex : Fin tail := ⟨j.1 - front, by
      have h_lt : j.1 < representation.activeLiftedWidth := j.2
      have h_sum : front + tail = representation.activeLiftedWidth := by
        simpa [front, tail] using representation.firstSupportedWidths_add h_support
      have h_lt' : j.1 < front + tail := by
        omega
      have h_ge : front ≤ j.1 := Nat.le_of_not_lt h_head
      omega⟩
    let activeTailIndex : Fin representation.activeLiftedWidth := ⟨front + tailIndex.1, by
      have h_sum : front + tail = representation.activeLiftedWidth := by
        simpa [front, tail] using representation.firstSupportedWidths_add h_support
      have h_bound : front + tailIndex.1 < front + tail :=
        Nat.add_lt_add_left tailIndex.2 front
      simpa [h_sum] using h_bound⟩
    let prepTailIndex : Fin (front + tail) := ⟨front + tailIndex.1, by
      exact Nat.add_lt_add_left tailIndex.2 front⟩
    have h_j_eq : j = activeTailIndex := by
      apply Fin.ext
      dsimp [activeTailIndex, tailIndex]
      omega
    have h_cast_eq : Fin.cast (representation.firstSupportedWidths_add h_support).symm j = prepTailIndex := by
      apply Fin.ext
      dsimp [prepTailIndex, tailIndex]
      omega
    calc
      representation.liftedMatrix.entry i j = representation.liftedMatrix.entry i activeTailIndex := by
        rw [h_j_eq]
      _ = (representation.firstSupportedCollapsedMatrix h_support).entry i tailIndex.succ := by
            simpa [front, tail, activeTailIndex, tailIndex] using
              representation.liftedMatrix_entry_eq_firstSupportedCollapsedMatrix_tail h_support i tailIndex
      _ = (representation.firstSupportedPrependedMatrix h_support).entry i j := by
            rw [FinitePositiveMatrixRepresentation.firstSupportedPrependedMatrix,
              ConditionalProbabilityMatrix.cast_entry, h_cast_eq]
            symm
            simpa [front, tail, prepTailIndex, tailIndex] using
              prependSourceMassMatrixPositiveWidth_tail
                (representation.firstSupportedCollapsedMatrix h_support)
                (representation.firstSupportedMass h_support)
                (representation.firstSupportedMass_nonnegative h_support)
                (representation.firstSupportedBase_conditionalSupportWidth_pos h_support)
                i
                tailIndex

theorem FinitePositiveMatrixRepresentation.firstSupportedCollapsedMatrix_reachable_to_liftedMatrix
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (h_support : 0 < supportedWidth M)
    (h_singular : matrix_is_singular M) :
    MatrixReachable (pps_ppm_vpm_step (k := k))
      ⟨representation.firstSupportedTailWidth h_support + 1,
        representation.firstSupportedCollapsedMatrix h_support⟩
      ⟨representation.activeLiftedWidth,
        representation.liftedMatrix⟩ := by
  have h_reach_prep :
      MatrixReachable (pps_ppm_vpm_step (k := k))
        ⟨representation.firstSupportedTailWidth h_support + 1,
          representation.firstSupportedCollapsedMatrix h_support⟩
        ⟨representation.activeLiftedWidth,
          representation.firstSupportedPrependedMatrix h_support⟩ := by
    have h_reach_raw :
        MatrixReachable (pps_ppm_vpm_step (k := k))
          ⟨representation.firstSupportedTailWidth h_support + 1,
            representation.firstSupportedCollapsedMatrix h_support⟩
          ⟨representation.conditionalSupportWidth (representation.firstSupportedBase h_support) +
              representation.firstSupportedTailWidth h_support,
            prependSourceMassMatrixPositiveWidth
              (representation.firstSupportedCollapsedMatrix h_support)
              (representation.firstSupportedMass h_support)
              (representation.firstSupportedMass_nonnegative h_support)
              (representation.firstSupportedBase_conditionalSupportWidth_pos h_support)⟩ := by
      exact matrix_reachable_to_prependSourceMassMatrixPositiveWidth_of_sum_one
        (representation.firstSupportedCollapsedMatrix h_support)
        (representation.firstSupportedCollapsedMatrix_is_singular h_support h_singular)
        (representation.firstSupportedMass h_support)
        (representation.firstSupportedMass_positive h_support)
        (representation.firstSupportedMass_sum_one h_support)
        (representation.firstSupportedBase_conditionalSupportWidth_pos h_support)
    have h_state_eq :
        (⟨representation.activeLiftedWidth,
          representation.firstSupportedPrependedMatrix h_support⟩ : MatrixState k) =
        ⟨representation.conditionalSupportWidth (representation.firstSupportedBase h_support) +
            representation.firstSupportedTailWidth h_support,
          prependSourceMassMatrixPositiveWidth
            (representation.firstSupportedCollapsedMatrix h_support)
            (representation.firstSupportedMass h_support)
            (representation.firstSupportedMass_nonnegative h_support)
            (representation.firstSupportedBase_conditionalSupportWidth_pos h_support)⟩ := by
      simpa [FinitePositiveMatrixRepresentation.firstSupportedPrependedMatrix] using
        (MatrixState.cast_eq
          (M := prependSourceMassMatrixPositiveWidth
            (representation.firstSupportedCollapsedMatrix h_support)
            (representation.firstSupportedMass h_support)
            (representation.firstSupportedMass_nonnegative h_support)
            (representation.firstSupportedBase_conditionalSupportWidth_pos h_support))
          (h := representation.firstSupportedWidths_add h_support))
    have h_reach_casted := h_reach_raw
    rw [← h_state_eq] at h_reach_casted
    exact h_reach_casted
  simpa [representation.liftedMatrix_eq_firstSupportedPrependedMatrix h_support] using h_reach_prep

noncomputable def FinitePositiveMatrixRepresentation.firstSupportedTailActiveIndex
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (h_support : 0 < supportedWidth M)
    (t : Fin (representation.firstSupportedTailWidth h_support)) :
    Fin representation.activeLiftedWidth :=
  ⟨representation.conditionalSupportWidth (representation.firstSupportedBase h_support) + t.1, by
    have h_sum := representation.firstSupportedWidths_add h_support
    have h_bound :
        representation.conditionalSupportWidth (representation.firstSupportedBase h_support) + t.1 <
          representation.conditionalSupportWidth (representation.firstSupportedBase h_support) +
            representation.firstSupportedTailWidth h_support := by
      exact Nat.add_lt_add_left t.2 _
    simpa [h_sum] using h_bound⟩

noncomputable def FinitePositiveMatrixRepresentation.firstSupportedTailBase
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (h_support : 0 < supportedWidth M)
    (t : Fin (representation.firstSupportedTailWidth h_support)) : Fin m :=
  (representation.activeLiftedOutput (representation.firstSupportedTailActiveIndex h_support t)).1

noncomputable def FinitePositiveMatrixRepresentation.firstSupportedTailWitness
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (h_support : 0 < supportedWidth M)
    (t : Fin (representation.firstSupportedTailWidth h_support)) : Fin representation.width :=
  (representation.activeLiftedOutput (representation.firstSupportedTailActiveIndex h_support t)).2

theorem FinitePositiveMatrixRepresentation.used_lifted_output_has_firstSupportedTailIndex
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (h_support : 0 < supportedWidth M)
    (yw : Fin m × Fin representation.width)
    (h_used : representation.liftedOutputUsed yw)
    (h_ne : yw.1 ≠ representation.firstSupportedBase h_support) :
    ∃ t : Fin (representation.firstSupportedTailWidth h_support),
      representation.activeLiftedOutput (representation.firstSupportedTailActiveIndex h_support t) = yw := by
  let front : Nat := representation.conditionalSupportWidth (representation.firstSupportedBase h_support)
  rcases representation.used_lifted_output_has_active_index yw h_used with ⟨jActive, h_jActive⟩
  have h_ge_front : front ≤ jActive.1 := by
    by_cases h_ge : front ≤ jActive.1
    · exact h_ge
    · have h_lt_front : jActive.1 < front := Nat.lt_of_not_ge h_ge
      let jFront : Fin front := ⟨jActive.1, h_lt_front⟩
      have h_active_eq_front :
          jActive = ⟨jFront.1, representation.firstSupportedBlockIndex_lt_activeLiftedWidth h_support jFront⟩ := by
        apply Fin.ext
        rfl
      have h_first_block :
          representation.activeLiftedOutput jActive =
            (representation.firstSupportedBase h_support,
              representation.conditionalSupportWitness (representation.firstSupportedBase h_support) jFront) := by
        rw [h_active_eq_front]
        simpa [front, jFront, FinitePositiveMatrixRepresentation.firstSupportedBase] using
          representation.activeLiftedOutput_eq_first_supported_block h_support jFront
      have h_base_eq : yw.1 = representation.firstSupportedBase h_support := by
        calc
          yw.1 = (representation.activeLiftedOutput jActive).1 := by
            simp [h_jActive]
          _ = representation.firstSupportedBase h_support := by
            simp [h_first_block]
      exact False.elim (h_ne h_base_eq)
  let t : Fin (representation.firstSupportedTailWidth h_support) := ⟨jActive.1 - front, by
    have h_lt_active : jActive.1 < representation.activeLiftedWidth := jActive.2
    have h_sum : front + representation.firstSupportedTailWidth h_support = representation.activeLiftedWidth := by
      simpa [front] using representation.firstSupportedWidths_add h_support
    omega⟩
  have h_tail_index_eq : representation.firstSupportedTailActiveIndex h_support t = jActive := by
    apply Fin.ext
    dsimp [FinitePositiveMatrixRepresentation.firstSupportedTailActiveIndex, t, front]
    omega
  refine ⟨t, ?_⟩
  rw [h_tail_index_eq]
  exact h_jActive

theorem FinitePositiveMatrixRepresentation.witness_has_firstSupportedTailIndex
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (h_support : 0 < supportedWidth M)
    (i : Fin k)
    (w : Fin representation.width)
    (h_ne : representation.decode i w ≠ representation.firstSupportedBase h_support) :
    ∃ t : Fin (representation.firstSupportedTailWidth h_support),
      representation.activeLiftedOutput (representation.firstSupportedTailActiveIndex h_support t) =
        (representation.decode i w, w) := by
  exact representation.used_lifted_output_has_firstSupportedTailIndex
    h_support
    (representation.decode i w, w)
    ⟨i, rfl⟩
    h_ne

noncomputable def FinitePositiveMatrixRepresentation.firstSupportedCollapsedOutput
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (h_support : 0 < supportedWidth M)
    (i : Fin k)
    (w : Fin representation.width) :
    Fin (representation.firstSupportedTailWidth h_support + 1) := by
  by_cases h_base : representation.decode i w = representation.firstSupportedBase h_support
  · exact 0
  · exact (Classical.choose (representation.witness_has_firstSupportedTailIndex h_support i w h_base)).succ

theorem FinitePositiveMatrixRepresentation.firstSupportedCollapsedOutput_of_eq_base
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (h_support : 0 < supportedWidth M)
    (i : Fin k)
    (w : Fin representation.width)
    (h_base : representation.decode i w = representation.firstSupportedBase h_support) :
    representation.firstSupportedCollapsedOutput h_support i w = 0 := by
  simp [FinitePositiveMatrixRepresentation.firstSupportedCollapsedOutput, h_base]

theorem FinitePositiveMatrixRepresentation.firstSupportedCollapsedOutput_of_ne_base
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (h_support : 0 < supportedWidth M)
    (i : Fin k)
    (w : Fin representation.width)
    (h_ne : representation.decode i w ≠ representation.firstSupportedBase h_support) :
    representation.firstSupportedCollapsedOutput h_support i w =
      (Classical.choose (representation.witness_has_firstSupportedTailIndex h_support i w h_ne)).succ := by
  simp [FinitePositiveMatrixRepresentation.firstSupportedCollapsedOutput, h_ne]

theorem FinitePositiveMatrixRepresentation.firstSupportedCollapsedOutput_ne_zero_of_ne_base
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (h_support : 0 < supportedWidth M)
    (i : Fin k)
    (w : Fin representation.width)
    (h_ne : representation.decode i w ≠ representation.firstSupportedBase h_support) :
    representation.firstSupportedCollapsedOutput h_support i w ≠ 0 := by
  rw [representation.firstSupportedCollapsedOutput_of_ne_base h_support i w h_ne]
  intro h_zero
  cases h_zero

theorem FinitePositiveMatrixRepresentation.firstSupportedCollapsedOutput_eq_zero_iff
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (h_support : 0 < supportedWidth M)
    (i : Fin k)
    (w : Fin representation.width) :
    representation.firstSupportedCollapsedOutput h_support i w = 0 ↔
      representation.decode i w = representation.firstSupportedBase h_support := by
  constructor
  · intro h_zero
    by_cases h_base : representation.decode i w = representation.firstSupportedBase h_support
    · exact h_base
    · exact False.elim ((representation.firstSupportedCollapsedOutput_ne_zero_of_ne_base
        h_support i w h_base) h_zero)
  · intro h_base
    exact representation.firstSupportedCollapsedOutput_of_eq_base h_support i w h_base

theorem FinitePositiveMatrixRepresentation.firstSupportedCollapsedOutput_tail_spec
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (h_support : 0 < supportedWidth M)
    (i : Fin k)
    (w : Fin representation.width)
    (h_ne : representation.decode i w ≠ representation.firstSupportedBase h_support) :
    let t := Classical.choose (representation.witness_has_firstSupportedTailIndex h_support i w h_ne)
    representation.activeLiftedOutput (representation.firstSupportedTailActiveIndex h_support t) =
      (representation.decode i w, w) := by
  simpa using Classical.choose_spec
    (representation.witness_has_firstSupportedTailIndex h_support i w h_ne)

theorem FinitePositiveMatrixRepresentation.firstSupportedTailBase_eq_decode_of_ne_base
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (h_support : 0 < supportedWidth M)
    (i : Fin k)
    (w : Fin representation.width)
    (h_ne : representation.decode i w ≠ representation.firstSupportedBase h_support) :
    let t := Classical.choose (representation.witness_has_firstSupportedTailIndex h_support i w h_ne)
    representation.firstSupportedTailBase h_support t = representation.decode i w := by
  simp [FinitePositiveMatrixRepresentation.firstSupportedTailBase,
    representation.firstSupportedCollapsedOutput_tail_spec h_support i w h_ne]

theorem FinitePositiveMatrixRepresentation.firstSupportedTailWitness_eq_of_ne_base
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (h_support : 0 < supportedWidth M)
    (i : Fin k)
    (w : Fin representation.width)
    (h_ne : representation.decode i w ≠ representation.firstSupportedBase h_support) :
    let t := Classical.choose (representation.witness_has_firstSupportedTailIndex h_support i w h_ne)
    representation.firstSupportedTailWitness h_support t = w := by
  simp [FinitePositiveMatrixRepresentation.firstSupportedTailWitness,
    representation.firstSupportedCollapsedOutput_tail_spec h_support i w h_ne]

theorem FinitePositiveMatrixRepresentation.firstSupportedTailBase_ne_firstSupportedBase
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (h_support : 0 < supportedWidth M)
    (t : Fin (representation.firstSupportedTailWidth h_support)) :
    representation.firstSupportedTailBase h_support t ≠ representation.firstSupportedBase h_support := by
  intro h_eq
  let tailIdx := representation.firstSupportedTailActiveIndex h_support t
  let tailBase : Fin m := (representation.activeLiftedOutput tailIdx).1
  rcases representation.activeLiftedOutput_has_conditionalSupportWitness tailIdx with ⟨jFront, h_witness⟩
  have h_eq_base : tailBase = representation.firstSupportedBase h_support := by
    simpa [tailBase, FinitePositiveMatrixRepresentation.firstSupportedTailBase, tailIdx] using h_eq
  let j : Fin (representation.conditionalSupportWidth (representation.firstSupportedBase h_support)) :=
    Fin.cast (congrArg representation.conditionalSupportWidth h_eq_base) jFront
  have hj :
      representation.conditionalSupportWitness (representation.firstSupportedBase h_support) j =
        representation.firstSupportedTailWitness h_support t := by
    calc
      representation.conditionalSupportWitness (representation.firstSupportedBase h_support) j =
          representation.conditionalSupportWitness tailBase jFront := by
            simpa [j] using
              FinitePositiveMatrixRepresentation.conditionalSupportWitness_cast
                representation h_eq_base jFront
      _ = representation.firstSupportedTailWitness h_support t := by
            simpa [tailBase, FinitePositiveMatrixRepresentation.firstSupportedTailWitness, tailIdx] using h_witness
  let frontIdx : Fin representation.activeLiftedWidth :=
    ⟨j.1, representation.firstSupportedBlockIndex_lt_activeLiftedWidth h_support j⟩
  have h_front_eq :
      representation.activeLiftedOutput frontIdx =
        (representation.firstSupportedBase h_support,
          representation.firstSupportedTailWitness h_support t) := by
    calc
      representation.activeLiftedOutput frontIdx =
          (representation.firstSupportedBase h_support,
            representation.conditionalSupportWitness (representation.firstSupportedBase h_support) j) := by
              simpa [frontIdx, FinitePositiveMatrixRepresentation.firstSupportedBase] using
                representation.activeLiftedOutput_eq_first_supported_block h_support j
      _ = (representation.firstSupportedBase h_support,
            representation.firstSupportedTailWitness h_support t) := by
              simp [hj]
  have h_tail_eq :
      representation.activeLiftedOutput tailIdx =
        (representation.firstSupportedBase h_support,
          representation.firstSupportedTailWitness h_support t) := by
    apply Prod.ext
    · exact h_eq_base
    · rfl
  have h_indices : frontIdx = tailIdx := by
    apply representation.activeLiftedOutput_injective
    calc
      representation.activeLiftedOutput frontIdx =
          (representation.firstSupportedBase h_support,
            representation.firstSupportedTailWitness h_support t) := h_front_eq
      _ = representation.activeLiftedOutput tailIdx := h_tail_eq.symm
  have h_front_lt : frontIdx.1 < representation.conditionalSupportWidth (representation.firstSupportedBase h_support) := j.2
  have h_tail_ge :
      representation.conditionalSupportWidth (representation.firstSupportedBase h_support) ≤ tailIdx.1 := by
    dsimp [tailIdx, FinitePositiveMatrixRepresentation.firstSupportedTailActiveIndex]
    exact Nat.le_add_right _ _
  have h_val_eq : frontIdx.1 = tailIdx.1 := by
    simpa [frontIdx, tailIdx] using congrArg Fin.val h_indices
  have h_contra : frontIdx.1 < frontIdx.1 := by
    calc
      frontIdx.1 < representation.conditionalSupportWidth (representation.firstSupportedBase h_support) := h_front_lt
      _ ≤ tailIdx.1 := h_tail_ge
      _ = frontIdx.1 := h_val_eq.symm
  exact Nat.lt_irrefl _ h_contra

noncomputable def FinitePositiveMatrixRepresentation.firstSupportedCollapsedConditionalWeight
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (h_support : 0 < supportedWidth M) :
    Fin (representation.firstSupportedTailWidth h_support + 1) → Fin representation.width → Probability :=
  fun y w =>
    if h_zero : y.1 = 0 then
      representation.pW_given_Y (representation.firstSupportedBase h_support) w
    else
      let t : Fin (representation.firstSupportedTailWidth h_support) := ⟨y.1 - 1, by
        have h_pos : 0 < y.1 := Nat.pos_of_ne_zero h_zero
        have h_lt : y.1 < representation.firstSupportedTailWidth h_support + 1 := y.2
        omega⟩
      if w = representation.firstSupportedTailWitness h_support t then 1 else 0

theorem FinitePositiveMatrixRepresentation.firstSupportedCollapsedConditionalWeight_head
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (h_support : 0 < supportedWidth M)
    (w : Fin representation.width) :
    representation.firstSupportedCollapsedConditionalWeight h_support 0 w =
      representation.pW_given_Y (representation.firstSupportedBase h_support) w := by
  simp [FinitePositiveMatrixRepresentation.firstSupportedCollapsedConditionalWeight]

theorem FinitePositiveMatrixRepresentation.firstSupportedCollapsedConditionalWeight_tail
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (h_support : 0 < supportedWidth M)
    (t : Fin (representation.firstSupportedTailWidth h_support))
    (w : Fin representation.width) :
    representation.firstSupportedCollapsedConditionalWeight h_support t.succ w =
      (if w = representation.firstSupportedTailWitness h_support t then 1 else 0) := by
  simp [FinitePositiveMatrixRepresentation.firstSupportedCollapsedConditionalWeight,
    FinitePositiveMatrixRepresentation.firstSupportedTailWitness]

theorem FinitePositiveMatrixRepresentation.firstSupportedCollapsedConditionalWeight_head_sum_one
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (h_support : 0 < supportedWidth M) :
    discrete_sum (representation.firstSupportedCollapsedConditionalWeight h_support 0) = 1 := by
  simpa [FinitePositiveMatrixRepresentation.firstSupportedCollapsedConditionalWeight] using
    representation.conditional_normalized (representation.firstSupportedBase h_support)

theorem FinitePositiveMatrixRepresentation.firstSupportedCollapsedConditionalWeight_tail_sum_one
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (h_support : 0 < supportedWidth M)
    (t : Fin (representation.firstSupportedTailWidth h_support)) :
    discrete_sum (representation.firstSupportedCollapsedConditionalWeight h_support t.succ) = 1 := by
  calc
    discrete_sum (representation.firstSupportedCollapsedConditionalWeight h_support t.succ) =
        discrete_sum (fun w : Fin representation.width =>
          if w = representation.firstSupportedTailWitness h_support t then 1 else 0) := by
            apply InfoTheory.discrete_sum_congr
            intro w
            exact representation.firstSupportedCollapsedConditionalWeight_tail h_support t w
    _ = 1 := discrete_sum_singleton_indicator (representation.firstSupportedTailWitness h_support t)

theorem FinitePositiveMatrixRepresentation.firstSupportedCollapsedOutput_eq_tail_iff
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (h_support : 0 < supportedWidth M)
    (i : Fin k)
    (w : Fin representation.width)
    (t : Fin (representation.firstSupportedTailWidth h_support)) :
    representation.firstSupportedCollapsedOutput h_support i w = t.succ ↔
      representation.decode i w = representation.firstSupportedTailBase h_support t ∧
        w = representation.firstSupportedTailWitness h_support t := by
  constructor
  · intro h_out
    have h_ne : representation.decode i w ≠ representation.firstSupportedBase h_support := by
      intro h_base
      rw [representation.firstSupportedCollapsedOutput_of_eq_base h_support i w h_base] at h_out
      cases h_out
    let t' := Classical.choose (representation.witness_has_firstSupportedTailIndex h_support i w h_ne)
    have h_out' : t'.succ = t.succ := by
      rw [← representation.firstSupportedCollapsedOutput_of_ne_base h_support i w h_ne]
      exact h_out
    have h_t' : t' = t := by
      apply Fin.ext
      have h_val : t'.1 + 1 = t.1 + 1 := by
        simpa [t'] using congrArg Fin.val h_out'
      omega
    have h_spec :
        representation.activeLiftedOutput (representation.firstSupportedTailActiveIndex h_support t) =
          (representation.decode i w, w) := by
      simpa [t', h_t'] using representation.firstSupportedCollapsedOutput_tail_spec h_support i w h_ne
    constructor
    · simpa [FinitePositiveMatrixRepresentation.firstSupportedTailBase] using congrArg Prod.fst h_spec.symm
    · simpa [FinitePositiveMatrixRepresentation.firstSupportedTailWitness] using congrArg Prod.snd h_spec.symm
  · rintro ⟨h_decode, h_witness⟩
    have h_ne : representation.decode i w ≠ representation.firstSupportedBase h_support := by
      intro h_base
      exact (representation.firstSupportedTailBase_ne_firstSupportedBase h_support t)
        (h_decode.symm.trans h_base)
    let t' := Classical.choose (representation.witness_has_firstSupportedTailIndex h_support i w h_ne)
    have h_spec' :
        representation.activeLiftedOutput (representation.firstSupportedTailActiveIndex h_support t') =
          (representation.firstSupportedTailBase h_support t,
            representation.firstSupportedTailWitness h_support t) := by
      calc
        representation.activeLiftedOutput (representation.firstSupportedTailActiveIndex h_support t') =
            (representation.decode i w, w) := by
              simpa [t'] using representation.firstSupportedCollapsedOutput_tail_spec h_support i w h_ne
        _ = (representation.firstSupportedTailBase h_support t,
              representation.firstSupportedTailWitness h_support t) := by
              cases h_witness
              exact Prod.ext h_decode rfl
    have h_tail_self :
        representation.activeLiftedOutput (representation.firstSupportedTailActiveIndex h_support t) =
          (representation.firstSupportedTailBase h_support t,
            representation.firstSupportedTailWitness h_support t) := by
      rfl
    have h_active_eq :
        representation.firstSupportedTailActiveIndex h_support t' =
          representation.firstSupportedTailActiveIndex h_support t := by
      apply representation.activeLiftedOutput_injective
      calc
        representation.activeLiftedOutput (representation.firstSupportedTailActiveIndex h_support t') =
            (representation.firstSupportedTailBase h_support t,
              representation.firstSupportedTailWitness h_support t) := h_spec'
        _ = representation.activeLiftedOutput (representation.firstSupportedTailActiveIndex h_support t) := h_tail_self.symm
    have h_t' : t' = t := by
      apply Fin.ext
      have h_val :
          (representation.firstSupportedTailActiveIndex h_support t').1 =
            (representation.firstSupportedTailActiveIndex h_support t).1 := by
        simpa using congrArg Fin.val h_active_eq
      dsimp [FinitePositiveMatrixRepresentation.firstSupportedTailActiveIndex] at h_val
      omega
    calc
      representation.firstSupportedCollapsedOutput h_support i w = t'.succ := by
        exact representation.firstSupportedCollapsedOutput_of_ne_base h_support i w h_ne
      _ = t.succ := by
        simpa [t'] using congrArg Fin.succ h_t'

theorem FinitePositiveMatrixRepresentation.firstSupportedCollapsedFactorization_head
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (h_support : 0 < supportedWidth M)
    (i : Fin k)
    (w : Fin representation.width) :
    (if representation.firstSupportedCollapsedOutput h_support i w = 0 then representation.pW w else 0) =
      representation.firstSupportedCollapsedConditionalWeight h_support 0 w *
        (representation.firstSupportedCollapsedMatrix h_support).entry i 0 := by
  simp [representation.firstSupportedCollapsedOutput_eq_zero_iff h_support i w,
    representation.firstSupportedCollapsedConditionalWeight_head h_support w,
    representation.firstSupportedCollapsedMatrix_head h_support i]
  simpa [FinitePositiveMatrixRepresentation.firstSupportedBase] using
    representation.conditional_factorization i (representation.firstSupportedBase h_support) w

theorem FinitePositiveMatrixRepresentation.firstSupportedCollapsedFactorization_tail
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (h_support : 0 < supportedWidth M)
    (t : Fin (representation.firstSupportedTailWidth h_support))
    (i : Fin k)
    (w : Fin representation.width) :
    (if representation.firstSupportedCollapsedOutput h_support i w = t.succ then representation.pW w else 0) =
      representation.firstSupportedCollapsedConditionalWeight h_support t.succ w *
        (representation.firstSupportedCollapsedMatrix h_support).entry i t.succ := by
  let tailIdx := representation.firstSupportedTailActiveIndex h_support t
  have h_lifted :
      representation.liftedMatrix.entry i tailIdx =
        representation.pW_given_Y (representation.firstSupportedTailBase h_support t)
          (representation.firstSupportedTailWitness h_support t) *
            M.entry i (representation.firstSupportedTailBase h_support t) := by
    simpa [FinitePositiveMatrixRepresentation.firstSupportedTailBase,
      FinitePositiveMatrixRepresentation.firstSupportedTailWitness, tailIdx] using
      representation.liftedMatrix_entry_eq_conditional_weight i tailIdx
  by_cases h_w : w = representation.firstSupportedTailWitness h_support t
  · subst h_w
    calc
      (if representation.firstSupportedCollapsedOutput h_support i
            (representation.firstSupportedTailWitness h_support t) = t.succ then
          representation.pW (representation.firstSupportedTailWitness h_support t)
        else 0) =
          (if representation.decode i (representation.firstSupportedTailWitness h_support t) =
                representation.firstSupportedTailBase h_support t then
              representation.pW (representation.firstSupportedTailWitness h_support t)
            else 0) := by
              simp [representation.firstSupportedCollapsedOutput_eq_tail_iff h_support i
                (representation.firstSupportedTailWitness h_support t) t]
      _ = representation.pW_given_Y (representation.firstSupportedTailBase h_support t)
            (representation.firstSupportedTailWitness h_support t) *
              M.entry i (representation.firstSupportedTailBase h_support t) := by
            simpa [FinitePositiveMatrixRepresentation.firstSupportedTailBase,
              FinitePositiveMatrixRepresentation.firstSupportedTailWitness, tailIdx] using
              representation.conditional_factorization i
                (representation.firstSupportedTailBase h_support t)
                (representation.firstSupportedTailWitness h_support t)
      _ = representation.liftedMatrix.entry i tailIdx := by rw [h_lifted]
      _ = (representation.firstSupportedCollapsedMatrix h_support).entry i t.succ := by
            symm
            exact representation.firstSupportedCollapsedMatrix_tail h_support i t
      _ = representation.firstSupportedCollapsedConditionalWeight h_support t.succ
            (representation.firstSupportedTailWitness h_support t) *
              (representation.firstSupportedCollapsedMatrix h_support).entry i t.succ := by
            rw [representation.firstSupportedCollapsedConditionalWeight_tail h_support t]
            simp
  · have h_out_ne : representation.firstSupportedCollapsedOutput h_support i w ≠ t.succ := by
      intro h_out
      exact h_w ((representation.firstSupportedCollapsedOutput_eq_tail_iff h_support i w t).mp h_out).2
    simp [h_out_ne, representation.firstSupportedCollapsedConditionalWeight_tail h_support t, h_w]

theorem FinitePositiveMatrixRepresentation.firstSupportedCollapsedConditionalWeight_sum_one
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (h_support : 0 < supportedWidth M)
    (y : Fin (representation.firstSupportedTailWidth h_support + 1)) :
    discrete_sum (representation.firstSupportedCollapsedConditionalWeight h_support y) = 1 := by
  by_cases h_zero : y.1 = 0
  · have hy : y = 0 := by
      apply Fin.ext
      exact h_zero
    simpa [hy] using representation.firstSupportedCollapsedConditionalWeight_head_sum_one h_support
  · let t : Fin (representation.firstSupportedTailWidth h_support) := ⟨y.1 - 1, by
      have h_pos : 0 < y.1 := Nat.pos_of_ne_zero h_zero
      have h_lt : y.1 < representation.firstSupportedTailWidth h_support + 1 := y.2
      omega⟩
    have hy : y = t.succ := by
      apply Fin.ext
      dsimp [t]
      omega
    simpa [hy] using representation.firstSupportedCollapsedConditionalWeight_tail_sum_one h_support t

theorem FinitePositiveMatrixRepresentation.firstSupportedCollapsedFactorization
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (h_support : 0 < supportedWidth M)
    (i : Fin k)
    (y : Fin (representation.firstSupportedTailWidth h_support + 1))
    (w : Fin representation.width) :
    (if representation.firstSupportedCollapsedOutput h_support i w = y then representation.pW w else 0) =
      representation.firstSupportedCollapsedConditionalWeight h_support y w *
        (representation.firstSupportedCollapsedMatrix h_support).entry i y := by
  by_cases h_zero : y.1 = 0
  · have hy : y = 0 := by
      apply Fin.ext
      exact h_zero
    simpa [hy] using representation.firstSupportedCollapsedFactorization_head h_support i w
  · let t : Fin (representation.firstSupportedTailWidth h_support) := ⟨y.1 - 1, by
      have h_pos : 0 < y.1 := Nat.pos_of_ne_zero h_zero
      have h_lt : y.1 < representation.firstSupportedTailWidth h_support + 1 := y.2
      omega⟩
    have hy : y = t.succ := by
      apply Fin.ext
      dsimp [t]
      omega
    simpa [hy] using representation.firstSupportedCollapsedFactorization_tail h_support t i w

noncomputable def FinitePositiveMatrixRepresentation.firstSupportedCollapsedRepresentation
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (h_support : 0 < supportedWidth M) :
    FinitePositiveMatrixRepresentation (representation.firstSupportedCollapsedMatrix h_support) :=
  { width := representation.width
    pW := representation.pW
    decode := representation.firstSupportedCollapsedOutput h_support
    positive := representation.positive
    normalized := representation.normalized
    pW_given_Y := representation.firstSupportedCollapsedConditionalWeight h_support
    conditional_normalized := representation.firstSupportedCollapsedConditionalWeight_sum_one h_support
    conditional_factorization := representation.firstSupportedCollapsedFactorization h_support }

theorem FinitePositiveMatrixRepresentation.firstSupportedCollapsedRepresentation_liftedOutputUsed_head_iff
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (h_support : 0 < supportedWidth M)
    (w : Fin representation.width) :
    (representation.firstSupportedCollapsedRepresentation h_support).liftedOutputUsed (0, w) ↔
      representation.liftedOutputUsed (representation.firstSupportedBase h_support, w) := by
  constructor
  · intro h_used
    rcases h_used with ⟨i, h_decode⟩
    exact ⟨i, (representation.firstSupportedCollapsedOutput_eq_zero_iff h_support i w).mp h_decode⟩
  · intro h_used
    rcases h_used with ⟨i, h_decode⟩
    exact ⟨i, (representation.firstSupportedCollapsedOutput_eq_zero_iff h_support i w).mpr h_decode⟩

theorem FinitePositiveMatrixRepresentation.firstSupportedCollapsedRepresentation_conditionalSupportWitnesses_head
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (h_support : 0 < supportedWidth M) :
    (representation.firstSupportedCollapsedRepresentation h_support).conditionalSupportWitnesses 0 =
      representation.conditionalSupportWitnesses (representation.firstSupportedBase h_support) := by
  classical
  let base := representation.firstSupportedBase h_support
  have h_pred :
      (fun w : Fin representation.width =>
        decide ((representation.firstSupportedCollapsedRepresentation h_support).liftedOutputUsed (0, w))) =
      (fun w : Fin representation.width => decide (representation.liftedOutputUsed (base, w))) := by
    funext w
    by_cases h_used : (representation.firstSupportedCollapsedRepresentation h_support).liftedOutputUsed (0, w)
    · have h_used' : representation.liftedOutputUsed (base, w) :=
        (representation.firstSupportedCollapsedRepresentation_liftedOutputUsed_head_iff h_support w).mp h_used
      simp [h_used, h_used']
    · have h_used' : ¬ representation.liftedOutputUsed (base, w) := by
        intro h_orig
        exact h_used
          ((representation.firstSupportedCollapsedRepresentation_liftedOutputUsed_head_iff h_support w).mpr h_orig)
      simp [h_used, h_used']
  unfold FinitePositiveMatrixRepresentation.conditionalSupportWitnesses
  change List.filter
      (fun w : Fin representation.width =>
        decide ((representation.firstSupportedCollapsedRepresentation h_support).liftedOutputUsed (0, w)))
      (List.finRange representation.width) =
    List.filter (fun w : Fin representation.width => decide (representation.liftedOutputUsed (base, w)))
      (List.finRange representation.width)
  rw [h_pred]

theorem List.finRange_filter_eq_singleton {n : Nat} (w₀ : Fin n) :
    List.filter (fun w : Fin n => decide (w = w₀)) (List.finRange n) = [w₀] := by
  have h_ofFn_succ_eq_map_finRange :
      ∀ n : Nat,
        List.ofFn (fun i : Fin n => i.succ) = (List.finRange n).map Fin.succ := by
    intro n
    apply List.ext_get
    · simp [List.finRange, List.length_ofFn]
    · intro k hk_left hk_right
      have hk_range : k < (List.finRange n).length := by
        simpa [List.length_map] using hk_right
      have h_get_range :
          (List.finRange n).get ⟨k, hk_range⟩ =
            (⟨k, by simpa [List.finRange, List.length_ofFn] using hk_range⟩ : Fin n) := by
        change (List.ofFn (fun i : Fin n => i)).get ⟨k, hk_range⟩ =
          (⟨k, by simpa [List.finRange, List.length_ofFn] using hk_range⟩ : Fin n)
        exact List.getElem_ofFn (f := fun i : Fin n => i) hk_range
      have h_get_map :
          ((List.finRange n).map Fin.succ).get ⟨k, hk_right⟩ =
            Fin.succ ((List.finRange n).get ⟨k, hk_range⟩) := by
        change ((List.finRange n).map Fin.succ)[k] = Fin.succ ((List.finRange n)[k]'hk_range)
        exact List.getElem_map (l := List.finRange n) (f := Fin.succ) (i := k) (h := hk_right)
      calc
        (List.ofFn (fun i : Fin n => i.succ)).get ⟨k, hk_left⟩ =
            (⟨k, by simpa [List.length_ofFn] using hk_left⟩ : Fin n).succ := by
              exact List.getElem_ofFn (f := fun i : Fin n => i.succ) hk_left
        _ = Fin.succ ((List.finRange n).get ⟨k, hk_range⟩) := by
              rw [h_get_range]
        _ = ((List.finRange n).map Fin.succ).get ⟨k, hk_right⟩ := by
              exact h_get_map.symm
  induction n with
  | zero =>
      cases w₀.2
  | succ n ih =>
      cases w₀ using Fin.cases with
      | zero =>
          have h_comp_zero :
              ((fun w : Fin (n + 1) => decide (w = 0)) ∘ Fin.succ) = fun _ : Fin n => false := by
            funext a
            have h_ne : a.succ ≠ (0 : Fin (n + 1)) := by
              intro h
              cases h
            simp [Function.comp, h_ne]
          rw [List.finRange, List.ofFn_succ, List.filter_cons_of_pos]
          · rw [h_ofFn_succ_eq_map_finRange n, List.filter_map, h_comp_zero]
            simp
          · simp
      | succ w =>
          have h_comp_succ :
              ((fun w' : Fin (n + 1) => decide (w' = w.succ)) ∘ Fin.succ) =
                fun a : Fin n => decide (a = w) := by
            funext a
            by_cases h_eq : a = w
            · simp [Function.comp, h_eq]
            · have h_ne : a.succ ≠ w.succ := by
                intro h
                apply h_eq
                apply Fin.ext
                simpa using congrArg Fin.val h
              simp [Function.comp, h_eq, h_ne]
          rw [List.finRange, List.ofFn_succ, List.filter_cons_of_neg]
          · rw [h_ofFn_succ_eq_map_finRange n, List.filter_map, h_comp_succ]
            simpa using congrArg (List.map Fin.succ) (ih w)
          · intro h
            cases h

theorem FinitePositiveMatrixRepresentation.firstSupportedCollapsedRepresentation_liftedOutputUsed_tail_iff
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (h_support : 0 < supportedWidth M)
    (t : Fin (representation.firstSupportedTailWidth h_support))
    (w : Fin representation.width) :
    (representation.firstSupportedCollapsedRepresentation h_support).liftedOutputUsed (t.succ, w) ↔
      w = representation.firstSupportedTailWitness h_support t := by
  constructor
  · intro h_used
    rcases h_used with ⟨i, h_decode⟩
    exact (representation.firstSupportedCollapsedOutput_eq_tail_iff h_support i w t).mp h_decode |>.2
  · intro h_w
    let tailIdx := representation.firstSupportedTailActiveIndex h_support t
    rcases representation.activeLiftedOutput_used tailIdx with ⟨i, h_decode⟩
    refine ⟨i, ?_⟩
    exact (representation.firstSupportedCollapsedOutput_eq_tail_iff h_support i w t).mpr
      ⟨by simpa [h_w, FinitePositiveMatrixRepresentation.firstSupportedTailBase,
          FinitePositiveMatrixRepresentation.firstSupportedTailWitness, tailIdx] using h_decode,
        h_w⟩

theorem FinitePositiveMatrixRepresentation.firstSupportedCollapsedRepresentation_conditionalSupportWitnesses_tail
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (h_support : 0 < supportedWidth M)
    (t : Fin (representation.firstSupportedTailWidth h_support)) :
    (representation.firstSupportedCollapsedRepresentation h_support).conditionalSupportWitnesses t.succ =
      [representation.firstSupportedTailWitness h_support t] := by
  classical
  have h_pred :
      (fun w : Fin representation.width =>
        decide ((representation.firstSupportedCollapsedRepresentation h_support).liftedOutputUsed (t.succ, w))) =
      (fun w : Fin representation.width => decide (w = representation.firstSupportedTailWitness h_support t)) := by
    funext w
    by_cases h_eq : w = representation.firstSupportedTailWitness h_support t
    · have h_used : (representation.firstSupportedCollapsedRepresentation h_support).liftedOutputUsed (t.succ, w) :=
        (representation.firstSupportedCollapsedRepresentation_liftedOutputUsed_tail_iff h_support t w).mpr h_eq
      rw [show decide ((representation.firstSupportedCollapsedRepresentation h_support).liftedOutputUsed (t.succ, w)) = true by
            simp [h_used]]
      rw [show decide (w = representation.firstSupportedTailWitness h_support t) = true by
            simp [h_eq]]
    · have h_used : ¬ (representation.firstSupportedCollapsedRepresentation h_support).liftedOutputUsed (t.succ, w) := by
        intro h_used
        exact h_eq
          ((representation.firstSupportedCollapsedRepresentation_liftedOutputUsed_tail_iff h_support t w).mp h_used)
      have h_used' : w ≠ representation.firstSupportedTailWitness h_support t := by
        intro h_eq
        exact h_used
          ((representation.firstSupportedCollapsedRepresentation_liftedOutputUsed_tail_iff h_support t w).mpr h_eq)
      rw [show decide ((representation.firstSupportedCollapsedRepresentation h_support).liftedOutputUsed (t.succ, w)) = false by
            simp [h_used]]
      rw [show decide (w = representation.firstSupportedTailWitness h_support t) = false by
            simp [h_eq]]
  unfold FinitePositiveMatrixRepresentation.conditionalSupportWitnesses
  change List.filter
      (fun w : Fin representation.width =>
        decide ((representation.firstSupportedCollapsedRepresentation h_support).liftedOutputUsed (t.succ, w)))
      (List.finRange representation.width) = [representation.firstSupportedTailWitness h_support t]
  rw [h_pred]
  exact List.finRange_filter_eq_singleton (representation.firstSupportedTailWitness h_support t)

theorem FinitePositiveMatrixRepresentation.firstSupportedCollapsedRepresentation_activeLiftedOutputs
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (h_support : 0 < supportedWidth M) :
    (representation.firstSupportedCollapsedRepresentation h_support).activeLiftedOutputs =
      (representation.conditionalSupportWitnesses (representation.firstSupportedBase h_support)).map (Prod.mk 0) ++
        List.map
          (fun t : Fin (representation.firstSupportedTailWidth h_support) =>
            (t.succ, representation.firstSupportedTailWitness h_support t))
          (List.finRange (representation.firstSupportedTailWidth h_support)) := by
  classical
  let collapsed := representation.firstSupportedCollapsedRepresentation h_support
  let tailWidth := representation.firstSupportedTailWidth h_support
  let base := representation.firstSupportedBase h_support
  calc
    collapsed.activeLiftedOutputs =
        (List.map (fun y => (collapsed.conditionalSupportWitnesses y).map (Prod.mk y))
          (List.finRange (tailWidth + 1))).flatten := by
            simpa [collapsed, tailWidth] using collapsed.activeLiftedOutputs_eq_blocks
    _ = (collapsed.conditionalSupportWitnesses 0).map (Prod.mk 0) ++
          (List.map
            (fun t : Fin tailWidth =>
              (collapsed.conditionalSupportWitnesses t.succ).map (Prod.mk t.succ))
            (List.finRange tailWidth)).flatten := by
              rw [List.finRange, List.ofFn_succ, List.ofFn_succ_eq_map_finRange]
              simp
              apply congrArg List.flatten
              apply congrArg (fun f => List.map f (List.finRange tailWidth))
              funext t
              rfl
    _ = (collapsed.conditionalSupportWitnesses 0).map (Prod.mk 0) ++
          (List.map
            (fun t : Fin tailWidth =>
              [(t.succ, representation.firstSupportedTailWitness h_support t)])
            (List.finRange tailWidth)).flatten := by
              have h_tail_blocks :
                  (List.map
                    (fun t : Fin tailWidth =>
                      (collapsed.conditionalSupportWitnesses t.succ).map (Prod.mk t.succ))
                    (List.finRange tailWidth)).flatten =
                    (List.map
                      (fun t : Fin tailWidth =>
                        [(t.succ, representation.firstSupportedTailWitness h_support t)])
                      (List.finRange tailWidth)).flatten := by
                    apply congrArg List.flatten
                    apply congrArg (fun f => List.map f (List.finRange tailWidth))
                    funext t
                    rw [representation.firstSupportedCollapsedRepresentation_conditionalSupportWitnesses_tail h_support]
                    rfl
              exact congrArg
                (fun xs => (collapsed.conditionalSupportWitnesses 0).map (Prod.mk 0) ++ xs)
                h_tail_blocks
    _ = (representation.conditionalSupportWitnesses base).map (Prod.mk 0) ++
          (List.map
            (fun t : Fin tailWidth =>
              [(t.succ, representation.firstSupportedTailWitness h_support t)])
            (List.finRange tailWidth)).flatten := by
              rw [representation.firstSupportedCollapsedRepresentation_conditionalSupportWitnesses_head h_support]
              rfl
    _ = (representation.conditionalSupportWitnesses base).map (Prod.mk 0) ++
          List.map
            (fun t : Fin tailWidth =>
              (t.succ, representation.firstSupportedTailWitness h_support t))
            (List.finRange tailWidth) := by
              simp [List.flatten_map_singleton]

theorem FinitePositiveMatrixRepresentation.firstSupportedCollapsedRepresentation_activeLiftedWidth
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (h_support : 0 < supportedWidth M) :
    (representation.firstSupportedCollapsedRepresentation h_support).activeLiftedWidth =
      representation.activeLiftedWidth := by
  calc
    (representation.firstSupportedCollapsedRepresentation h_support).activeLiftedWidth =
        representation.conditionalSupportWidth (representation.firstSupportedBase h_support) +
          representation.firstSupportedTailWidth h_support := by
            rw [FinitePositiveMatrixRepresentation.activeLiftedWidth,
              representation.firstSupportedCollapsedRepresentation_activeLiftedOutputs h_support]
            calc
              (List.map (Prod.mk 0)
                  (representation.conditionalSupportWitnesses (representation.firstSupportedBase h_support)) ++
                    List.map
                      (fun t : Fin (representation.firstSupportedTailWidth h_support) =>
                        (t.succ, representation.firstSupportedTailWitness h_support t))
                      (List.finRange (representation.firstSupportedTailWidth h_support))).length =
                  (representation.conditionalSupportWitnesses (representation.firstSupportedBase h_support)).length +
                    (List.finRange (representation.firstSupportedTailWidth h_support)).length := by
                      simp
              _ = representation.conditionalSupportWidth (representation.firstSupportedBase h_support) +
                    representation.firstSupportedTailWidth h_support := by
                      simp [FinitePositiveMatrixRepresentation.conditionalSupportWidth]
    _ = representation.activeLiftedWidth := by
          simpa [FinitePositiveMatrixRepresentation.conditionalSupportWidth] using
            representation.firstSupportedWidths_add h_support

theorem FinitePositiveMatrixRepresentation.firstSupportedCollapsedRepresentation_liftedMatrix_eq_firstSupportedPrependedMatrix
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (h_support : 0 < supportedWidth M) :
    ((representation.firstSupportedCollapsedRepresentation h_support).liftedMatrix).cast
        (representation.firstSupportedCollapsedRepresentation_activeLiftedWidth h_support) =
      representation.firstSupportedPrependedMatrix h_support := by
  classical
  let collapsed := representation.firstSupportedCollapsedRepresentation h_support
  let h_width := representation.firstSupportedCollapsedRepresentation_activeLiftedWidth h_support
  let front := representation.conditionalSupportWidth (representation.firstSupportedBase h_support)
  let tail := representation.firstSupportedTailWidth h_support
  let base := representation.firstSupportedBase h_support
  let headBlock : List (Fin (tail + 1) × Fin representation.width) :=
    (representation.conditionalSupportWitnesses base).map (Prod.mk 0)
  let tailBlock : List (Fin (tail + 1) × Fin representation.width) :=
    List.map
      (fun t : Fin tail => (t.succ, representation.firstSupportedTailWitness h_support t))
      (List.finRange tail)
  have h_outputs :
      collapsed.activeLiftedOutputs = headBlock ++ tailBlock := by
    simpa [collapsed, front, tail, base, headBlock, tailBlock,
      FinitePositiveMatrixRepresentation.conditionalSupportWidth] using
      representation.firstSupportedCollapsedRepresentation_activeLiftedOutputs h_support
  apply ConditionalProbabilityMatrix.ext
  intro i j
  let jCollapsed : Fin collapsed.activeLiftedWidth := Fin.cast h_width.symm j
  have hltCollapsedWidth : j.1 < collapsed.activeLiftedWidth := by
    rw [h_width]
    exact j.2
  have hltCollapsed : j.1 < collapsed.activeLiftedOutputs.length := by
    simpa [collapsed, FinitePositiveMatrixRepresentation.activeLiftedWidth] using hltCollapsedWidth
  have h_active_get :
      collapsed.activeLiftedOutput jCollapsed = collapsed.activeLiftedOutputs.get ⟨j.1, hltCollapsed⟩ := by
    symm
    simpa [jCollapsed, hltCollapsed] using collapsed.activeLiftedOutput_eq jCollapsed
  by_cases h_head : j.1 < front
  · let head : Fin front := ⟨j.1, h_head⟩
    have h_head_len : headBlock.length = front := by
      simp [headBlock, front, base, FinitePositiveMatrixRepresentation.conditionalSupportWidth]
    let jBlock : Fin headBlock.length := ⟨j.1, by
      rwa [h_head_len]⟩
    let prepHeadIndex : Fin (front + tail) := ⟨head.1, by
      have h_le : front ≤ front + tail := Nat.le_add_right front tail
      exact Nat.lt_of_lt_of_le head.2 h_le⟩
    have h_cast_eq : Fin.cast (representation.firstSupportedWidths_add h_support).symm j = prepHeadIndex := by
      apply Fin.ext
      rfl
    have h_get_prefix :
        collapsed.activeLiftedOutputs.get ⟨j.1, hltCollapsed⟩ = headBlock.get jBlock := by
      simpa [h_outputs, headBlock, tailBlock, jBlock, hltCollapsed] using
        List.get_append_left_eq (l₂ := tailBlock) jBlock
    have h_block_get :
        headBlock.get jBlock = (0, representation.conditionalSupportWitness base head) := by
      unfold headBlock FinitePositiveMatrixRepresentation.conditionalSupportWitness
      simp [jBlock, head, base]
    have h_active_eq :
        collapsed.activeLiftedOutput jCollapsed =
          (0, representation.conditionalSupportWitness base head) := by
      calc
        collapsed.activeLiftedOutput jCollapsed = collapsed.activeLiftedOutputs.get ⟨j.1, hltCollapsed⟩ :=
          h_active_get
        _ = headBlock.get jBlock := h_get_prefix
        _ = (0, representation.conditionalSupportWitness base head) := h_block_get
    calc
      (collapsed.liftedMatrix.cast h_width).entry i j = collapsed.liftedMatrix.entry i jCollapsed := by
        rfl
      _ = representation.firstSupportedMass h_support head *
            (representation.firstSupportedCollapsedMatrix h_support).entry i 0 := by
              simpa [collapsed, base, h_active_eq,
                FinitePositiveMatrixRepresentation.firstSupportedMass,
                representation.firstSupportedCollapsedConditionalWeight_head h_support] using
                collapsed.liftedMatrix_entry_eq_conditional_weight i jCollapsed
      _ = (representation.firstSupportedPrependedMatrix h_support).entry i j := by
            rw [FinitePositiveMatrixRepresentation.firstSupportedPrependedMatrix,
              ConditionalProbabilityMatrix.cast_entry, h_cast_eq]
            symm
            simpa [front, tail, prepHeadIndex] using
              prependSourceMassMatrixPositiveWidth_head
                (representation.firstSupportedCollapsedMatrix h_support)
                (representation.firstSupportedMass h_support)
                (representation.firstSupportedMass_nonnegative h_support)
                (representation.firstSupportedBase_conditionalSupportWidth_pos h_support)
                i
                head
  · let tailIndex : Fin tail := ⟨j.1 - front, by
      have h_lt : j.1 < representation.activeLiftedWidth := j.2
      have h_sum : front + tail = representation.activeLiftedWidth := by
        simpa [front, tail] using representation.firstSupportedWidths_add h_support
      have h_ge : front ≤ j.1 := Nat.le_of_not_lt h_head
      omega⟩
    have h_head_len : headBlock.length = front := by
      simp [headBlock, front, base, FinitePositiveMatrixRepresentation.conditionalSupportWidth]
    have h_tail_len : tailBlock.length = tail := by
      simp [tailBlock]
    let jBlock : Fin tailBlock.length := ⟨tailIndex.1, by
      exact h_tail_len.symm ▸ tailIndex.2⟩
    let prepTailIndex : Fin (front + tail) := ⟨front + tailIndex.1, by
      exact Nat.add_lt_add_left tailIndex.2 front⟩
    have h_j_eq : j.1 = headBlock.length + jBlock.1 := by
      have h_ge : front ≤ j.1 := Nat.le_of_not_lt h_head
      calc
        j.1 = (j.1 - front) + front := by omega
        _ = front + (j.1 - front) := by omega
        _ = headBlock.length + jBlock.1 := by
            simp [h_head_len, jBlock, tailIndex]
    have h_cast_eq : Fin.cast (representation.firstSupportedWidths_add h_support).symm j = prepTailIndex := by
      apply Fin.ext
      dsimp [prepTailIndex, tailIndex]
      have h_ge : front ≤ j.1 := Nat.le_of_not_lt h_head
      omega
    have h_get_tail :
        collapsed.activeLiftedOutputs.get ⟨j.1, hltCollapsed⟩ = tailBlock.get jBlock := by
      have hltAppend : jBlock.1 + headBlock.length < (headBlock ++ tailBlock).length := by
        have hltAppendBase : tailIndex.1 + headBlock.length < (headBlock ++ tailBlock).length := by
          rw [List.length_append, h_head_len, h_tail_len]
          have h_lt : tailIndex.1 + front < tail + front :=
            Nat.add_lt_add_right tailIndex.2 front
          omega
        simpa [jBlock] using hltAppendBase
      have hltOutputsList : j.1 < (headBlock ++ tailBlock).length := by
        have hlt := hltCollapsed
        rw [h_outputs] at hlt
        exact hlt
      have hltOutputs' : j.1 < headBlock.length + tailBlock.length := by
        rw [List.length_append] at hltOutputsList
        exact hltOutputsList
      let jOutput : Fin (headBlock ++ tailBlock).length := ⟨j.1, by
        rw [List.length_append]
        exact hltOutputs'⟩
      have h_idx_eq :
          jOutput =
            ⟨jBlock.1 + headBlock.length, hltAppend⟩ := by
        apply Fin.ext
        calc
          j.1 = headBlock.length + jBlock.1 := h_j_eq
          _ = jBlock.1 + headBlock.length := by omega
      have h_get_append : (headBlock ++ tailBlock).get jOutput = tailBlock.get jBlock := by
        rw [h_idx_eq]
        exact List.get_append_right_eq jBlock
      simpa [h_outputs, jOutput] using h_get_append
    have h_block_get :
        tailBlock.get jBlock = (tailIndex.succ, representation.firstSupportedTailWitness h_support tailIndex) := by
      unfold tailBlock
      simp [jBlock, tailIndex]
    have h_active_eq :
        collapsed.activeLiftedOutput jCollapsed =
          (tailIndex.succ, representation.firstSupportedTailWitness h_support tailIndex) := by
      calc
        collapsed.activeLiftedOutput jCollapsed = collapsed.activeLiftedOutputs.get ⟨j.1, hltCollapsed⟩ :=
          h_active_get
        _ = tailBlock.get jBlock := h_get_tail
        _ = (tailIndex.succ, representation.firstSupportedTailWitness h_support tailIndex) := h_block_get
    calc
      (collapsed.liftedMatrix.cast h_width).entry i j = collapsed.liftedMatrix.entry i jCollapsed := by
        rfl
      _ = collapsed.pW_given_Y tailIndex.succ
            (representation.firstSupportedTailWitness h_support tailIndex) *
            (representation.firstSupportedCollapsedMatrix h_support).entry i tailIndex.succ := by
              simpa [h_active_eq] using collapsed.liftedMatrix_entry_eq_conditional_weight i jCollapsed
      _ = (representation.firstSupportedCollapsedMatrix h_support).entry i tailIndex.succ := by
            change representation.firstSupportedCollapsedConditionalWeight h_support tailIndex.succ
                (representation.firstSupportedTailWitness h_support tailIndex) *
                  (representation.firstSupportedCollapsedMatrix h_support).entry i tailIndex.succ =
              (representation.firstSupportedCollapsedMatrix h_support).entry i tailIndex.succ
            rw [representation.firstSupportedCollapsedConditionalWeight_tail h_support]
            simp
      _ = (representation.firstSupportedPrependedMatrix h_support).entry i j := by
            rw [FinitePositiveMatrixRepresentation.firstSupportedPrependedMatrix,
              ConditionalProbabilityMatrix.cast_entry, h_cast_eq]
            symm
            simpa [front, tail, prepTailIndex, tailIndex] using
              prependSourceMassMatrixPositiveWidth_tail
                (representation.firstSupportedCollapsedMatrix h_support)
                (representation.firstSupportedMass h_support)
                (representation.firstSupportedMass_nonnegative h_support)
                (representation.firstSupportedBase_conditionalSupportWidth_pos h_support)
                i
                tailIndex

noncomputable def supportedSubmatrix {k m : Nat}
    (M : ConditionalProbabilityMatrix k m) :
    ConditionalProbabilityMatrix k (supportedWidth M) :=
  { entry := fun i j => M.entry i (supportedOutput M j)
    nonnegative := by
      intro i j
      exact M.nonnegative i (supportedOutput M j) }

theorem supportedSubmatrix_column_pattern {k m : Nat}
    (M : ConditionalProbabilityMatrix k m)
    (j : Fin (supportedWidth M)) :
    column_pattern (supportedSubmatrix M) j =
      column_pattern M (supportedOutput M j) := by
  funext i
  rfl

theorem supportedSubmatrix_is_singular {k m : Nat}
    (M : ConditionalProbabilityMatrix k m)
    (h_singular : matrix_is_singular M) :
    matrix_is_singular (supportedSubmatrix M) := by
  intro j i₁ i₂ h_pos₁ h_pos₂
  exact h_singular (supportedOutput M j) i₁ i₂ h_pos₁ h_pos₂

theorem supportedSubmatrix_has_positive_entry {k m : Nat}
    (M : ConditionalProbabilityMatrix k m)
    (j : Fin (supportedWidth M)) :
    ∃ i : Fin k, 0 < (supportedSubmatrix M).entry i j := by
  simpa [supportedSubmatrix] using supportedOutput_has_positive_entry M j

theorem supportedOutputs_supportedSubmatrix_eq_finRange {k m : Nat}
    (M : ConditionalProbabilityMatrix k m) :
    supportedOutputs (supportedSubmatrix M) = List.finRange (supportedWidth M) := by
  classical
  unfold supportedOutputs
  refine List.filter_eq_self.2 ?_
  intro y hy
  simp
  exact supportedSubmatrix_has_positive_entry M y

theorem supportedWidth_supportedSubmatrix_eq {k m : Nat}
    (M : ConditionalProbabilityMatrix k m) :
    supportedWidth (supportedSubmatrix M) = supportedWidth M := by
  simpa [supportedWidth] using
    congrArg List.length (supportedOutputs_supportedSubmatrix_eq_finRange M)

theorem supportedOutput_supportedSubmatrix_cast {k m : Nat}
    (M : ConditionalProbabilityMatrix k m)
    (j : Fin (supportedWidth M)) :
    supportedOutput (supportedSubmatrix M)
        (Fin.cast (supportedWidth_supportedSubmatrix_eq M).symm j) = j := by
  have hk : j.1 < (List.finRange (supportedWidth M)).length := by
    rw [List.finRange, List.length_ofFn]
    exact j.2
  have h_output :
      supportedOutput (supportedSubmatrix M)
          (Fin.cast (supportedWidth_supportedSubmatrix_eq M).symm j) =
        (List.finRange (supportedWidth M)).get ⟨j.1, hk⟩ := by
    simp [supportedOutput, supportedOutputs_supportedSubmatrix_eq_finRange M]
  have hk_width : j.1 < supportedWidth M := j.2
  have h_get_raw := List.get_finRange_eq (n := supportedWidth M) j.1 hk
  have h_get :
      (List.finRange (supportedWidth M)).get ⟨j.1, hk⟩ = j := by
    calc
      (List.finRange (supportedWidth M)).get ⟨j.1, hk⟩ =
          (⟨j.1, hk_width⟩ : Fin (supportedWidth M)) := by
            exact h_get_raw.trans (by
              apply Fin.ext
              rfl)
    _ = j := by
          apply Fin.ext
          rfl
  exact h_output.trans h_get

theorem supportedOutput_supportedSubmatrix_eq_cast {k m : Nat}
    (M : ConditionalProbabilityMatrix k m)
    (j : Fin (supportedWidth (supportedSubmatrix M))) :
    supportedOutput (supportedSubmatrix M) j =
      Fin.cast (supportedWidth_supportedSubmatrix_eq M) j := by
  simpa using
    supportedOutput_supportedSubmatrix_cast M (Fin.cast (supportedWidth_supportedSubmatrix_eq M) j)

theorem supportedSubmatrix_supportedSubmatrix_eq {k m : Nat}
    (M : ConditionalProbabilityMatrix k m) :
    supportedSubmatrix (supportedSubmatrix M) =
      (supportedSubmatrix M).cast (supportedWidth_supportedSubmatrix_eq M).symm := by
  apply ConditionalProbabilityMatrix.ext
  intro i j
  calc
    (supportedSubmatrix (supportedSubmatrix M)).entry i j =
        (supportedSubmatrix M).entry i (supportedOutput (supportedSubmatrix M) j) := by
          rfl
    _ = (supportedSubmatrix M).entry i (Fin.cast (supportedWidth_supportedSubmatrix_eq M) j) := by
          rw [supportedOutput_supportedSubmatrix_eq_cast M j]
    _ = ((supportedSubmatrix M).cast (supportedWidth_supportedSubmatrix_eq M).symm).entry i j := by
          symm
          exact ConditionalProbabilityMatrix.cast_entry
            (supportedSubmatrix M) (supportedWidth_supportedSubmatrix_eq M).symm i j

theorem firstSupportedOutput_supportedSubmatrix_eq_zero {k m : Nat}
    (M : ConditionalProbabilityMatrix k m)
    (h_support : 0 < supportedWidth (supportedSubmatrix M)) :
    supportedOutput (supportedSubmatrix M) ⟨0, h_support⟩ =
      (⟨0, by simpa [supportedWidth_supportedSubmatrix_eq M] using h_support⟩ :
        Fin (supportedWidth M)) := by
  simpa using supportedOutput_supportedSubmatrix_eq_cast M ⟨0, h_support⟩

noncomputable def FinitePositiveMatrixRepresentation.supportedSubmatrixRepresentation
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M) :
    FinitePositiveMatrixRepresentation (supportedSubmatrix M) :=
  { width := representation.width
    pW := representation.pW
    decode := representation.supportedDecode
    positive := representation.positive
    normalized := representation.normalized
    pW_given_Y := fun y w => representation.pW_given_Y (supportedOutput M y) w
    conditional_normalized := by
      intro y
      exact representation.conditional_normalized (supportedOutput M y)
    conditional_factorization := by
      intro i y w
      have h_if :
          (if representation.supportedDecode i w = y then representation.pW w else 0) =
            (if representation.decode i w = supportedOutput M y then representation.pW w else 0) := by
        by_cases h_eq : representation.supportedDecode i w = y
        · have h_decode : representation.decode i w = supportedOutput M y :=
            (representation.supportedDecode_eq_iff i w y).mp h_eq
          simp [h_eq, h_decode]
        · have h_decode : representation.decode i w ≠ supportedOutput M y := by
            intro h_decode
            exact h_eq ((representation.supportedDecode_eq_iff i w y).mpr h_decode)
          simp [h_eq, h_decode]
      calc
        (if representation.supportedDecode i w = y then representation.pW w else 0) =
            (if representation.decode i w = supportedOutput M y then representation.pW w else 0) := h_if
        _ = representation.pW_given_Y (supportedOutput M y) w * M.entry i (supportedOutput M y) := by
              exact representation.conditional_factorization i (supportedOutput M y) w
        _ = representation.pW_given_Y (supportedOutput M y) w * (supportedSubmatrix M).entry i y := by
              rfl }

theorem FinitePositiveMatrixRepresentation.firstSupportedBase_supportedSubmatrixRepresentation_eq_zero
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (h_support : 0 < supportedWidth (supportedSubmatrix M)) :
    representation.supportedSubmatrixRepresentation.firstSupportedBase h_support =
      (⟨0, by simpa [supportedWidth_supportedSubmatrix_eq M] using h_support⟩ :
        Fin (supportedWidth M)) := by
  simpa [FinitePositiveMatrixRepresentation.firstSupportedBase] using
    firstSupportedOutput_supportedSubmatrix_eq_zero M h_support

noncomputable def FinitePositiveMatrixRepresentation.representativeLiftedMatrix
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M) :
    ConditionalProbabilityMatrix k (supportedWidth M) :=
  { entry := fun i j =>
      representation.liftedMatrix.entry i
        (representation.activeLiftedRepresentative
          (supportedOutput M j) (supportedOutput_has_positive_entry M j))
    nonnegative := by
      intro i j
      exact representation.liftedMatrix.nonnegative i _ }

theorem FinitePositiveMatrixRepresentation.representativeLiftedMatrix_entry_eq
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (i : Fin k) (j : Fin (supportedWidth M)) :
    representation.representativeLiftedMatrix.entry i j =
      representation.liftedMatrix.entry i
        (representation.activeLiftedRepresentative
          (supportedOutput M j) (supportedOutput_has_positive_entry M j)) := by
  rfl

theorem FinitePositiveMatrixRepresentation.representativeLiftedMatrix_entry_eq_conditional_weight
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (i : Fin k) (j : Fin (supportedWidth M)) :
    representation.representativeLiftedMatrix.entry i j =
      representation.pW_given_Y
          (supportedOutput M j)
          (representation.activeLiftedOutput
            (representation.activeLiftedRepresentative
              (supportedOutput M j) (supportedOutput_has_positive_entry M j))).2 *
        (supportedSubmatrix M).entry i j := by
  let representativeIndex := representation.activeLiftedRepresentative
    (supportedOutput M j) (supportedOutput_has_positive_entry M j)
  calc
    representation.representativeLiftedMatrix.entry i j =
        representation.liftedMatrix.entry i representativeIndex := by
          simp [FinitePositiveMatrixRepresentation.representativeLiftedMatrix_entry_eq,
            representativeIndex]
    _ = representation.pW_given_Y (representation.activeLiftedOutput representativeIndex).1
          (representation.activeLiftedOutput representativeIndex).2 *
            M.entry i (representation.activeLiftedOutput representativeIndex).1 := by
              simpa [representativeIndex] using
                representation.liftedMatrix_entry_eq_conditional_weight i representativeIndex
    _ = representation.pW_given_Y
          (supportedOutput M j)
          (representation.activeLiftedOutput representativeIndex).2 *
            M.entry i (supportedOutput M j) := by
              rw [representation.activeLiftedRepresentative_base
                (supportedOutput M j) (supportedOutput_has_positive_entry M j)]
    _ = representation.pW_given_Y
          (supportedOutput M j)
          (representation.activeLiftedOutput representativeIndex).2 *
            (supportedSubmatrix M).entry i j := by
              rfl

theorem FinitePositiveMatrixRepresentation.representativeLiftedMatrix_column_pattern
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (j : Fin (supportedWidth M)) :
    column_pattern representation.representativeLiftedMatrix j =
      column_pattern M (supportedOutput M j) := by
  let representativeIndex := representation.activeLiftedRepresentative
    (supportedOutput M j) (supportedOutput_has_positive_entry M j)
  calc
    column_pattern representation.representativeLiftedMatrix j =
        column_pattern representation.liftedMatrix representativeIndex := by
          funext i
          simp [column_pattern,
            FinitePositiveMatrixRepresentation.representativeLiftedMatrix_entry_eq,
            representativeIndex]
    _ = column_pattern M (representation.activeLiftedOutput representativeIndex).1 := by
          exact representation.activeLiftedOutput_column_pattern representativeIndex
    _ = column_pattern M (supportedOutput M j) := by
          rw [representation.activeLiftedRepresentative_base
            (supportedOutput M j) (supportedOutput_has_positive_entry M j)]

theorem FinitePositiveMatrixRepresentation.representativeLiftedMatrix_matches_supportedSubmatrix
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (j : Fin (supportedWidth M)) :
    column_pattern representation.representativeLiftedMatrix j =
      column_pattern (supportedSubmatrix M) j := by
  rw [representation.representativeLiftedMatrix_column_pattern,
    supportedSubmatrix_column_pattern]

theorem FinitePositiveMatrixRepresentation.representativeLiftedMatrix_is_singular
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (h_singular : matrix_is_singular M) :
    matrix_is_singular representation.representativeLiftedMatrix := by
  intro j i₁ i₂ h_pos₁ h_pos₂
  let representativeIndex := representation.activeLiftedRepresentative
    (supportedOutput M j) (supportedOutput_has_positive_entry M j)
  have h_rep₁ : 0 < representation.liftedMatrix.entry i₁ representativeIndex := by
    simpa [FinitePositiveMatrixRepresentation.representativeLiftedMatrix,
      representativeIndex] using h_pos₁
  have h_rep₂ : 0 < representation.liftedMatrix.entry i₂ representativeIndex := by
    simpa [FinitePositiveMatrixRepresentation.representativeLiftedMatrix,
      representativeIndex] using h_pos₂
  exact representation.liftedMatrix_is_singular h_singular representativeIndex i₁ i₂ h_rep₁ h_rep₂

noncomputable def FinitePositiveMatrixRepresentation.witnessSupportMatrix
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    {n : Nat}
    (witness : Fin n → Fin representation.width)
    (supports : Fin n → Fin m → Bool) :
    ConditionalProbabilityMatrix k n :=
  { entry := fun i j =>
      if supports j (representation.decode i (witness j)) then representation.pW (witness j) else 0
    nonnegative := by
      intro i j
      by_cases h_support : supports j (representation.decode i (witness j))
      · simp [h_support, Rat.le_of_lt (representation.positive (witness j))]
      · simp [h_support] }

theorem FinitePositiveMatrixRepresentation.witnessSupportMatrix_entry_eq
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    {n : Nat}
    (witness : Fin n → Fin representation.width)
    (supports : Fin n → Fin m → Bool)
    (i : Fin k) (j : Fin n) :
    (representation.witnessSupportMatrix witness supports).entry i j =
      if supports j (representation.decode i (witness j)) then representation.pW (witness j) else 0 := by
  rfl

theorem FinitePositiveMatrixRepresentation.witnessSupportMatrix_is_singular
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    {n : Nat}
    (witness : Fin n → Fin representation.width)
    (supports : Fin n → Fin m → Bool) :
    matrix_is_singular (representation.witnessSupportMatrix witness supports) := by
  intro j i₁ i₂ h_pos₁ h_pos₂
  by_cases h_support₁ : supports j (representation.decode i₁ (witness j))
  · by_cases h_support₂ : supports j (representation.decode i₂ (witness j))
    · simp [FinitePositiveMatrixRepresentation.witnessSupportMatrix, h_support₁, h_support₂]
    · rw [FinitePositiveMatrixRepresentation.witnessSupportMatrix_entry_eq] at h_pos₂
      simp [h_support₂] at h_pos₂
  · rw [FinitePositiveMatrixRepresentation.witnessSupportMatrix_entry_eq] at h_pos₁
    simp [h_support₁] at h_pos₁

def FinitePositiveMatrixRepresentation.witnessSupportAllUsed
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    {n : Nat}
    (witness : Fin n → Fin representation.width)
    (supports : Fin n → Fin m → Bool) : Prop :=
  ∀ j : Fin n, ∃ i : Fin k, supports j (representation.decode i (witness j)) = true

def FinitePositiveMatrixRepresentation.witnessSupportPairwiseDisjoint
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    {n : Nat}
    (witness : Fin n → Fin representation.width)
    (supports : Fin n → Fin m → Bool) : Prop :=
  ∀ j₁ j₂ : Fin n,
    witness j₁ = witness j₂ →
    j₁ ≠ j₂ →
    ∀ i : Fin k,
      supports j₁ (representation.decode i (witness j₁)) = true →
      supports j₂ (representation.decode i (witness j₁)) = false

def FinitePositiveMatrixRepresentation.witnessSupportValid
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    {n : Nat}
    (witness : Fin n → Fin representation.width)
    (supports : Fin n → Fin m → Bool) : Prop :=
  representation.witnessSupportAllUsed witness supports ∧
    representation.witnessSupportPairwiseDisjoint witness supports

def FinitePositiveMatrixRepresentation.witnessSupportWitnessCovered
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    {n : Nat}
    (witness : Fin n → Fin representation.width) : Prop :=
  ∀ w : Fin representation.width, ∃ j : Fin n, witness j = w

def FinitePositiveMatrixRepresentation.witnessSupportOutputCovered
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    {n : Nat}
    (witness : Fin n → Fin representation.width)
    (supports : Fin n → Fin m → Bool) : Prop :=
  ∀ y : Fin m, ∀ w : Fin representation.width,
    representation.liftedOutputUsed (y, w) →
      ∃ j : Fin n, witness j = w ∧ supports j y = true

theorem FinitePositiveMatrixRepresentation.witnessSupportWitnessCovered_width_le
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    {n : Nat}
    (witness : Fin n → Fin representation.width)
    (h_covered : representation.witnessSupportWitnessCovered witness) :
    representation.width ≤ n := by
  classical
  by_cases h_le : representation.width ≤ n
  · exact h_le
  · have h_lt : n < representation.width := Nat.lt_of_not_ge h_le
    let pick : Fin representation.width → Fin n :=
      fun w => Classical.choose (h_covered w)
    have h_pick : ∀ w : Fin representation.width, witness (pick w) = w := by
      intro w
      exact Classical.choose_spec (h_covered w)
    rcases exists_duplicate_of_lt (f := pick) h_lt with ⟨w₁, w₂, h_ne, h_eq⟩
    apply False.elim
    apply h_ne
    calc
      w₁ = witness (pick w₁) := (h_pick w₁).symm
      _ = witness (pick w₂) := by rw [h_eq]
      _ = w₂ := h_pick w₂

theorem FinitePositiveMatrixRepresentation.witnessSupportWitnessCovered_injective
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (witness : Fin representation.width → Fin representation.width)
    (h_covered : representation.witnessSupportWitnessCovered witness) :
    Function.Injective witness := by
  exact fin_surjective_same_injective witness h_covered

theorem FinitePositiveMatrixRepresentation.witnessSupport_support_true_of_covered_outputCovered
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (witness : Fin representation.width → Fin representation.width)
    (supports : Fin representation.width → Fin m → Bool)
    (h_covered : representation.witnessSupportWitnessCovered witness)
    (h_output : representation.witnessSupportOutputCovered witness supports)
    (i : Fin k) (j : Fin representation.width) :
    supports j (representation.decode i (witness j)) = true := by
  have h_inj : Function.Injective witness :=
    representation.witnessSupportWitnessCovered_injective witness h_covered
  have h_used : representation.liftedOutputUsed (representation.decode i (witness j), witness j) := by
    exact ⟨i, rfl⟩
  rcases h_output (representation.decode i (witness j)) (witness j) h_used with ⟨j', h_w, h_support⟩
  have h_j' : j' = j := h_inj (by simpa using h_w)
  simpa [h_j'] using h_support

theorem FinitePositiveMatrixRepresentation.witnessSupportMatrix_entry_eq_pW_of_covered_outputCovered
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (witness : Fin representation.width → Fin representation.width)
    (supports : Fin representation.width → Fin m → Bool)
    (h_covered : representation.witnessSupportWitnessCovered witness)
    (h_output : representation.witnessSupportOutputCovered witness supports)
    (i : Fin k) (j : Fin representation.width) :
    (representation.witnessSupportMatrix witness supports).entry i j =
      representation.pW (witness j) := by
  have h_support : supports j (representation.decode i (witness j)) = true :=
    representation.witnessSupport_support_true_of_covered_outputCovered
      witness supports h_covered h_output i j
  rw [representation.witnessSupportMatrix_entry_eq]
  simp [h_support]

theorem FinitePositiveMatrixRepresentation.witnessSupportMatrix_eq_massMatrix_of_covered_outputCovered
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (witness : Fin representation.width → Fin representation.width)
    (supports : Fin representation.width → Fin m → Bool)
    (h_covered : representation.witnessSupportWitnessCovered witness)
    (h_output : representation.witnessSupportOutputCovered witness supports) :
    representation.witnessSupportMatrix witness supports =
      massMatrix k representation.width
        (fun j => representation.pW (witness j))
        (fun j => Rat.le_of_lt (representation.positive (witness j))) := by
  apply ConditionalProbabilityMatrix.ext
  intro i j
  exact representation.witnessSupportMatrix_entry_eq_pW_of_covered_outputCovered
    witness supports h_covered h_output i j

theorem FinitePositiveMatrixRepresentation.witnessSupportMatrix_column_pattern_true_of_covered_outputCovered
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (witness : Fin representation.width → Fin representation.width)
    (supports : Fin representation.width → Fin m → Bool)
    (h_covered : representation.witnessSupportWitnessCovered witness)
    (h_output : representation.witnessSupportOutputCovered witness supports)
    (j : Fin representation.width) :
    column_pattern (representation.witnessSupportMatrix witness supports) j = fun _ => true := by
  funext i
  have h_pos :
      0 < (representation.witnessSupportMatrix witness supports).entry i j := by
    rw [representation.witnessSupportMatrix_entry_eq_pW_of_covered_outputCovered
      witness supports h_covered h_output i j]
    exact representation.positive (witness j)
  simp [column_pattern, h_pos]

theorem FinitePositiveMatrixRepresentation.witnessSupportMatrix_reachable_to_one_vector_of_covered_outputCovered
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (witness : Fin representation.width → Fin representation.width)
    (supports : Fin representation.width → Fin m → Bool)
    (h_covered : representation.witnessSupportWitnessCovered witness)
    (h_output : representation.witnessSupportOutputCovered witness supports) :
    MatrixReachable (pps_ppm_vpm_step (k := k))
      ⟨representation.width,
        representation.witnessSupportMatrix witness supports⟩
      ⟨1, one_vector_matrix k⟩ := by
  have h_inj : Function.Injective witness :=
    representation.witnessSupportWitnessCovered_injective witness h_covered
  have h_sum_one :
      discrete_sum (fun j : Fin representation.width => representation.pW (witness j)) = 1 := by
    calc
      discrete_sum (fun j : Fin representation.width => representation.pW (witness j)) =
          discrete_sum representation.pW := by
            exact discrete_sum_fin_reindex_injective representation.pW witness h_inj
      _ = 1 := representation.normalized
  have h_mass_reach :
      MatrixReachable (pps_ppm_vpm_step (k := k))
        ⟨representation.width,
          massMatrix k representation.width
            (fun j => representation.pW (witness j))
            (fun j => Rat.le_of_lt (representation.positive (witness j)))⟩
        ⟨1, one_vector_matrix k⟩ :=
    massMatrix_reachable_to_one_vector_of_sum_one_any
      (k := k)
      (mass := fun j : Fin representation.width => representation.pW (witness j))
      (fun j => representation.positive (witness j))
      h_sum_one
  simpa [representation.witnessSupportMatrix_eq_massMatrix_of_covered_outputCovered
    witness supports h_covered h_output] using h_mass_reach

theorem FinitePositiveMatrixRepresentation.witnessSupportMatrix_entry_positive_iff
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    {n : Nat}
    (witness : Fin n → Fin representation.width)
    (supports : Fin n → Fin m → Bool)
    (i : Fin k) (j : Fin n) :
    0 < (representation.witnessSupportMatrix witness supports).entry i j ↔
      supports j (representation.decode i (witness j)) = true := by
  rw [representation.witnessSupportMatrix_entry_eq]
  by_cases h_support : supports j (representation.decode i (witness j))
  · simp [h_support, representation.positive (witness j)]
  · simp [h_support]

noncomputable def FinitePositiveMatrixRepresentation.orderedWitnessMergeWitness
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    {n : Nat}
    (witness : Fin (n + 1) → Fin representation.width)
    (left right : Fin (n + 1))
    (h_lt : left.1 < right.1) :
    Fin n → Fin representation.width :=
  fun j =>
    if h : j = ordered_vpm_target left right h_lt then
      witness left
    else
      witness (ordered_vpm_backward left right h_lt ⟨j, h⟩).1

noncomputable def FinitePositiveMatrixRepresentation.orderedWitnessMergeSupports
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
  (_representation : FinitePositiveMatrixRepresentation M)
    {n : Nat}
    (supports : Fin (n + 1) → Fin m → Bool)
    (left right : Fin (n + 1))
    (h_lt : left.1 < right.1) :
    Fin n → Fin m → Bool :=
  fun j y =>
    if h : j = ordered_vpm_target left right h_lt then
      supports left y || supports right y
    else
      supports (ordered_vpm_backward left right h_lt ⟨j, h⟩).1 y

theorem FinitePositiveMatrixRepresentation.orderedWitnessMergeWitness_target
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    {n : Nat}
    (witness : Fin (n + 1) → Fin representation.width)
    (left right : Fin (n + 1))
    (h_lt : left.1 < right.1) :
    representation.orderedWitnessMergeWitness witness left right h_lt
      (ordered_vpm_target left right h_lt) = witness left := by
  simp [FinitePositiveMatrixRepresentation.orderedWitnessMergeWitness]

theorem FinitePositiveMatrixRepresentation.orderedWitnessMergeSupports_target
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    {n : Nat}
    (supports : Fin (n + 1) → Fin m → Bool)
    (left right : Fin (n + 1))
    (h_lt : left.1 < right.1)
    (y : Fin m) :
    representation.orderedWitnessMergeSupports supports left right h_lt
      (ordered_vpm_target left right h_lt) y =
        (supports left y || supports right y) := by
  simp [FinitePositiveMatrixRepresentation.orderedWitnessMergeSupports]

theorem FinitePositiveMatrixRepresentation.orderedWitnessMergeWitness_rest
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    {n : Nat}
    (witness : Fin (n + 1) → Fin representation.width)
    (left right : Fin (n + 1))
    (h_lt : left.1 < right.1)
    (old : ColumnsExceptTwo left right) :
    representation.orderedWitnessMergeWitness witness left right h_lt
      ((ordered_vpm_transport left right h_lt).forward old).1 = witness old.1 := by
  have h_not_target : (ordered_vpm_forward left right h_lt old).1 ≠ ordered_vpm_target left right h_lt :=
    (ordered_vpm_forward left right h_lt old).2
  simp [FinitePositiveMatrixRepresentation.orderedWitnessMergeWitness,
    ordered_vpm_transport, h_not_target,
    ordered_vpm_backward_forward left right h_lt old]

theorem FinitePositiveMatrixRepresentation.orderedWitnessMergeSupports_rest
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    {n : Nat}
    (supports : Fin (n + 1) → Fin m → Bool)
    (left right : Fin (n + 1))
    (h_lt : left.1 < right.1)
    (old : ColumnsExceptTwo left right)
    (y : Fin m) :
    representation.orderedWitnessMergeSupports supports left right h_lt
      ((ordered_vpm_transport left right h_lt).forward old).1 y = supports old.1 y := by
  have h_not_target : (ordered_vpm_forward left right h_lt old).1 ≠ ordered_vpm_target left right h_lt :=
    (ordered_vpm_forward left right h_lt old).2
  simp [FinitePositiveMatrixRepresentation.orderedWitnessMergeSupports,
    ordered_vpm_transport, h_not_target,
    ordered_vpm_backward_forward left right h_lt old]

theorem FinitePositiveMatrixRepresentation.witnessSupportAllUsed_orderedMerge
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    {n : Nat}
    (witness : Fin (n + 1) → Fin representation.width)
    (supports : Fin (n + 1) → Fin m → Bool)
    (left right : Fin (n + 1))
    (h_lt : left.1 < right.1)
    (h_used : representation.witnessSupportAllUsed witness supports) :
    representation.witnessSupportAllUsed
      (representation.orderedWitnessMergeWitness witness left right h_lt)
      (representation.orderedWitnessMergeSupports supports left right h_lt) := by
  intro j
  by_cases h_target : j = ordered_vpm_target left right h_lt
  · rcases h_used left with ⟨i, h_left⟩
    subst j
    refine ⟨i, ?_⟩
    simp [FinitePositiveMatrixRepresentation.orderedWitnessMergeWitness,
      FinitePositiveMatrixRepresentation.orderedWitnessMergeSupports, h_left]
  · let old : ColumnsExceptTwo left right := ordered_vpm_backward left right h_lt ⟨j, h_target⟩
    rcases h_used old.1 with ⟨i, h_old⟩
    refine ⟨i, ?_⟩
    simp [FinitePositiveMatrixRepresentation.orderedWitnessMergeWitness,
      FinitePositiveMatrixRepresentation.orderedWitnessMergeSupports,
      h_target, old, h_old]

theorem FinitePositiveMatrixRepresentation.witnessSupportPairwiseDisjoint_orderedMerge
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    {n : Nat}
    (witness : Fin (n + 1) → Fin representation.width)
    (supports : Fin (n + 1) → Fin m → Bool)
    (left right : Fin (n + 1))
    (h_lt : left.1 < right.1)
    (h_same_lr : witness left = witness right)
    (h_pairwise : representation.witnessSupportPairwiseDisjoint witness supports) :
    representation.witnessSupportPairwiseDisjoint
      (representation.orderedWitnessMergeWitness witness left right h_lt)
      (representation.orderedWitnessMergeSupports supports left right h_lt) := by
  intro j₁ j₂ h_same h_ne i h_support
  by_cases h_j₁_target : j₁ = ordered_vpm_target left right h_lt
  · subst j₁
    have h_j₂_not_target : j₂ ≠ ordered_vpm_target left right h_lt := by
      intro h_eq
      exact h_ne h_eq.symm
    let old₂ : ColumnsExceptTwo left right :=
      ordered_vpm_backward left right h_lt ⟨j₂, h_j₂_not_target⟩
    have h_j₂_eq : ((ordered_vpm_transport left right h_lt).forward old₂).1 = j₂ := by
      simpa [ordered_vpm_transport, old₂] using congrArg Subtype.val
        (ordered_vpm_forward_backward left right h_lt ⟨j₂, h_j₂_not_target⟩)
    have h_same_old₂ : witness left = witness old₂.1 := by
      have h_same' := h_same
      rw [← h_j₂_eq] at h_same'
      rw [representation.orderedWitnessMergeWitness_target witness left right h_lt,
        representation.orderedWitnessMergeWitness_rest witness left right h_lt old₂] at h_same'
      exact h_same'
    have h_target_support :
        supports left (representation.decode i (witness left)) ||
          supports right (representation.decode i (witness left)) = true := by
      rw [representation.orderedWitnessMergeWitness_target witness left right h_lt,
        representation.orderedWitnessMergeSupports_target supports left right h_lt] at h_support
      simpa using h_support
    have h_left_ne_old₂ : left ≠ old₂.1 := by
      intro h_eq
      exact old₂.2.1 h_eq.symm
    have h_right_ne_old₂ : right ≠ old₂.1 := by
      intro h_eq
      exact old₂.2.2 h_eq.symm
    by_cases h_left_support : supports left (representation.decode i (witness left))
    · have h_old₂_false :
          supports old₂.1 (representation.decode i (witness left)) = false :=
        h_pairwise left old₂.1 h_same_old₂ h_left_ne_old₂ i h_left_support
      rw [← h_j₂_eq,
        representation.orderedWitnessMergeWitness_target witness left right h_lt,
        representation.orderedWitnessMergeSupports_rest supports left right h_lt old₂]
      exact h_old₂_false
    · have h_right_support : supports right (representation.decode i (witness left)) = true := by
        cases h_right : supports right (representation.decode i (witness left))
        · simp [h_left_support, h_right] at h_target_support
        · rfl
      have h_same_right_old₂ : witness right = witness old₂.1 := by
        calc
          witness right = witness left := h_same_lr.symm
          _ = witness old₂.1 := h_same_old₂
      have h_right_support' : supports right (representation.decode i (witness right)) = true := by
        simpa [h_same_lr] using h_right_support
      have h_old₂_false :
          supports old₂.1 (representation.decode i (witness right)) = false :=
        h_pairwise right old₂.1 h_same_right_old₂ h_right_ne_old₂ i h_right_support'
      rw [← h_j₂_eq,
        representation.orderedWitnessMergeWitness_target witness left right h_lt,
        representation.orderedWitnessMergeSupports_rest supports left right h_lt old₂]
      simpa [h_same_lr] using h_old₂_false
  · by_cases h_j₂_target : j₂ = ordered_vpm_target left right h_lt
    · subst j₂
      have h_j₁_not_target : j₁ ≠ ordered_vpm_target left right h_lt := h_j₁_target
      let old₁ : ColumnsExceptTwo left right :=
        ordered_vpm_backward left right h_lt ⟨j₁, h_j₁_not_target⟩
      have h_j₁_eq : ((ordered_vpm_transport left right h_lt).forward old₁).1 = j₁ := by
        simpa [ordered_vpm_transport, old₁] using congrArg Subtype.val
          (ordered_vpm_forward_backward left right h_lt ⟨j₁, h_j₁_not_target⟩)
      have h_same_old₁ : witness old₁.1 = witness left := by
        have h_same' := h_same
        rw [← h_j₁_eq] at h_same'
        rw [representation.orderedWitnessMergeWitness_rest witness left right h_lt old₁,
          representation.orderedWitnessMergeWitness_target witness left right h_lt] at h_same'
        exact h_same'
      have h_old₁_support :
          supports old₁.1 (representation.decode i (witness old₁.1)) = true := by
        have h_support' := h_support
        rw [← h_j₁_eq] at h_support'
        rw [representation.orderedWitnessMergeWitness_rest witness left right h_lt old₁,
          representation.orderedWitnessMergeSupports_rest supports left right h_lt old₁] at h_support'
        exact h_support'
      have h_left_false : supports left (representation.decode i (witness left)) = false := by
        have h_old_left_false :
            supports left (representation.decode i (witness old₁.1)) = false :=
          h_pairwise old₁.1 left h_same_old₁ old₁.2.1 i h_old₁_support
        simpa [h_same_old₁] using h_old_left_false
      have h_same_old₁_right : witness old₁.1 = witness right := by
        calc
          witness old₁.1 = witness left := h_same_old₁
          _ = witness right := h_same_lr
      have h_right_false : supports right (representation.decode i (witness left)) = false := by
        have h_old_right_false :
            supports right (representation.decode i (witness old₁.1)) = false :=
          h_pairwise old₁.1 right h_same_old₁_right old₁.2.2 i h_old₁_support
        simpa [h_same_old₁] using h_old_right_false
      rw [← h_j₁_eq,
        representation.orderedWitnessMergeWitness_rest witness left right h_lt old₁,
        representation.orderedWitnessMergeSupports_target supports left right h_lt]
      simp [h_same_old₁, h_left_false, h_right_false]
    · let old₁ : ColumnsExceptTwo left right :=
        ordered_vpm_backward left right h_lt ⟨j₁, h_j₁_target⟩
      let old₂ : ColumnsExceptTwo left right :=
        ordered_vpm_backward left right h_lt ⟨j₂, h_j₂_target⟩
      have h_j₁_eq : ((ordered_vpm_transport left right h_lt).forward old₁).1 = j₁ := by
        simpa [ordered_vpm_transport, old₁] using congrArg Subtype.val
          (ordered_vpm_forward_backward left right h_lt ⟨j₁, h_j₁_target⟩)
      have h_j₂_eq : ((ordered_vpm_transport left right h_lt).forward old₂).1 = j₂ := by
        simpa [ordered_vpm_transport, old₂] using congrArg Subtype.val
          (ordered_vpm_forward_backward left right h_lt ⟨j₂, h_j₂_target⟩)
      have h_same_old : witness old₁.1 = witness old₂.1 := by
        have h_same' := h_same
        rw [← h_j₁_eq, ← h_j₂_eq] at h_same'
        rw [representation.orderedWitnessMergeWitness_rest witness left right h_lt old₁,
          representation.orderedWitnessMergeWitness_rest witness left right h_lt old₂] at h_same'
        exact h_same'
      have h_old₁_support :
          supports old₁.1 (representation.decode i (witness old₁.1)) = true := by
        have h_support' := h_support
        rw [← h_j₁_eq] at h_support'
        rw [representation.orderedWitnessMergeWitness_rest witness left right h_lt old₁,
          representation.orderedWitnessMergeSupports_rest supports left right h_lt old₁] at h_support'
        exact h_support'
      have h_old_ne : old₁.1 ≠ old₂.1 := by
        intro h_old_eq
        have h_old_sub : old₁ = old₂ := by
          apply Subtype.ext
          simpa using h_old_eq
        have h_forward_eq : ordered_vpm_forward left right h_lt old₁ = ordered_vpm_forward left right h_lt old₂ := by
          simp [h_old_sub]
        have h_left_new : ordered_vpm_forward left right h_lt old₁ = ⟨j₁, h_j₁_target⟩ := by
          simpa [old₁] using ordered_vpm_forward_backward left right h_lt ⟨j₁, h_j₁_target⟩
        have h_right_new : ordered_vpm_forward left right h_lt old₂ = ⟨j₂, h_j₂_target⟩ := by
          simpa [old₂] using ordered_vpm_forward_backward left right h_lt ⟨j₂, h_j₂_target⟩
        have h_new_eq :
            (⟨j₁, h_j₁_target⟩ : ColumnsExceptTarget (ordered_vpm_target left right h_lt)) =
              ⟨j₂, h_j₂_target⟩ := by
          calc
            (⟨j₁, h_j₁_target⟩ : ColumnsExceptTarget (ordered_vpm_target left right h_lt)) =
                ordered_vpm_forward left right h_lt old₁ := by
                  symm
                  exact h_left_new
            _ = ordered_vpm_forward left right h_lt old₂ := h_forward_eq
            _ = (⟨j₂, h_j₂_target⟩ : ColumnsExceptTarget (ordered_vpm_target left right h_lt)) :=
                  h_right_new
        exact h_ne (congrArg Subtype.val h_new_eq)
      have h_old₂_false :
          supports old₂.1 (representation.decode i (witness old₁.1)) = false :=
        h_pairwise old₁.1 old₂.1 h_same_old h_old_ne i h_old₁_support
      rw [← h_j₂_eq,
        representation.orderedWitnessMergeSupports_rest supports left right h_lt old₂]
      rw [← h_j₁_eq,
        representation.orderedWitnessMergeWitness_rest witness left right h_lt old₁]
      exact h_old₂_false

theorem FinitePositiveMatrixRepresentation.witnessSupportValid_orderedMerge
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    {n : Nat}
    (witness : Fin (n + 1) → Fin representation.width)
    (supports : Fin (n + 1) → Fin m → Bool)
    (left right : Fin (n + 1))
    (h_lt : left.1 < right.1)
    (h_same_lr : witness left = witness right)
    (h_valid : representation.witnessSupportValid witness supports) :
    representation.witnessSupportValid
      (representation.orderedWitnessMergeWitness witness left right h_lt)
      (representation.orderedWitnessMergeSupports supports left right h_lt) := by
  exact ⟨representation.witnessSupportAllUsed_orderedMerge witness supports left right h_lt h_valid.1,
    representation.witnessSupportPairwiseDisjoint_orderedMerge
      witness supports left right h_lt h_same_lr h_valid.2⟩

theorem FinitePositiveMatrixRepresentation.witnessSupportWitnessCovered_orderedMerge
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    {n : Nat}
    (witness : Fin (n + 1) → Fin representation.width)
    (left right : Fin (n + 1))
    (h_lt : left.1 < right.1)
    (h_same_lr : witness left = witness right)
    (h_covered : representation.witnessSupportWitnessCovered witness) :
    representation.witnessSupportWitnessCovered
      (representation.orderedWitnessMergeWitness witness left right h_lt) := by
  intro w
  by_cases h_w : w = witness left
  · subst w
    exact ⟨ordered_vpm_target left right h_lt,
      representation.orderedWitnessMergeWitness_target witness left right h_lt⟩
  · rcases h_covered w with ⟨j, hj⟩
    have h_j_ne_left : j ≠ left := by
      intro h_eq
      apply h_w
      calc
        w = witness j := hj.symm
        _ = witness left := by simp [h_eq]
    have h_j_ne_right : j ≠ right := by
      intro h_eq
      apply h_w
      calc
        w = witness j := hj.symm
        _ = witness right := by simp [h_eq]
        _ = witness left := h_same_lr.symm
    let old : ColumnsExceptTwo left right := ⟨j, h_j_ne_left, h_j_ne_right⟩
    refine ⟨((ordered_vpm_transport left right h_lt).forward old).1, ?_⟩
    calc
      representation.orderedWitnessMergeWitness witness left right h_lt
          ((ordered_vpm_transport left right h_lt).forward old).1 = witness old.1 := by
            exact representation.orderedWitnessMergeWitness_rest witness left right h_lt old
      _ = witness j := rfl
      _ = w := hj

theorem FinitePositiveMatrixRepresentation.witnessSupportOutputCovered_orderedMerge
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    {n : Nat}
    (witness : Fin (n + 1) → Fin representation.width)
    (supports : Fin (n + 1) → Fin m → Bool)
    (left right : Fin (n + 1))
    (h_lt : left.1 < right.1)
    (h_same_lr : witness left = witness right)
    (h_covered : representation.witnessSupportOutputCovered witness supports) :
    representation.witnessSupportOutputCovered
      (representation.orderedWitnessMergeWitness witness left right h_lt)
      (representation.orderedWitnessMergeSupports supports left right h_lt) := by
  intro y w h_used
  rcases h_covered y w h_used with ⟨j, h_w, h_support⟩
  by_cases h_j_left : j = left
  · subst j
    refine ⟨ordered_vpm_target left right h_lt, ?_, ?_⟩
    · rw [representation.orderedWitnessMergeWitness_target witness left right h_lt]
      exact h_w
    · rw [representation.orderedWitnessMergeSupports_target supports left right h_lt]
      simp [h_support]
  · by_cases h_j_right : j = right
    · subst j
      refine ⟨ordered_vpm_target left right h_lt, ?_, ?_⟩
      · rw [representation.orderedWitnessMergeWitness_target witness left right h_lt]
        exact h_same_lr.trans h_w
      · rw [representation.orderedWitnessMergeSupports_target supports left right h_lt]
        simp [h_support]
    · let old : ColumnsExceptTwo left right := ⟨j, h_j_left, h_j_right⟩
      refine ⟨((ordered_vpm_transport left right h_lt).forward old).1, ?_, ?_⟩
      · rw [representation.orderedWitnessMergeWitness_rest witness left right h_lt old]
        exact h_w
      · rw [representation.orderedWitnessMergeSupports_rest supports left right h_lt old]
        exact h_support

theorem FinitePositiveMatrixRepresentation.witnessSupportMatrix_ordered_vpm_target_entry
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    {n : Nat}
    (witness : Fin (n + 1) → Fin representation.width)
    (supports : Fin (n + 1) → Fin m → Bool)
    (left right : Fin (n + 1))
    (h_lt : left.1 < right.1)
    (h_same : witness left = witness right)
    (h_disjoint : ∀ i : Fin k,
      supports left (representation.decode i (witness left)) = true →
        supports right (representation.decode i (witness left)) = false)
    (i : Fin k) :
    (ordered_vpm_merge_matrix (representation.witnessSupportMatrix witness supports) left right h_lt).entry i
        (ordered_vpm_target left right h_lt) =
      (representation.witnessSupportMatrix
        (representation.orderedWitnessMergeWitness witness left right h_lt)
        (representation.orderedWitnessMergeSupports supports left right h_lt)).entry i
          (ordered_vpm_target left right h_lt) := by
  by_cases h_left : supports left (representation.decode i (witness left))
  · have h_right : supports right (representation.decode i (witness left)) = false :=
      h_disjoint i h_left
    rw [ordered_vpm_merge_matrix_target,
      representation.witnessSupportMatrix_entry_eq,
      representation.witnessSupportMatrix_entry_eq,
      representation.witnessSupportMatrix_entry_eq,
      ← h_same]
    simp [FinitePositiveMatrixRepresentation.orderedWitnessMergeWitness,
      FinitePositiveMatrixRepresentation.orderedWitnessMergeSupports,
      h_left, h_right, Rat.add_zero]
  · by_cases h_right : supports right (representation.decode i (witness left))
    · rw [ordered_vpm_merge_matrix_target,
        representation.witnessSupportMatrix_entry_eq,
        representation.witnessSupportMatrix_entry_eq,
        representation.witnessSupportMatrix_entry_eq,
        ← h_same]
      simp [FinitePositiveMatrixRepresentation.orderedWitnessMergeWitness,
        FinitePositiveMatrixRepresentation.orderedWitnessMergeSupports,
        h_left, h_right, Rat.zero_add]
    · rw [ordered_vpm_merge_matrix_target,
        representation.witnessSupportMatrix_entry_eq,
        representation.witnessSupportMatrix_entry_eq,
        representation.witnessSupportMatrix_entry_eq,
        ← h_same]
      simp [FinitePositiveMatrixRepresentation.orderedWitnessMergeWitness,
        FinitePositiveMatrixRepresentation.orderedWitnessMergeSupports,
        h_left, h_right, Rat.add_zero]

theorem FinitePositiveMatrixRepresentation.witnessSupportMatrix_ordered_vpm_rest_entry
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    {n : Nat}
    (witness : Fin (n + 1) → Fin representation.width)
    (supports : Fin (n + 1) → Fin m → Bool)
    (left right : Fin (n + 1))
    (h_lt : left.1 < right.1)
    (old : ColumnsExceptTwo left right)
    (i : Fin k) :
    (representation.witnessSupportMatrix
      (representation.orderedWitnessMergeWitness witness left right h_lt)
      (representation.orderedWitnessMergeSupports supports left right h_lt)).entry i
        ((ordered_vpm_transport left right h_lt).forward old).1 =
      (representation.witnessSupportMatrix witness supports).entry i old.1 := by
  have h_not_target : (ordered_vpm_forward left right h_lt old).1 ≠ ordered_vpm_target left right h_lt :=
    (ordered_vpm_forward left right h_lt old).2
  rw [representation.witnessSupportMatrix_entry_eq,
    representation.witnessSupportMatrix_entry_eq]
  simp [FinitePositiveMatrixRepresentation.orderedWitnessMergeWitness,
    FinitePositiveMatrixRepresentation.orderedWitnessMergeSupports,
    ordered_vpm_transport, h_not_target,
    ordered_vpm_backward_forward left right h_lt old]

theorem FinitePositiveMatrixRepresentation.witnessSupportMatrix_column_value_of_support_true
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    {n : Nat}
    (witness : Fin n → Fin representation.width)
    (supports : Fin n → Fin m → Bool)
    (i : Fin k) (j : Fin n)
    (h_support : supports j (representation.decode i (witness j)) = true) :
    column_value (representation.witnessSupportMatrix witness supports) j = representation.pW (witness j) := by
  have h_entry_pos : 0 < (representation.witnessSupportMatrix witness supports).entry i j := by
    rw [representation.witnessSupportMatrix_entry_eq]
    simp [h_support, representation.positive (witness j)]
  have h_col : column_pattern (representation.witnessSupportMatrix witness supports) j i = true := by
    simp [column_pattern, h_entry_pos]
  have h_entry_eq_value :
      (representation.witnessSupportMatrix witness supports).entry i j =
        column_value (representation.witnessSupportMatrix witness supports) j := by
    rw [entry_eq_column_value_or_zero (representation.witnessSupportMatrix witness supports)
      (representation.witnessSupportMatrix_is_singular witness supports) i j, h_col]
    simp
  have h_entry_eq_pw :
      (representation.witnessSupportMatrix witness supports).entry i j = representation.pW (witness j) := by
    rw [representation.witnessSupportMatrix_entry_eq]
    simp [h_support]
  calc
    column_value (representation.witnessSupportMatrix witness supports) j =
        (representation.witnessSupportMatrix witness supports).entry i j := by
          symm
          exact h_entry_eq_value
    _ = representation.pW (witness j) := h_entry_eq_pw

theorem FinitePositiveMatrixRepresentation.witnessSupportMatrix_same_witness_equal_column_value
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    {n : Nat}
    (witness : Fin (n + 1) → Fin representation.width)
    (supports : Fin (n + 1) → Fin m → Bool)
    (left right : Fin (n + 1))
    (h_same : witness left = witness right)
    (h_left_used : ∃ i : Fin k, supports left (representation.decode i (witness left)) = true)
    (h_right_used : ∃ i : Fin k, supports right (representation.decode i (witness right)) = true) :
    column_value (representation.witnessSupportMatrix witness supports) left =
      column_value (representation.witnessSupportMatrix witness supports) right := by
  rcases h_left_used with ⟨i_left, h_left_support⟩
  rcases h_right_used with ⟨i_right, h_right_support⟩
  rw [representation.witnessSupportMatrix_column_value_of_support_true witness supports i_left left h_left_support,
    representation.witnessSupportMatrix_column_value_of_support_true witness supports i_right right h_right_support,
    h_same]

theorem FinitePositiveMatrixRepresentation.witnessSupportMatrix_disjoint_entry_support
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    {n : Nat}
    (witness : Fin (n + 1) → Fin representation.width)
    (supports : Fin (n + 1) → Fin m → Bool)
    (left right : Fin (n + 1))
    (h_same : witness left = witness right)
    (h_disjoint : ∀ i : Fin k,
      supports left (representation.decode i (witness left)) = true →
        supports right (representation.decode i (witness left)) = false) :
    ∀ i : Fin k,
      0 < (representation.witnessSupportMatrix witness supports).entry i left →
      (representation.witnessSupportMatrix witness supports).entry i right = 0 := by
  intro i h_pos
  have h_left_support : supports left (representation.decode i (witness left)) = true := by
    by_cases h_hit : supports left (representation.decode i (witness left))
    · exact h_hit
    · rw [representation.witnessSupportMatrix_entry_eq] at h_pos
      simp [h_hit] at h_pos
  have h_right_support : supports right (representation.decode i (witness left)) = false :=
    h_disjoint i h_left_support
  rw [representation.witnessSupportMatrix_entry_eq, ← h_same]
  simp [h_right_support]

theorem FinitePositiveMatrixRepresentation.witnessSupportMatrix_ordered_vpm_is_vpm_operation
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    {n : Nat}
    (witness : Fin (n + 1) → Fin representation.width)
    (supports : Fin (n + 1) → Fin m → Bool)
    (left right : Fin (n + 1))
    (h_lt : left.1 < right.1)
    (h_same : witness left = witness right)
    (h_left_used : ∃ i : Fin k, supports left (representation.decode i (witness left)) = true)
    (h_right_used : ∃ i : Fin k, supports right (representation.decode i (witness right)) = true)
    (h_disjoint : ∀ i : Fin k,
      supports left (representation.decode i (witness left)) = true →
        supports right (representation.decode i (witness left)) = false) :
    is_vpm_operation
      (representation.witnessSupportMatrix witness supports)
      (representation.witnessSupportMatrix
        (representation.orderedWitnessMergeWitness witness left right h_lt)
        (representation.orderedWitnessMergeSupports supports left right h_lt)) := by
  refine ⟨representation.witnessSupportMatrix_is_singular witness supports,
    representation.witnessSupportMatrix_is_singular
      (representation.orderedWitnessMergeWitness witness left right h_lt)
      (representation.orderedWitnessMergeSupports supports left right h_lt),
    rfl, left, right, ?_, ?_, ?_, ordered_vpm_target left right h_lt, ?_,
    ordered_vpm_transport left right h_lt, ?_, ?_⟩
  · intro h_eq
    have h_val : left.1 = right.1 := by
      simpa using congrArg Fin.val h_eq
    omega
  · exact representation.witnessSupportMatrix_same_witness_equal_column_value
      witness supports left right h_same h_left_used h_right_used
  · exact representation.witnessSupportMatrix_disjoint_entry_support
      witness supports left right h_same h_disjoint
  · simp [ordered_vpm_target, Nat.min_eq_left (Nat.le_of_lt h_lt)]
  · intro i
    calc
      (representation.witnessSupportMatrix
        (representation.orderedWitnessMergeWitness witness left right h_lt)
        (representation.orderedWitnessMergeSupports supports left right h_lt)).entry i
          (ordered_vpm_target left right h_lt) =
          (ordered_vpm_merge_matrix (representation.witnessSupportMatrix witness supports) left right h_lt).entry i
            (ordered_vpm_target left right h_lt) := by
              symm
              exact representation.witnessSupportMatrix_ordered_vpm_target_entry
                witness supports left right h_lt h_same h_disjoint i
      _ = (representation.witnessSupportMatrix witness supports).entry i left +
            (representation.witnessSupportMatrix witness supports).entry i right := by
              exact ordered_vpm_merge_matrix_target
                (representation.witnessSupportMatrix witness supports) left right h_lt i
  · intro old i
    exact representation.witnessSupportMatrix_ordered_vpm_rest_entry
      witness supports left right h_lt old i

theorem FinitePositiveMatrixRepresentation.witnessSupportMatrix_ordered_vpm_reachable_by_pps_ppm_vpm
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    {n : Nat}
    (witness : Fin (n + 1) → Fin representation.width)
    (supports : Fin (n + 1) → Fin m → Bool)
    (left right : Fin (n + 1))
    (h_lt : left.1 < right.1)
    (h_same : witness left = witness right)
    (h_left_used : ∃ i : Fin k, supports left (representation.decode i (witness left)) = true)
    (h_right_used : ∃ i : Fin k, supports right (representation.decode i (witness right)) = true)
    (h_disjoint : ∀ i : Fin k,
      supports left (representation.decode i (witness left)) = true →
        supports right (representation.decode i (witness left)) = false) :
    MatrixReachable (pps_ppm_vpm_step (k := k))
      ⟨n + 1, representation.witnessSupportMatrix witness supports⟩
      ⟨n,
        representation.witnessSupportMatrix
          (representation.orderedWitnessMergeWitness witness left right h_lt)
          (representation.orderedWitnessMergeSupports supports left right h_lt)⟩ := by
  apply MatrixReachable.single
  dsimp [pps_ppm_vpm_step, pps_step, ppm_step, vpm_step]
  exact Or.inr (Or.inr
    (representation.witnessSupportMatrix_ordered_vpm_is_vpm_operation
      witness supports left right h_lt h_same h_left_used h_right_used h_disjoint))

theorem FinitePositiveMatrixRepresentation.witnessSupportMatrix_ordered_vpm_reachable_by_pps_ppm_vpm_of_valid
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    {n : Nat}
    (witness : Fin (n + 1) → Fin representation.width)
    (supports : Fin (n + 1) → Fin m → Bool)
    (h_used : representation.witnessSupportAllUsed witness supports)
    (h_pairwise : representation.witnessSupportPairwiseDisjoint witness supports)
    (left right : Fin (n + 1))
    (h_lt : left.1 < right.1)
    (h_same : witness left = witness right) :
    MatrixReachable (pps_ppm_vpm_step (k := k))
      ⟨n + 1, representation.witnessSupportMatrix witness supports⟩
      ⟨n,
        representation.witnessSupportMatrix
          (representation.orderedWitnessMergeWitness witness left right h_lt)
          (representation.orderedWitnessMergeSupports supports left right h_lt)⟩ := by
  have h_ne : left ≠ right := by
    intro h_eq
    have h_val : left.1 = right.1 := by
      simpa using congrArg Fin.val h_eq
    omega
  exact representation.witnessSupportMatrix_ordered_vpm_reachable_by_pps_ppm_vpm
    witness supports left right h_lt h_same (h_used left) (h_used right)
    (h_pairwise left right h_same h_ne)

theorem FinitePositiveMatrixRepresentation.witnessSupportMatrix_ordered_vpm_reachable_by_pps_ppm_vpm_state
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (start : MatrixState k)
    (witness : Fin start.1 → Fin representation.width)
    (supports : Fin start.1 → Fin m → Bool)
    (h_start : start.2 = representation.witnessSupportMatrix witness supports)
    (left right : Fin start.1)
    (h_lt : left.1 < right.1)
    (h_same : witness left = witness right)
    (h_left_used : ∃ i : Fin k, supports left (representation.decode i (witness left)) = true)
    (h_right_used : ∃ i : Fin k, supports right (representation.decode i (witness right)) = true)
    (h_disjoint : ∀ i : Fin k,
      supports left (representation.decode i (witness left)) = true →
        supports right (representation.decode i (witness left)) = false) :
    ∃ finish : MatrixState k,
      MatrixReachable (pps_ppm_vpm_step (k := k)) start finish := by
  rcases start with ⟨width, startMatrix⟩
  cases width with
  | zero =>
      cases left with
      | mk val isLt =>
          simp at isLt
  | succ n =>
      have h_start' : startMatrix = representation.witnessSupportMatrix witness supports := by
        simpa using h_start
      rw [h_start']
      refine ⟨⟨n,
        representation.witnessSupportMatrix
          (representation.orderedWitnessMergeWitness witness left right h_lt)
          (representation.orderedWitnessMergeSupports supports left right h_lt)⟩, ?_⟩
      exact representation.witnessSupportMatrix_ordered_vpm_reachable_by_pps_ppm_vpm
        witness supports left right h_lt h_same h_left_used h_right_used h_disjoint

theorem FinitePositiveMatrixRepresentation.witnessSupportMatrix_ordered_vpm_reachable_by_pps_ppm_vpm_state_of_valid
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (start : MatrixState k)
    (witness : Fin start.1 → Fin representation.width)
    (supports : Fin start.1 → Fin m → Bool)
    (h_start : start.2 = representation.witnessSupportMatrix witness supports)
    (h_used : representation.witnessSupportAllUsed witness supports)
    (h_pairwise : representation.witnessSupportPairwiseDisjoint witness supports)
    (left right : Fin start.1)
    (h_lt : left.1 < right.1)
    (h_same : witness left = witness right) :
    ∃ finish : MatrixState k,
      MatrixReachable (pps_ppm_vpm_step (k := k)) start finish := by
  exact representation.witnessSupportMatrix_ordered_vpm_reachable_by_pps_ppm_vpm_state
    start witness supports h_start left right h_lt h_same
    (h_used left) (h_used right) (h_pairwise left right h_same (by
      intro h_eq
      have h_val : left.1 = right.1 := by
        simpa using congrArg Fin.val h_eq
      omega))

theorem FinitePositiveMatrixRepresentation.witnessSupportMatrix_reachable_by_pps_ppm_vpm_state_of_valid_of_width_lt
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (start : MatrixState k)
    (witness : Fin start.1 → Fin representation.width)
    (supports : Fin start.1 → Fin m → Bool)
    (h_start : start.2 = representation.witnessSupportMatrix witness supports)
    (h_valid : representation.witnessSupportValid witness supports)
    (h_width_lt : representation.width < start.1) :
    ∃ finish : MatrixState k,
      MatrixReachable (pps_ppm_vpm_step (k := k)) start finish := by
  rcases exists_ordered_duplicate_of_lt (f := witness) h_width_lt with ⟨left, right, h_lt, h_same⟩
  exact representation.witnessSupportMatrix_ordered_vpm_reachable_by_pps_ppm_vpm_state_of_valid
    start witness supports h_start h_valid.1 h_valid.2 left right h_lt h_same

theorem FinitePositiveMatrixRepresentation.witnessSupportMatrix_reachable_to_valid_merge
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    {n : Nat}
    (witness : Fin (n + 1) → Fin representation.width)
    (supports : Fin (n + 1) → Fin m → Bool)
    (h_valid : representation.witnessSupportValid witness supports)
    (h_width_lt : representation.width < n + 1) :
    ∃ nextWitness : Fin n → Fin representation.width,
      ∃ nextSupports : Fin n → Fin m → Bool,
        MatrixReachable (pps_ppm_vpm_step (k := k))
          ⟨n + 1, representation.witnessSupportMatrix witness supports⟩
          ⟨n, representation.witnessSupportMatrix nextWitness nextSupports⟩ ∧
        representation.witnessSupportValid nextWitness nextSupports := by
  rcases exists_ordered_duplicate_of_lt (f := witness) h_width_lt with ⟨left, right, h_lt, h_same⟩
  let nextWitness := representation.orderedWitnessMergeWitness witness left right h_lt
  let nextSupports := representation.orderedWitnessMergeSupports supports left right h_lt
  refine Exists.intro nextWitness ?_
  refine Exists.intro nextSupports ?_
  refine And.intro ?_ ?_
  · exact representation.witnessSupportMatrix_ordered_vpm_reachable_by_pps_ppm_vpm_of_valid
      witness supports h_valid.1 h_valid.2 left right h_lt h_same
  · exact representation.witnessSupportValid_orderedMerge witness supports left right h_lt h_same h_valid

theorem FinitePositiveMatrixRepresentation.witnessSupportMatrix_reachable_to_valid_width
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (extra : Nat)
    (witness : Fin (representation.width + extra) → Fin representation.width)
    (supports : Fin (representation.width + extra) → Fin m → Bool)
    (h_valid : representation.witnessSupportValid witness supports) :
    ∃ finishWitness : Fin representation.width → Fin representation.width,
      ∃ finishSupports : Fin representation.width → Fin m → Bool,
        MatrixReachable (pps_ppm_vpm_step (k := k))
          ⟨representation.width + extra, representation.witnessSupportMatrix witness supports⟩
          ⟨representation.width,
            representation.witnessSupportMatrix finishWitness finishSupports⟩ ∧
        representation.witnessSupportValid finishWitness finishSupports := by
  induction extra with
  | zero =>
      refine ⟨witness, supports, ?_, h_valid⟩
      simpa using (MatrixReachable.refl
        (step := pps_ppm_vpm_step (k := k))
        ⟨representation.width,
          representation.witnessSupportMatrix witness supports⟩)
  | succ extra ih =>
      have h_width_lt : representation.width < representation.width + extra + 1 := by
        omega
      rcases representation.witnessSupportMatrix_reachable_to_valid_merge
          (witness := witness) (supports := supports) h_valid h_width_lt with
        ⟨nextWitness, nextSupports, h_step, h_next_valid⟩
      rcases ih nextWitness nextSupports h_next_valid with
        ⟨finishWitness, finishSupports, h_tail, h_finish_valid⟩
      refine ⟨finishWitness, finishSupports, MatrixReachable.trans h_step h_tail, h_finish_valid⟩

theorem FinitePositiveMatrixRepresentation.witnessSupportMatrix_reachable_to_valid_covered_merge
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    {n : Nat}
    (witness : Fin (n + 1) → Fin representation.width)
    (supports : Fin (n + 1) → Fin m → Bool)
    (h_valid : representation.witnessSupportValid witness supports)
    (h_covered : representation.witnessSupportWitnessCovered witness)
    (h_width_lt : representation.width < n + 1) :
    ∃ nextWitness : Fin n → Fin representation.width,
      ∃ nextSupports : Fin n → Fin m → Bool,
        MatrixReachable (pps_ppm_vpm_step (k := k))
          ⟨n + 1, representation.witnessSupportMatrix witness supports⟩
          ⟨n, representation.witnessSupportMatrix nextWitness nextSupports⟩ ∧
        representation.witnessSupportValid nextWitness nextSupports ∧
        representation.witnessSupportWitnessCovered nextWitness := by
  rcases exists_ordered_duplicate_of_lt (f := witness) h_width_lt with ⟨left, right, h_lt, h_same⟩
  let nextWitness := representation.orderedWitnessMergeWitness witness left right h_lt
  let nextSupports := representation.orderedWitnessMergeSupports supports left right h_lt
  refine Exists.intro nextWitness ?_
  refine Exists.intro nextSupports ?_
  refine And.intro ?_ ?_
  · exact representation.witnessSupportMatrix_ordered_vpm_reachable_by_pps_ppm_vpm_of_valid
      witness supports h_valid.1 h_valid.2 left right h_lt h_same
  · refine And.intro ?_ ?_
    · exact representation.witnessSupportValid_orderedMerge witness supports left right h_lt h_same h_valid
    · exact representation.witnessSupportWitnessCovered_orderedMerge witness left right h_lt h_same h_covered

theorem FinitePositiveMatrixRepresentation.witnessSupportMatrix_reachable_to_valid_covered_width
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (extra : Nat)
    (witness : Fin (representation.width + extra) → Fin representation.width)
    (supports : Fin (representation.width + extra) → Fin m → Bool)
    (h_valid : representation.witnessSupportValid witness supports)
    (h_covered : representation.witnessSupportWitnessCovered witness) :
    ∃ finishWitness : Fin representation.width → Fin representation.width,
      ∃ finishSupports : Fin representation.width → Fin m → Bool,
        MatrixReachable (pps_ppm_vpm_step (k := k))
          ⟨representation.width + extra, representation.witnessSupportMatrix witness supports⟩
          ⟨representation.width,
            representation.witnessSupportMatrix finishWitness finishSupports⟩ ∧
        representation.witnessSupportValid finishWitness finishSupports ∧
        representation.witnessSupportWitnessCovered finishWitness := by
  induction extra with
  | zero =>
      refine Exists.intro witness ?_
      refine Exists.intro supports ?_
      refine And.intro ?_ ?_
      · simpa using (MatrixReachable.refl
          (step := pps_ppm_vpm_step (k := k))
          ⟨representation.width,
            representation.witnessSupportMatrix witness supports⟩)
      · exact And.intro h_valid h_covered
  | succ extra ih =>
      have h_width_lt : representation.width < representation.width + extra + 1 := by
        omega
      rcases representation.witnessSupportMatrix_reachable_to_valid_covered_merge
          (witness := witness) (supports := supports) h_valid h_covered h_width_lt with
        ⟨nextWitness, nextSupports, h_step, h_rest⟩
      rcases h_rest with ⟨h_next_valid, h_next_covered⟩
      rcases ih nextWitness nextSupports h_next_valid h_next_covered with
        ⟨finishWitness, finishSupports, h_tail, h_finish_rest⟩
      rcases h_finish_rest with ⟨h_finish_valid, h_finish_covered⟩
      refine Exists.intro finishWitness ?_
      refine Exists.intro finishSupports ?_
      refine And.intro (MatrixReachable.trans h_step h_tail) ?_
      exact And.intro h_finish_valid h_finish_covered

theorem FinitePositiveMatrixRepresentation.witnessSupportMatrix_reachable_to_valid_covered_outputCovered_merge
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    {n : Nat}
    (witness : Fin (n + 1) → Fin representation.width)
    (supports : Fin (n + 1) → Fin m → Bool)
    (h_valid : representation.witnessSupportValid witness supports)
    (h_covered : representation.witnessSupportWitnessCovered witness)
    (h_output : representation.witnessSupportOutputCovered witness supports)
    (h_width_lt : representation.width < n + 1) :
    ∃ nextWitness : Fin n → Fin representation.width,
      ∃ nextSupports : Fin n → Fin m → Bool,
        MatrixReachable (pps_ppm_vpm_step (k := k))
          ⟨n + 1, representation.witnessSupportMatrix witness supports⟩
          ⟨n, representation.witnessSupportMatrix nextWitness nextSupports⟩ ∧
        representation.witnessSupportValid nextWitness nextSupports ∧
        representation.witnessSupportWitnessCovered nextWitness ∧
        representation.witnessSupportOutputCovered nextWitness nextSupports := by
  rcases exists_ordered_duplicate_of_lt (f := witness) h_width_lt with ⟨left, right, h_lt, h_same⟩
  let nextWitness := representation.orderedWitnessMergeWitness witness left right h_lt
  let nextSupports := representation.orderedWitnessMergeSupports supports left right h_lt
  refine Exists.intro nextWitness ?_
  refine Exists.intro nextSupports ?_
  refine And.intro ?_ ?_
  · exact representation.witnessSupportMatrix_ordered_vpm_reachable_by_pps_ppm_vpm_of_valid
      witness supports h_valid.1 h_valid.2 left right h_lt h_same
  · refine And.intro ?_ ?_
    · exact representation.witnessSupportValid_orderedMerge witness supports left right h_lt h_same h_valid
    · refine And.intro ?_ ?_
      · exact representation.witnessSupportWitnessCovered_orderedMerge witness left right h_lt h_same h_covered
      · exact representation.witnessSupportOutputCovered_orderedMerge witness supports left right h_lt h_same h_output

theorem FinitePositiveMatrixRepresentation.witnessSupportMatrix_reachable_to_valid_covered_outputCovered_width
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (extra : Nat)
    (witness : Fin (representation.width + extra) → Fin representation.width)
    (supports : Fin (representation.width + extra) → Fin m → Bool)
    (h_valid : representation.witnessSupportValid witness supports)
    (h_covered : representation.witnessSupportWitnessCovered witness)
    (h_output : representation.witnessSupportOutputCovered witness supports) :
    ∃ finishWitness : Fin representation.width → Fin representation.width,
      ∃ finishSupports : Fin representation.width → Fin m → Bool,
        MatrixReachable (pps_ppm_vpm_step (k := k))
          ⟨representation.width + extra, representation.witnessSupportMatrix witness supports⟩
          ⟨representation.width,
            representation.witnessSupportMatrix finishWitness finishSupports⟩ ∧
        representation.witnessSupportValid finishWitness finishSupports ∧
        representation.witnessSupportWitnessCovered finishWitness ∧
        representation.witnessSupportOutputCovered finishWitness finishSupports := by
  induction extra with
  | zero =>
      refine Exists.intro witness ?_
      refine Exists.intro supports ?_
      refine And.intro ?_ ?_
      · simpa using (MatrixReachable.refl
          (step := pps_ppm_vpm_step (k := k))
          ⟨representation.width,
            representation.witnessSupportMatrix witness supports⟩)
      · exact And.intro h_valid (And.intro h_covered h_output)
  | succ extra ih =>
      have h_width_lt : representation.width < representation.width + extra + 1 := by
        omega
      rcases representation.witnessSupportMatrix_reachable_to_valid_covered_outputCovered_merge
          (witness := witness) (supports := supports) h_valid h_covered h_output h_width_lt with
        ⟨nextWitness, nextSupports, h_step, h_rest⟩
      rcases h_rest with ⟨h_next_valid, h_next_rest⟩
      rcases h_next_rest with ⟨h_next_covered, h_next_output⟩
      rcases ih nextWitness nextSupports h_next_valid h_next_covered h_next_output with
        ⟨finishWitness, finishSupports, h_tail, h_finish_rest⟩
      rcases h_finish_rest with ⟨h_finish_valid, h_finish_rest⟩
      rcases h_finish_rest with ⟨h_finish_covered, h_finish_output⟩
      refine Exists.intro finishWitness ?_
      refine Exists.intro finishSupports ?_
      refine And.intro (MatrixReachable.trans h_step h_tail) ?_
      exact And.intro h_finish_valid (And.intro h_finish_covered h_finish_output)

theorem FinitePositiveMatrixRepresentation.witnessSupportMatrix_reachable_to_valid_covered_state_width
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (extra : Nat)
    (start : MatrixState k)
    (witness : Fin start.1 → Fin representation.width)
    (supports : Fin start.1 → Fin m → Bool)
    (h_start : start.2 = representation.witnessSupportMatrix witness supports)
    (h_valid : representation.witnessSupportValid witness supports)
    (h_covered : representation.witnessSupportWitnessCovered witness)
    (h_width : start.1 = representation.width + extra) :
    ∃ finishWitness : Fin representation.width → Fin representation.width,
      ∃ finishSupports : Fin representation.width → Fin m → Bool,
        MatrixReachable (pps_ppm_vpm_step (k := k)) start
          ⟨representation.width,
            representation.witnessSupportMatrix finishWitness finishSupports⟩ ∧
        representation.witnessSupportValid finishWitness finishSupports ∧
        representation.witnessSupportWitnessCovered finishWitness := by
  cases start with
  | mk width startMatrix =>
      dsimp at h_width
      subst width
      have h_start' : startMatrix = representation.witnessSupportMatrix witness supports := by
        simpa using h_start
      rcases representation.witnessSupportMatrix_reachable_to_valid_covered_width
          extra witness supports h_valid h_covered with
        ⟨finishWitness, finishSupports, h_reach, h_finish_rest⟩
      refine Exists.intro finishWitness ?_
      refine Exists.intro finishSupports ?_
      refine And.intro ?_ h_finish_rest
      simpa [h_start'] using h_reach

theorem FinitePositiveMatrixRepresentation.witnessSupportMatrix_reachable_to_valid_covered_outputCovered_state_width
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (extra : Nat)
    (start : MatrixState k)
    (witness : Fin start.1 → Fin representation.width)
    (supports : Fin start.1 → Fin m → Bool)
    (h_start : start.2 = representation.witnessSupportMatrix witness supports)
    (h_valid : representation.witnessSupportValid witness supports)
    (h_covered : representation.witnessSupportWitnessCovered witness)
    (h_output : representation.witnessSupportOutputCovered witness supports)
    (h_width : start.1 = representation.width + extra) :
    ∃ finishWitness : Fin representation.width → Fin representation.width,
      ∃ finishSupports : Fin representation.width → Fin m → Bool,
        MatrixReachable (pps_ppm_vpm_step (k := k)) start
          ⟨representation.width,
            representation.witnessSupportMatrix finishWitness finishSupports⟩ ∧
        representation.witnessSupportValid finishWitness finishSupports ∧
        representation.witnessSupportWitnessCovered finishWitness ∧
        representation.witnessSupportOutputCovered finishWitness finishSupports := by
  cases start with
  | mk width startMatrix =>
      dsimp at h_width
      subst width
      have h_start' : startMatrix = representation.witnessSupportMatrix witness supports := by
        simpa using h_start
      rcases representation.witnessSupportMatrix_reachable_to_valid_covered_outputCovered_width
          extra witness supports h_valid h_covered h_output with
        ⟨finishWitness, finishSupports, h_reach, h_finish_rest⟩
      refine Exists.intro finishWitness ?_
      refine Exists.intro finishSupports ?_
      refine And.intro ?_ h_finish_rest
      simpa [h_start'] using h_reach

theorem FinitePositiveMatrixRepresentation.liftedMatrix_entry_eq_witnessSupportMatrix
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (i : Fin k) (j : Fin representation.activeLiftedWidth) :
    representation.liftedMatrix.entry i j =
      (representation.witnessSupportMatrix
        (fun j => (representation.activeLiftedOutput j).2)
        (fun j y => decide (y = (representation.activeLiftedOutput j).1))).entry i j := by
  let yw := representation.activeLiftedOutput j
  calc
    representation.liftedMatrix.entry i j = representation.liftedChannel i yw := by
      simpa [yw] using representation.liftedMatrix_entry_eq i j
    _ = if representation.decode i yw.2 = yw.1 then representation.pW yw.2 else 0 := by
      rfl
    _ = if decide (representation.decode i yw.2 = yw.1) then representation.pW yw.2 else 0 := by
      by_cases h_decode : representation.decode i yw.2 = yw.1
      · simp [h_decode]
      · simp [h_decode]
    _ = (representation.witnessSupportMatrix
          (fun j => (representation.activeLiftedOutput j).2)
          (fun j y => decide (y = (representation.activeLiftedOutput j).1))).entry i j := by
      rfl

theorem FinitePositiveMatrixRepresentation.liftedMatrix_eq_witnessSupportMatrix
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M) :
    representation.liftedMatrix =
      representation.witnessSupportMatrix
        (fun j => (representation.activeLiftedOutput j).2)
        (fun j y => decide (y = (representation.activeLiftedOutput j).1)) := by
  apply ConditionalProbabilityMatrix.ext
  intro i j
  exact representation.liftedMatrix_entry_eq_witnessSupportMatrix i j

theorem FinitePositiveMatrixRepresentation.activeLiftedOutput_witnessSupport_used
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (j : Fin representation.activeLiftedWidth) :
    ∃ i : Fin k,
      (decide (representation.decode i (representation.activeLiftedOutput j).2 =
        (representation.activeLiftedOutput j).1) : Bool) = true := by
  rcases representation.activeLiftedOutput_used j with ⟨i, h_decode⟩
  refine ⟨i, ?_⟩
  simp [h_decode]

theorem FinitePositiveMatrixRepresentation.liftedMatrix_witnessSupportAllUsed
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M) :
    representation.witnessSupportAllUsed
      (fun j => (representation.activeLiftedOutput j).2)
      (fun j y => decide (y = (representation.activeLiftedOutput j).1)) := by
  intro j
  exact representation.activeLiftedOutput_witnessSupport_used j

theorem FinitePositiveMatrixRepresentation.same_w_activeLiftedOutputs_witnessSupport_disjoint
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (j₁ j₂ : Fin representation.activeLiftedWidth)
    (h_base_ne : (representation.activeLiftedOutput j₁).1 ≠ (representation.activeLiftedOutput j₂).1) :
    ∀ i : Fin k,
      (decide (representation.decode i (representation.activeLiftedOutput j₁).2 =
        (representation.activeLiftedOutput j₁).1) : Bool) = true →
      (decide (representation.decode i (representation.activeLiftedOutput j₁).2 =
        (representation.activeLiftedOutput j₂).1) : Bool) = false := by
  intro i h_left
  have h_decode_left : representation.decode i (representation.activeLiftedOutput j₁).2 =
      (representation.activeLiftedOutput j₁).1 := by
    by_cases h_eq : representation.decode i (representation.activeLiftedOutput j₁).2 =
        (representation.activeLiftedOutput j₁).1
    · exact h_eq
    · simp [h_eq] at h_left
  by_cases h_right : representation.decode i (representation.activeLiftedOutput j₁).2 =
      (representation.activeLiftedOutput j₂).1
  · have h_contra : (representation.activeLiftedOutput j₁).1 = (representation.activeLiftedOutput j₂).1 := by
      calc
        (representation.activeLiftedOutput j₁).1 = representation.decode i (representation.activeLiftedOutput j₁).2 :=
          h_decode_left.symm
        _ = (representation.activeLiftedOutput j₂).1 := h_right
    exact False.elim (h_base_ne h_contra)
  · simp [h_right]

theorem FinitePositiveMatrixRepresentation.liftedMatrix_witnessSupportPairwiseDisjoint
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M) :
    representation.witnessSupportPairwiseDisjoint
      (fun j => (representation.activeLiftedOutput j).2)
      (fun j y => decide (y = (representation.activeLiftedOutput j).1)) := by
  intro j₁ j₂ h_w h_ne i h_left
  exact representation.same_w_activeLiftedOutputs_witnessSupport_disjoint j₁ j₂
    (representation.same_w_activeLiftedOutputs_base_ne j₁ j₂ h_w h_ne) i h_left

theorem FinitePositiveMatrixRepresentation.liftedMatrix_witnessSupportValid
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M) :
    representation.witnessSupportValid
      (fun j => (representation.activeLiftedOutput j).2)
      (fun j y => decide (y = (representation.activeLiftedOutput j).1)) := by
  exact ⟨representation.liftedMatrix_witnessSupportAllUsed,
    representation.liftedMatrix_witnessSupportPairwiseDisjoint⟩

theorem FinitePositiveMatrixRepresentation.liftedMatrix_witnessSupportWitnessCovered
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (i : Fin k) :
    representation.witnessSupportWitnessCovered
      (fun j => (representation.activeLiftedOutput j).2) := by
  intro w
  rcases representation.witness_has_activeLiftedIndex i w with ⟨j, hj⟩
  refine ⟨j, ?_⟩
  simp [hj]

theorem FinitePositiveMatrixRepresentation.liftedMatrix_witnessSupportOutputCovered
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M) :
    representation.witnessSupportOutputCovered
      (fun j => (representation.activeLiftedOutput j).2)
      (fun j y => decide (y = (representation.activeLiftedOutput j).1)) := by
  intro y w h_used
  rcases representation.used_lifted_output_has_active_index (y, w) h_used with ⟨j, hj⟩
  refine ⟨j, ?_, ?_⟩
  · simp [hj]
  · simp [hj]

theorem FinitePositiveMatrixRepresentation.liftedMatrix_reachable_to_valid_covered_width_of_row
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (i : Fin k) :
    ∃ finishWitness : Fin representation.width → Fin representation.width,
      ∃ finishSupports : Fin representation.width → Fin m → Bool,
        MatrixReachable (pps_ppm_vpm_step (k := k))
          ⟨representation.activeLiftedWidth, representation.liftedMatrix⟩
          ⟨representation.width,
            representation.witnessSupportMatrix finishWitness finishSupports⟩ ∧
        representation.witnessSupportValid finishWitness finishSupports ∧
        representation.witnessSupportWitnessCovered finishWitness := by
  have h_le : representation.width ≤ representation.activeLiftedWidth :=
    representation.width_le_activeLiftedWidth_of_row i
  have h_width : representation.activeLiftedWidth =
      representation.width + (representation.activeLiftedWidth - representation.width) := by
    symm
    exact Nat.add_sub_of_le h_le
  exact representation.witnessSupportMatrix_reachable_to_valid_covered_state_width
    (representation.activeLiftedWidth - representation.width)
    ⟨representation.activeLiftedWidth, representation.liftedMatrix⟩
    (fun j => (representation.activeLiftedOutput j).2)
    (fun j y => decide (y = (representation.activeLiftedOutput j).1))
    representation.liftedMatrix_eq_witnessSupportMatrix
    representation.liftedMatrix_witnessSupportValid
    (representation.liftedMatrix_witnessSupportWitnessCovered i)
    h_width

theorem FinitePositiveMatrixRepresentation.liftedMatrix_reachable_to_valid_covered_outputCovered_width_of_row
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (i : Fin k) :
    ∃ finishWitness : Fin representation.width → Fin representation.width,
      ∃ finishSupports : Fin representation.width → Fin m → Bool,
        MatrixReachable (pps_ppm_vpm_step (k := k))
          ⟨representation.activeLiftedWidth, representation.liftedMatrix⟩
          ⟨representation.width,
            representation.witnessSupportMatrix finishWitness finishSupports⟩ ∧
        representation.witnessSupportValid finishWitness finishSupports ∧
        representation.witnessSupportWitnessCovered finishWitness ∧
        representation.witnessSupportOutputCovered finishWitness finishSupports := by
  have h_le : representation.width ≤ representation.activeLiftedWidth :=
    representation.width_le_activeLiftedWidth_of_row i
  have h_width : representation.activeLiftedWidth =
      representation.width + (representation.activeLiftedWidth - representation.width) := by
    symm
    exact Nat.add_sub_of_le h_le
  exact representation.witnessSupportMatrix_reachable_to_valid_covered_outputCovered_state_width
    (representation.activeLiftedWidth - representation.width)
    ⟨representation.activeLiftedWidth, representation.liftedMatrix⟩
    (fun j => (representation.activeLiftedOutput j).2)
    (fun j y => decide (y = (representation.activeLiftedOutput j).1))
    representation.liftedMatrix_eq_witnessSupportMatrix
    representation.liftedMatrix_witnessSupportValid
    (representation.liftedMatrix_witnessSupportWitnessCovered i)
    representation.liftedMatrix_witnessSupportOutputCovered
    h_width

theorem FinitePositiveMatrixRepresentation.liftedMatrix_reachable_to_valid_covered_outputCovered_allTrue_width_of_row
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (i : Fin k) :
    ∃ finishWitness : Fin representation.width → Fin representation.width,
      ∃ finishSupports : Fin representation.width → Fin m → Bool,
        MatrixReachable (pps_ppm_vpm_step (k := k))
          ⟨representation.activeLiftedWidth, representation.liftedMatrix⟩
          ⟨representation.width,
            representation.witnessSupportMatrix finishWitness finishSupports⟩ ∧
        representation.witnessSupportValid finishWitness finishSupports ∧
        representation.witnessSupportWitnessCovered finishWitness ∧
        representation.witnessSupportOutputCovered finishWitness finishSupports ∧
        (∀ j : Fin representation.width,
          column_pattern (representation.witnessSupportMatrix finishWitness finishSupports) j =
            fun _ => true) := by
  rcases representation.liftedMatrix_reachable_to_valid_covered_outputCovered_width_of_row i with
    ⟨finishWitness, finishSupports, h_reach, h_rest⟩
  rcases h_rest with ⟨h_valid, h_rest⟩
  rcases h_rest with ⟨h_covered, h_output⟩
  refine ⟨finishWitness, finishSupports, h_reach, h_valid, h_covered, h_output, ?_⟩
  intro j
  exact representation.witnessSupportMatrix_column_pattern_true_of_covered_outputCovered
    finishWitness finishSupports h_covered h_output j

theorem FinitePositiveMatrixRepresentation.liftedMatrix_reachable_to_one_vector_of_row
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (i : Fin k) :
    MatrixReachable (pps_ppm_vpm_step (k := k))
      ⟨representation.activeLiftedWidth, representation.liftedMatrix⟩
      ⟨1, one_vector_matrix k⟩ := by
  rcases representation.liftedMatrix_reachable_to_valid_covered_outputCovered_allTrue_width_of_row i with
    ⟨finishWitness, finishSupports, h_reach, _, h_covered, h_output, _⟩
  exact MatrixReachable.trans h_reach
    (representation.witnessSupportMatrix_reachable_to_one_vector_of_covered_outputCovered
      finishWitness finishSupports h_covered h_output)

theorem FinitePositiveMatrixRepresentation.liftedMatrix_reachable_to_witnessSupportMerge_of_width_lt_activeLiftedWidth
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (h_width_lt : representation.width < representation.activeLiftedWidth) :
    ∃ finish : MatrixState k,
      MatrixReachable (pps_ppm_vpm_step (k := k))
        ⟨representation.activeLiftedWidth, representation.liftedMatrix⟩ finish := by
  exact representation.witnessSupportMatrix_reachable_by_pps_ppm_vpm_state_of_valid_of_width_lt
    ⟨representation.activeLiftedWidth, representation.liftedMatrix⟩
    (fun j => (representation.activeLiftedOutput j).2)
    (fun j y => decide (y = (representation.activeLiftedOutput j).1))
    representation.liftedMatrix_eq_witnessSupportMatrix
    representation.liftedMatrix_witnessSupportValid
    h_width_lt

theorem FinitePositiveMatrixRepresentation.same_w_activeLiftedOutputs_reachable_to_witnessSupportMerge
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (j₁ j₂ : Fin representation.activeLiftedWidth)
    (h_lt : j₁.1 < j₂.1)
    (h_base_ne : (representation.activeLiftedOutput j₁).1 ≠ (representation.activeLiftedOutput j₂).1)
    (h_w : (representation.activeLiftedOutput j₁).2 = (representation.activeLiftedOutput j₂).2) :
    ∃ finish : MatrixState k,
      MatrixReachable (pps_ppm_vpm_step (k := k))
        ⟨representation.activeLiftedWidth, representation.liftedMatrix⟩ finish := by
  exact representation.witnessSupportMatrix_ordered_vpm_reachable_by_pps_ppm_vpm_state
    ⟨representation.activeLiftedWidth, representation.liftedMatrix⟩
    (fun j => (representation.activeLiftedOutput j).2)
    (fun j y => decide (y = (representation.activeLiftedOutput j).1))
    representation.liftedMatrix_eq_witnessSupportMatrix
    j₁ j₂ h_lt h_w
    (representation.activeLiftedOutput_witnessSupport_used j₁)
    (representation.activeLiftedOutput_witnessSupport_used j₂)
    (representation.same_w_activeLiftedOutputs_witnessSupport_disjoint j₁ j₂ h_base_ne)

noncomputable def FinitePositiveMatrixRepresentation.witnessValueMatrix
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M) :
    ConditionalProbabilityMatrix k representation.width :=
  { entry := fun _ w => representation.pW w
    nonnegative := by
      intro _ w
      exact Rat.le_of_lt (representation.positive w) }

theorem FinitePositiveMatrixRepresentation.witnessValueMatrix_entry_eq
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (i : Fin k) (w : Fin representation.width) :
    representation.witnessValueMatrix.entry i w = representation.pW w := by
  rfl

theorem FinitePositiveMatrixRepresentation.witnessValueMatrix_entry_eq_witnessSupportMatrix
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (i : Fin k) (w : Fin representation.width) :
    representation.witnessValueMatrix.entry i w =
      (representation.witnessSupportMatrix
        (fun w => w)
        (fun w y => decide (∃ i : Fin k, representation.decode i w = y))).entry i w := by
  have h_support :
      (fun w y => decide (∃ i : Fin k, representation.decode i w = y)) w (representation.decode i w) = true := by
    simp
  calc
    representation.witnessValueMatrix.entry i w = representation.pW w := by rfl
    _ = if (fun w y => decide (∃ i : Fin k, representation.decode i w = y)) w (representation.decode i w)
        then representation.pW w else 0 := by
          simp
    _ = (representation.witnessSupportMatrix
          (fun w => w)
          (fun w y => decide (∃ i : Fin k, representation.decode i w = y))).entry i w := by
          rfl

theorem FinitePositiveMatrixRepresentation.witnessValueMatrix_eq_witnessSupportMatrix
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M) :
    representation.witnessValueMatrix =
      representation.witnessSupportMatrix
        (fun w => w)
        (fun w y => decide (∃ i : Fin k, representation.decode i w = y)) := by
  apply ConditionalProbabilityMatrix.ext
  intro i w
  exact representation.witnessValueMatrix_entry_eq_witnessSupportMatrix i w

theorem FinitePositiveMatrixRepresentation.witnessValueMatrix_column_pattern
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M)
    (w : Fin representation.width) :
    column_pattern representation.witnessValueMatrix w = fun _ => true := by
  funext i
  have h_pos : 0 < representation.witnessValueMatrix.entry i w := by
    simpa [FinitePositiveMatrixRepresentation.witnessValueMatrix] using representation.positive w
  simp [column_pattern, h_pos]

theorem FinitePositiveMatrixRepresentation.witnessValueMatrix_is_singular
    {k m : Nat} {M : ConditionalProbabilityMatrix k m}
    (representation : FinitePositiveMatrixRepresentation M) :
    matrix_is_singular representation.witnessValueMatrix := by
  intro w i₁ i₂ _ _
  rfl

-- THEOREM 1: Main Characterization
-- A singular conditional matrix is perfectly representable iff
-- the vector 1_k can be obtained from it via PPM, PPS, and VPM operations
axiom finite_positive_representation_of_matrix_perfectly_representable {k m : Nat}
    (M : ConditionalProbabilityMatrix k m)
    (h_repr : matrix_perfectly_representable M) :
    FinitePositiveMatrixRepresentation M

axiom reducible_to_one_vector_of_finite_positive_representation {k m : Nat}
    (M : ConditionalProbabilityMatrix k m)
    (h_singular : matrix_is_singular M)
    (representation : FinitePositiveMatrixRepresentation M) :
    reducible_to_one_vector M

theorem perfect_representability_implies_reducible_to_one_vector {k m : Nat}
    (M : ConditionalProbabilityMatrix k m)
    (h_singular : matrix_is_singular M) :
    matrix_perfectly_representable M → reducible_to_one_vector M := by
  intro h_repr
  exact reducible_to_one_vector_of_finite_positive_representation M h_singular
    (finite_positive_representation_of_matrix_perfectly_representable M h_repr)

theorem perfect_representability_characterization_by_reduction {k m : Nat}
    (M : ConditionalProbabilityMatrix k m)
    (h_singular : matrix_is_singular M) :
    Iff (matrix_perfectly_representable M) (reducible_to_one_vector M) := by
  constructor
  · exact perfect_representability_implies_reducible_to_one_vector M h_singular
  · exact reducible_to_one_vector_implies_perfectly_representable M

theorem theorem_1_characterization {k m : Nat}
    (M : ConditionalProbabilityMatrix k m)
    (h_singular : matrix_is_singular M) :
    Iff (matrix_perfectly_representable M) (reducible_to_one_vector M) := by
  exact perfect_representability_characterization_by_reduction M h_singular

axiom satisfies_corresponding_primal_lp {k m : Nat}
  (M : ConditionalProbabilityMatrix k m) : Prop

def primal_linear_program_attains_value_one {k m : Nat}
  (M : ConditionalProbabilityMatrix k m) : Prop :=
  matrix_is_singular M ∧ satisfies_corresponding_primal_lp M

-- THEOREM 2: Linear Programming Characterization
-- A matrix is perfectly representable iff the LP
--   max 1_R · x = 1 subject to x ≥ 0 and Hx ≤ v
-- holds for the corresponding value vector v and incidence matrix H.
axiom perfect_representability_characterization_by_primal_lp {k m : Nat}
  (M : ConditionalProbabilityMatrix k m) :
  Iff (matrix_perfectly_representable M) (primal_linear_program_attains_value_one M)

theorem theorem_2_linear_program {k m : Nat}
  (M : ConditionalProbabilityMatrix k m) :
  Iff (matrix_perfectly_representable M) (primal_linear_program_attains_value_one M) := by
  exact perfect_representability_characterization_by_primal_lp M

end PerfectRepresentability
