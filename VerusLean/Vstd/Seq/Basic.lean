import VerusLean.Vstd.Seq.Defs

namespace Vstd

namespace VSeqLikeF

/-! # lawful sequences -/
open LawfulVSeqLikeF

variable {L : Type u → Type u} [VSeqLikeF L] [LawfulVSeqLikeF L]

theorem len_eq_zero_iff {α : Type u} (s : L α) : length s = 0 ↔ s = empty := by
  constructor
  · intro h
    apply LawfulVSeqLikeF.ext; constructor
    · rw [h, length_empty]
    · intro i hi; rw [h] at hi; contradiction
  · intro h; rw [h, length_empty]

theorem len_pos_iff_nonempty {α} (s : L α) : length s > 0 ↔ s ≠ empty := by
  constructor
  . intro h heq
    rw [heq, length_empty] at h
    contradiction
  . intro h_ne; false_or_by_contra; rename_i h_le_zero
    have h_len_zero := Nat.le_zero.mp (Nat.ge_of_not_lt h_le_zero)
    have h_s_empty := (len_eq_zero_iff s).mp h_len_zero
    exact h_ne h_s_empty

theorem filter_len {α : Type u} [Inhabited α] (s : L α) (p : α → Bool) :
  length (filter s p) ≤ length s := by
  let P (n : Nat) := ∀ (s' : L α), length s' = n → length (filter s' p) ≤ n
  suffices h_all_n : ∀ (n : Nat), P n by
    exact h_all_n (length s) s rfl
  intro n
  apply Nat.strongRecOn (motive := P) n
  intro n_step ih
  intro s_current h_len_eq_n_step

  by_cases h_s_is_empty : s_current = empty
  · rw [h_s_is_empty, filter_empty]; simp [length_empty]
  · let s' := extract s_current 0 (length s_current - 1)
    have h_len := (len_pos_iff_nonempty s_current).mpr h_s_is_empty
    have h_decomp : push s' (last s_current) = s_current := by
      have xx := eq_push_last s_current h_len
      rw [dropLast_eq] at xx
      exact xx
      exact h_len
    rw [←h_decomp]
    rw [filter_push]
    have hl : length s_current = length s' + 1 := by
        rw [←h_decomp, length_push]
    cases h_p_x : p (last s_current) with
    | true =>
      simp [h_p_x]
      rw [length_push]
      rw [← h_len_eq_n_step, hl]
      -- Goal is: len (filter s' p) + 1 ≤ len s' + 1
      have h_len_lt : length s' < n_step := by
        simp [←h_len_eq_n_step, hl]
      -- Apply the inductive hypothesis `ih` to `s'`.
      have ih_applies := ih (length s') h_len_lt s' rfl
      exact Nat.add_le_add_right ih_applies 1
    | false =>
      -- If p (last s_current) is false, then we do not push it.
      simp [h_p_x]
      rw [←h_len_eq_n_step, hl]
      -- Goal is: len (filter s' p) ≤ len s' + 1
      have h_len_lt : length s' < n_step := by
        rw [←h_len_eq_n_step, ←h_decomp, length_push]
        exact Nat.lt_succ_self _
      have ih_applies := ih (length s') h_len_lt s' rfl
      -- The IH gives `len (filter s' p) ≤ len s'`, and `len s' ≤ len s' + 1`.
      exact Nat.le_trans ih_applies (Nat.le_succ (length s'))

theorem filter_pred {α : Type u} [Inhabited α] (s : L α) (p : α → Bool) (h : i < length (filter s p)) :
  p (get (filter s p) i h) := by
  -- exact filter_pred s p h
  sorry

theorem filter_contains {α : Type u} [Inhabited α] (s : L α) (p : α → Bool) (i : Nat)
  (h : i < length (filter s p)) (hp : p (get (filter s p) i h)) :
  get (filter s p) i h ∈ s := by
  simp only [mem_iff_exists_get]
  sorry

theorem filter_distributes_over_add {α : Type u} (s₁ s₂ : L α) (p : α → Bool) :
  filter (s₁ + s₂) p = filter s₁ p + filter s₂ p := by
  apply LawfulVSeqLikeF.ext
  constructor
  . simp [length_add]
    sorry
  . sorry

theorem add_empty_left {α : Type u} (s : L α) :
  empty + s = s := by
  apply LawfulVSeqLikeF.ext
  constructor
  . simp [length_add, length_empty]
  . intro i h
    simp [get?_add, length_empty, Nat.zero_le]

theorem add_empty_right {α : Type u} (s : L α) :
  s + empty = s := by
  apply LawfulVSeqLikeF.ext
  constructor
  . simp [length_add, length_empty]
  . intro i h
    simp [length_add, length_empty] at h
    simp [get?_add, length_empty, h]

theorem push_distributes_over_add {α : Type u} (s₁ s₂ : L α) (a : α) :
  push (s₁ + s₂) a = s₁ + push s₂ a := by
  apply LawfulVSeqLikeF.ext
  constructor
  . simp only [length_push, length_add, Nat.add_assoc]
  . intro i h
    rw [length_push, length_add] at h
    simp only [get?_push, length_add, get?_add]
    by_cases h₁ : i < length s₁
    . simp [h₁] -- get? s₁ i = get? s₁ i
      intro h₂
      rw [h₂] at h₁
      have h₃ : length s₁ + length s₂ ≥ length s₁ := by simp [Nat.zero_le]
      have := (Nat.not_le_of_lt h₁) h₃
      contradiction
    . by_cases h₂ : i = length s₁ + length s₂
      . have h₃ : ¬ length s₁ + length s₂ < length s₁ := by simp [Nat.zero_le]
        simp [h₂, h₃, Nat.add_sub_cancel_left]
      . simp [h₁, h₂]
        have h₃ : ¬ i - length s₁ = length s₂ := by
          intro h_contra
          have h_le : length s₁ ≤ i := Nat.not_lt.mp h₁
          have h_eq_add : i = length s₂ + length s₁ := (Nat.sub_eq_iff_eq_add h_le).mp h_contra
          rw [Nat.add_comm] at h_eq_add
          exact h₂ h_eq_add
        simp [h₃]

-- theorem index_of_first

-- theorem index_of_last

theorem gt_zero_implies_ge_one (n : Nat) (h : n > 0) : n ≥ 1 := by
  have := Nat.succ_le_of_lt h
  exact this

theorem drop_last_distributes_over_add {α : Type u} (s₁ s₂ : L α) (h : length s₂ > 0) :
  dropLast (s₁ + s₂) = s₁ + dropLast s₂ := by
  apply LawfulVSeqLikeF.ext
  constructor
  . have h12 : length (s₁ + s₂) > 0 := by
      have h' : 0 < length s₂ := by simp [h]
      rw [length_add, Nat.add_comm (length s₁)]
      exact Nat.add_pos_left h' (length s₁)
    rw [dropLast_eq (s₁ + s₂) h12]
    rw [length_extract]
    . rw [length_add, length_add]
      rw [dropLast_eq s₂ h]
      have h_len := length_extract s₂ 0 (length s₂ - 1)
        (h₁ := Nat.zero_le (length s₂ - 1))
        (h₂ := Nat.sub_le (length s₂) 1)
      simp [h_len]
      rw [Nat.add_sub_assoc]
      simp only [Nat.succ_le_of_lt h]
    . simp [Nat.succ_le_of_lt h12, Nat.sub_le]
    . simp
  . intro i h
    rw [dropLast_eq]
    .
      sorry
    . sorry

-- theorem to_multiset

-- theorem insert

-- theorem remove

theorem fold_left_split {α β : Type u} (s : L α) (b : β) (f : β → α → β) (k : Nat) (h : k ≤ length s) :
  foldLeft (extract s k (length s)) (foldLeft (extract s 0 k) b f) f = foldLeft s b f := by
  sorry

-- `foldLeft` and `foldLeftAlt` are equivalent.
theorem fold_left_alt {α β : Type u} (s : L α) (b : β) (f : β → α → β) :
  foldLeft s b f = foldLeftAlt s b f := by
  sorry

theorem fold_right_split {α β : Type u} (s : L α) (f : α → β → β) (b : β) (k : Nat) (h : k ≤ length s) :
  foldRight (extract s 0 k) f (foldRight (extract s k (length s)) f b) = foldRight s f b := by
  sorry

theorem fold_right_commute_one {α β : Type u} (s : L α) (a : α) (f : α → β → β) (v : β) (h : FoldCommutativeR f) :
  foldRight s f (f a v) = f a (foldRight s f v) := by
  sorry

-- `foldRight` and `foldRightAlt` are equivalent.
theorem fold_right_alt {α β : Type u} (s : L α) (f : α → β → β) (b : β) :
  foldRight s f b = foldRightAlt s f b := by
  sorry

-- theorem multiset_has_no_duplicates

theorem add_last_back {α : Type u} [Inhabited α] (s : L α):
  push (dropLast s) (last s) = s := by
  sorry

theorem indexing_implies_membership {α : Type u} [Inhabited α] (s : L α) (f : α → Bool)
  (h : ∀ i < length s, f (get! s i)) : ∀ x, x ∈ s → f x := by
  sorry

theorem membership_implies_indexing {α : Type u} [Inhabited α] (s : L α) (f : α → Bool)
  (h : ∀ x, x ∈ s → f x) : ∀ i < length s, f (get! s i) := by
  sorry

theorem split_at_index {α : Type u} (s : L α) (pos : Nat) (h : pos ≤ length s) :
  extract s 0 pos + extract s pos (length s) = s := by
  sorry

theorem element_from_slice {α : Type u} [Inhabited α] (s : L α) (new : L α) (a : Nat) (b : Nat) (pos : Nat)
  (h₁ : a ≤ b && b ≤ length s) (h₃ : new = extract s a b) (h₄ : a ≤ pos && pos < b) :
  pos - a < length new ∧ get! new (pos - a) = get! s pos := by
  sorry

theorem slice_of_slice {α : Type u} (s : L α) (s₁ e₁ s₂ e₂ : Nat)
  (h₁ : s₁ ≤ e₁ && e₁ ≤ length s) (h₂ : s₂ ≤ e₂ && e₂ ≤ e₁ - s₁) :
  extract (extract s s₁ e₁) s₂ e₂ = extract s (s₁ + s₂) (s₁ + e₂) := by
  sorry

-- theorem unique_seq_to_set

-- theorem cardinality_of_set

-- Omit some theorems for now

end VSeqLikeF


end Vstd
