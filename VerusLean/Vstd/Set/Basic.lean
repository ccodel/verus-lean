import VerusLean.Vstd.Set.Defs

namespace Vstd

namespace VSetLikeF

open LawfulVSetLikeF

variable {S : Type u → Type v} [VSetLikeF S] [LawfulVSetLikeF S] {α β : Type u}

omit [LawfulVSetLikeF S] in
theorem mem_or_not_mem (a : α) (s : S α) : a ∈ s ∨ a ∉ s := by
  by_cases h : a ∈ s
  · exact Or.inl h
  · exact Or.inr h

/-! # subset -/

@[simp]
theorem empty_subset (s : S α) : ∅ ⊆ s := by
  simp only [subset_iff, not_mem_empty, false_implies, implies_true]

@[simp]
theorem subset_empty_iff {s : S α} : s ⊆ ∅ ↔ s = ∅ := by
  simp only [subset_iff, not_mem_empty, imp_false]
  constructor
  · intro h
    ext a
    simp only [not_mem_empty, iff_false]
    exact h a
  · rintro rfl
    simp only [not_mem_empty, not_false_eq_true, implies_true]

theorem eq_empty_iff_forall_not_mem {s : S α} : s = ∅ ↔ ∀ x, x ∉ s := by
  have := Iff.symm <| subset_empty_iff (s := s)
  simp only [subset_iff, not_mem_empty, imp_false] at this
  exact this

theorem ne_empty_iff_exists_mem {s : S α} : s ≠ ∅ ↔ ∃ x, x ∈ s := by
  constructor
  · intro h
    have := mt (eq_empty_iff_forall_not_mem (s := s)).mpr h
    simp only [Classical.not_forall, Classical.not_not] at this
    exact this
  · rintro ⟨x, hx⟩ rfl
    exact not_mem_empty x hx

theorem eq_of_subset_of_subset {s₁ s₂ : S α} : s₁ ⊆ s₂ → s₂ ⊆ s₁ → s₁ = s₂ := by
  simp only [subset_iff]
  intro h₁ h₂
  ext x
  exact ⟨h₁ x, h₂ x⟩

theorem subset_trans {s₁ s₂ s₃ : S α} : s₁ ⊆ s₂ → s₂ ⊆ s₃ → s₁ ⊆ s₃ := by
  simp only [subset_iff]
  intro h₁ h₂ x h
  exact h₂ _ (h₁ _ h)

theorem le_trans {s₁ s₂ s₃ : S α} : s₁ ≤ s₂ → s₂ ≤ s₃ → s₁ ≤ s₃ :=
  subset_trans

/-! # union -/

@[symm]
theorem union_comm {s₁ s₂ : S α} : s₁ ∪ s₂ = s₂ ∪ s₁ := by
  ext; simp only [mem_union_iff, or_comm]

theorem union_assoc {s₁ s₂ s₃ : S α} : (s₁ ∪ s₂) ∪ s₃ = s₁ ∪ (s₂ ∪ s₃) := by
  ext; simp only [mem_union_iff, or_assoc]

@[simp]
theorem mem_empty_iff_false (a : α) : a ∈ (∅ : S α) ↔ False :=
  Iff.intro
    (fun h => (not_mem_empty a) h)
    (fun h => False.elim h)

@[simp]
theorem union_empty (s : S α) : s ∪ ∅ = s := by
  ext; simp only [mem_union_iff, not_mem_empty, or_false]

@[simp]
theorem empty_union (s : S α) : ∅ ∪ s = s := by
  rw [union_comm]
  exact union_empty s

@[simp]
theorem union_self (s : S α) : s ∪ s = s := by
  ext; simp only [mem_union_iff, or_self]

theorem union_of_subset {s₁ s₂ : S α} : s₁ ⊆ s₂ → s₁ ∪ s₂ = s₂ := by
  intro h
  ext x
  simp only [mem_union_iff, or_iff_right_iff_imp]
  simp only [subset_iff] at h
  exact h x

/-! # inter -/

@[symm]
theorem inter_comm (s₁ s₂ : S α) : s₁ ∩ s₂ = s₂ ∩ s₁ := by
  ext; simp only [mem_inter_iff, and_comm]

theorem inter_assoc (s₁ s₂ s₃ : S α) : (s₁ ∩ s₂) ∩ s₃ = s₁ ∩ (s₂ ∩ s₃) := by
  ext; simp only [mem_inter_iff, and_assoc]

@[simp]
theorem inter_empty (s : S α) : s ∩ ∅ = ∅ := by
  ext; simp only [mem_inter_iff, not_mem_empty, and_false]

@[simp]
theorem empty_inter (s : S α) : ∅ ∩ s = ∅ := by
  rw [inter_comm]
  exact inter_empty s

@[simp]
theorem inter_self (s : S α) : s ∩ s = s := by
  ext; simp only [mem_inter_iff, and_self]

@[simp]
theorem inter_subset_left (s₁ s₂ : S α) : s₁ ∩ s₂ ⊆ s₁ := by
  simp only [subset_iff, mem_inter_iff, and_imp]
  intros
  assumption

@[simp]
theorem inter_subset_right (s₁ s₂ : S α) : s₁ ∩ s₂ ⊆ s₂ := by
  rw [inter_comm]
  exact inter_subset_left s₂ s₁

@[simp]
theorem inter_union_left (s₁ s₂ : S α) : s₁ ∩ (s₁ ∪ s₂) = s₁ := by
  ext; simp only [mem_inter_iff, mem_union_iff, and_iff_left_iff_imp]
  exact (Or.inl ·)

@[simp]
theorem inter_union_right (s₁ s₂ : S α) : s₁ ∩ (s₂ ∪ s₁) = s₁ := by
  rw [union_comm]
  exact inter_union_left s₁ s₂

@[simp]
theorem union_inter_left (s₁ s₂ : S α) : s₁ ∪ (s₁ ∩ s₂) = s₁ := by
  ext; simp only [mem_union_iff, mem_inter_iff, or_iff_left_iff_imp, and_imp]
  intros; assumption

@[simp]
theorem union_inter_right (s₁ s₂ : S α) : s₁ ∪ (s₂ ∩ s₁) = s₁ := by
  rw [inter_comm]
  exact union_inter_left s₁ s₂

theorem union_inter_distrib (s₁ s₂ s₃ : S α)
    : (s₁ ∪ s₂) ∩ s₃ = (s₁ ∩ s₃) ∪ (s₂ ∩ s₃) := by
  ext; simp only [mem_union_iff, mem_inter_iff, or_and_right]

theorem inter_union_distrib (s₁ s₂ s₃ : S α)
    : (s₁ ∩ s₂) ∪ s₃ = (s₁ ∪ s₃) ∩ (s₂ ∪ s₃) := by
  ext; simp only [mem_union_iff, mem_inter_iff, and_or_right]

/-! # sdiff -/

@[simp]
theorem sdiff_subset (s₁ s₂ : S α) : (s₁ \ s₂) ⊆ s₁ := by
  simp only [subset_iff, mem_sdiff_iff, and_imp]
  intros
  assumption

@[simp]
theorem sdiff_empty (s : S α) : s \ ∅ = s := by
  ext; simp only [mem_sdiff_iff, not_mem_empty, not_false_eq_true, and_true]

@[simp]
theorem empty_sdiff (s : S α) : ∅ \ s = ∅ := by
  ext; simp only [mem_sdiff_iff, not_mem_empty, false_and]

theorem sdiff_sdiff (s₁ s₂ s₃ : S α) : (s₁ \ s₂) \ s₃ = s₁ \ (s₂ ∪ s₃) := by
  ext; simp only [mem_sdiff_iff, and_assoc, mem_union_iff, not_or]

theorem sdiff_sdiff_comm (s₁ s₂ s₃ : S α) :
    (s₁ \ s₂) \ s₃ = (s₁ \ s₃) \ s₂ := by
  ext; simp only [mem_sdiff_iff, and_assoc, and_congr_right_iff]
  intro
  exact And.comm

@[simp]
theorem sdiff_union_left (s₁ s₂ : S α) : (s₁ \ s₂) ∪ s₁ = s₁ := by
  ext; simp only [mem_union_iff, mem_sdiff_iff, or_iff_right_iff_imp, and_imp]
  intros
  assumption

@[simp]
theorem sdiff_union_right (s₁ s₂ : S α) : (s₁ \ s₂) ∪ s₂ = s₁ ∪ s₂ := by
  ext x; simp only [mem_union_iff, mem_sdiff_iff]
  constructor
  · rintro (⟨h, _⟩ | h)
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h₁ | h₁)
    · by_cases h₂ : x ∈ s₂
      · exact Or.inr h₂
      · exact Or.inl ⟨h₁, h₂⟩
    · exact Or.inr h₁

/-! # insert -/

@[simp]
theorem insert_empty (x : α) : (∅ : S α) + x = {x} := by
  ext; simp only [mem_insert_iff, not_mem_empty, or_false, mem_singleton_iff]

instance instLawfulSingleton : LawfulSingleton α (S α) where
  insert_empty_eq := insert_empty

@[simp]
theorem mem_insert_self (a : α) (s : S α) : a ∈ (s + a) := by
  simp only [mem_insert_iff, true_or]

theorem mem_insert_of_mem {b : α} {s : S α} (h : b ∈ s) (a : α) : b ∈ (s + a) := by
  simp only [mem_insert_iff, h, or_true]

@[simp]
theorem insert_insert_self (a : α) (s : S α) : (s + a) + a = s + a := by
  ext; simp only [mem_insert_iff, or_self_left]

@[simp]
theorem insert_remove_of_mem {a : α} {s : S α} (h : a ∈ s)
    : (s - a) + a = s := by
  ext x
  simp only [mem_insert_iff, mem_remove_iff, ne_eq]
  constructor
  · rintro (rfl | ⟨_, h_mem⟩)
    <;> assumption
  · intro h_mem
    by_cases h_eq : x = a
    · exact Or.inl h_eq
    · exact Or.inr ⟨h_eq, h_mem⟩

theorem insert_insert_comm (a b : α) (s : S α) : (s + a) + b = (s + b) + a := by
  ext x; simp only [mem_insert_iff]; rw [← or_assoc, @or_comm (x = b) (x = a), or_assoc]

theorem insert_union_comm (a : α) (s₁ s₂ : S α) : (s₁ + a) ∪ s₂ = (s₁ ∪ s₂) + a := by
  ext x; simp only [mem_union_iff, mem_insert_iff, or_assoc]

theorem insert_eq_union_singleton (a : α) (s : S α) : (s + a) = s ∪ {a} := by
  ext x; simp only [mem_insert_iff, mem_union_iff, mem_singleton_iff, or_comm]

/-! # remove -/

@[simp]
theorem remove_empty (a : α) : (∅ : S α) - a = ∅ := by
  ext; simp only [mem_remove_iff, ne_eq, not_mem_empty, and_false]

@[simp]
theorem remove_singleton_self (a : α) : ({a} : S α) - a = ∅ := by
  ext; simp only [mem_remove_iff, ne_eq, mem_singleton_iff, not_and_self, not_mem_empty]

@[simp]
theorem remove_singleton_eq_empty_iff (a b : α)
    : ({a} : S α) - b = ∅ ↔ a = b := by
  constructor
  · intro h
    have h_iff := LawfulVSetLikeF.ext_iff.mp h
    simp only [mem_remove_iff, ne_eq, mem_singleton_iff,
        not_mem_empty, iff_false, not_and] at h_iff
    false_or_by_contra
    rename_i h_con
    have := h_iff a h_con
    contradiction
  · rintro rfl
    simp only [remove_singleton_self]

@[simp]
theorem not_mem_remove_self (a : α) (s : S α) : a ∉ (s - a) := by
  simp only [mem_remove_iff, ne_eq, not_true_eq_false, false_and, not_false_eq_true]

theorem not_mem_remove_iff {a b : α} {s : S α} : b ∉ (s - a) ↔ b = a ∨ b ∉ s := by
  simp only [mem_remove_iff, ne_eq, not_and]
  constructor
  · intro h_imp
    by_cases hba : b = a
    · exact Or.inl hba
    · exact Or.inr <| h_imp hba
  · rintro (rfl | h_mem)
    · simp only [not_true_eq_false, false_implies]
    · exact fun _ => h_mem

theorem remove_of_not_mem {a : α} {s : S α} (h : a ∉ s) : (s - a) = s := by
  ext x
  simp [mem_remove_iff]
  rintro hs rfl
  exact absurd hs h

@[simp]
theorem remove_remove (a : α) (s : S α) : (s - a) - a = s - a := by
  ext; simp only [mem_remove_iff, ne_eq, and_self_left]

theorem remove_eq_sdiff_singleton (a : α) (s : S α) :
    s - a = s \ {a} := by
  ext x; simp only [mem_remove_iff, ne_eq, mem_sdiff_iff, mem_singleton_iff, and_comm]

/-! # disjoint -/

theorem disjoint_iff_inter_eq_empty {s₁ s₂ : S α} :
    disjoint s₁ s₂ ↔ (s₁ ∩ s₂) = ∅ := by
  simp only [disjoint_iff, mem_inter_iff, not_and]
  constructor
  · intro h
    ext
    simp only [mem_inter_iff, not_mem_empty, iff_false, not_and]
    exact h _
  · intro h a h₁ h₂
    have := mem_inter_iff.mpr ⟨h₁, h₂⟩
    rw [h] at this
    exact absurd this (not_mem_empty _)

theorem disjoint_comm {s₁ s₂ : S α} : disjoint s₁ s₂ ↔ disjoint s₂ s₁ := by
  simp only [disjoint_iff, inter_comm]

@[simp]
theorem disjoint_empty (s : S α) : disjoint s ∅ := by
  rw [disjoint_iff_inter_eq_empty, inter_empty]

@[simp]
theorem empty_disjoint (s : S α) : disjoint ∅ s := by
  rw [disjoint_iff_inter_eq_empty, empty_inter]

@[simp]
theorem disjoint_self_iff (s : S α) : disjoint s s ↔ s = ∅ := by
  rw [disjoint_iff_inter_eq_empty, inter_self]

/-! # filter -/

@[simp]
theorem filter_subset (p : α → Bool) (s : S α) :
    filter s p ⊆ s := by
  simp only [subset_iff, mem_filter_iff, and_imp]
  intros
  assumption

@[simp]
theorem filter_trivial_true (s : S α) : filter s (fun _ => true) = s := by
  ext; simp only [mem_filter_iff, and_true]

@[simp]
theorem filter_trivial_false (s : S α) : filter s (fun _ => false) = ∅ := by
  ext; simp only [mem_filter_iff, Bool.false_eq_true, and_false, not_mem_empty]

@[simp]
theorem filter_filter_self (p : α → Bool) (s : S α) :
    filter (filter s p) p = filter s p := by
  ext; simp only [mem_filter_iff, and_self_right]

@[simp]
theorem filter_filter (p q : α → Bool) (s : S α) :
    filter (filter s p) q = filter s (fun x => p x && q x) := by
  ext; simp only [mem_filter_iff, and_assoc, Bool.and_eq_true]

theorem filter_filter_comm (p q : α → Bool) (s : S α) :
    filter (filter s p) q = filter (filter s q) p := by
  ext; simp only [filter_filter, mem_filter_iff, Bool.and_eq_true, and_comm]

theorem filter_subset_filter_of_subset {s₁ s₂ : S α}
    : s₁ ⊆ s₂ → ∀ (p : α → Bool), filter s₁ p ⊆ filter s₂ p := by
  intro h p
  simp only [subset_iff, mem_filter_iff, and_imp]
  intro a h_mem hp
  exact ⟨(subset_iff.mp h) _ h_mem, hp⟩

theorem filter_subset_of_subset {s₁ s₂ : S α}
    : s₁ ⊆ s₂ → ∀ (p : α → Bool), filter s₁ p ⊆ s₂ :=
  fun h p => subset_trans (filter_subset_filter_of_subset h p) (filter_subset _ _)

/-! # map -/

@[simp]
theorem map_empty (f : α → β) : f <$> (∅ : S α) = ∅ := by
  ext; simp only [mem_map_iff, mem_empty_iff_false, false_and, exists_false]

theorem map_map (f : α → β) (g : β → γ) (s : S α)
    : g <$> (f <$> s) = (fun x => g (f x)) <$> s :=
  Functor.map_map f g s

theorem map_map' (f : α → β) (g : β → γ) (s : S α)
    : g <$> (f <$> s) = (g ∘ f) <$> s :=
  Functor.map_map f g s

@[simp]
theorem map_singleton (f : α → β) (a : α) : f <$> ({a} : S α) = ({f a} : S β) := by
  ext; simp only [mem_map_iff, mem_singleton_iff, exists_eq_left]
  exact eq_comm

theorem map_union (f : α → β) (s₁ s₂ : S α)
    : f <$> (s₁ ∪ s₂) = (f <$> s₁) ∪ (f <$> s₂) := by
  ext; simp only [mem_map_iff, mem_union_iff, or_and_right, exists_or]

theorem map_inter (f : α → β) (S₁ S₂ : S α)
    : f <$> (S₁ ∩ S₂) ⊆ (f <$> S₁) ∩ (f <$> S₂) := by
  simp [subset_iff, mem_map_iff, mem_inter_iff]
  rintro b a ha₁ ha₂ rfl
  exact ⟨⟨a, ha₁, rfl⟩, ⟨a, ha₂, rfl⟩⟩

theorem map_insert (f : α → β) (a : α) (s : S α)
    : f <$> (s + a) = (f <$> s) + f a := by
  simp only [insert_eq_union_singleton, map_union, map_singleton]

theorem map_ofList (f : α → β) (l : List α)
    : f <$> (ofList l : S α) = ofList (l.map f) := by
  ext; simp only [mem_map_iff, mem_ofList_iff, List.mem_map]

end VSetLikeF /- namespace -/

namespace VSetF

open VSetLikeF LawfulVSetLikeF LawfulVSetF

variable {S : Type u → Type v} [VSetF S] [LawfulVSetF S] [∀ (a : α) (s : S α), Decidable (a ∈ s)]

/-! # card -/

@[simp]
theorem card_eq_zero_iff (s : S α) : card s = 0 ↔ s = ∅ := by
  constructor
  · intro h
    false_or_by_contra
    rename_i h_con
    rcases (ne_empty_iff_exists_mem (s := s)).mp h_con with ⟨x, hx⟩
    have := insert_remove_of_mem hx
    rw [← this, card_insert] at h
    simp only [not_mem_remove_self, ↓reduceIte, Nat.add_one_ne_zero] at h
  · rintro rfl
    exact card_empty

@[simp]
theorem card_singleton (a : α) : card ({a} : S α) = 1 := by
  simp only [← insert_empty, card_insert, mem_empty_iff_false,
    ↓reduceIte, card_empty, Nat.zero_add]

@[simp]
theorem card_pos_iff_ne_empty {s : S α} : 0 < card s ↔ s ≠ ∅ := by
  -- TODO: Probably a one-line proof via `mt` or something similar
  constructor
  · intro h h_con
    rw [(card_eq_zero_iff (s := s)).mpr h_con] at h
    contradiction
  · rw [← Nat.ne_zero_iff_zero_lt]
    intro h h_con
    rw [(card_eq_zero_iff (s := s)).mp h_con] at h
    contradiction

theorem card_remove (a : α) (s : S α)
    : card (s - a) = if a ∈ s then card s - 1 else card s := by
  split
  <;> rename_i ha
  · conv => rhs; rw [← insert_remove_of_mem ha, card_insert]
    simp only [not_mem_remove_self, ↓reduceIte, Nat.add_one_sub_one]
  · rw [remove_of_not_mem ha]

theorem card_union (s₁ s₂ : S α)
    : card (s₁ ∪ s₂) = card s₁ + card s₂ - card (s₁ ∩ s₂) := by
  sorry
  done

theorem card_disjoint {s₁ s₂ : S α} : disjoint s₁ s₂ → card (s₁ ∪ s₂) = card s₁ + card s₂ := by
  intro h
  rw [disjoint_iff_inter_eq_empty] at h
  simp only [card_union, h, card_empty, Nat.sub_zero]

end VSetF /- namespace -/

end Vstd

#exit

-- CC: (5/8) Below is an older implementation of `Set`

namespace Set

-- CC: Maybe phrase in terms of Surjectivity in Batteries?
-- CZ: can't find anything about `Surjective` in Batteries
-- A type is `Finite` if it is in bijective correspondence to some `Fin n`
def finite (S : Set α) : Prop :=
  ∃ (n : Nat) (f : Fin n → α), ∀ x, (x ∈ S ↔ ∃ i, f i = x)

def surj_on (f : α → β) (S : Set α) : Prop :=
  ∀ (a1 a2), S.contains a1 ∧ S.contains a2 ∧ a1 ≠ a2 → f a1 ≠ f a2

-- CZ: An alternate definition of `finite`, a direct translation of `finite` in Vstd
-- Note that this version has no bijection, so `ub` is not the cardinality
def finite' (S : Set α) : Prop :=
  ∃ (f : α → Nat) (ub : Nat), surj_on f S ∧ ∀ a, a ∈ S → f a < ub

open Classical

-- CC: This is broken, due to possibly needing `DecidableEq α`.
--     Ponder this. Verus seems to really like fold.
--     But don't spend too much time here, since Verus seemed to take a long time to build it up
/- noncomputable def fold (S : Set α) (f : α → β → α) (init : β) : β :=
  if h : ∃ x, x ∈ S then
    let x := S.choose h
    fold (S.remove x) f (f x init)
  else
    init -/

-- Only meaningful if a set is finite.
noncomputable def fold (S : Set α) (f : β → α → β) (init : β) (h_finite : finite S α) : β :=
  let n := Exists.choose h_finite
  let f_finite : Fin n → α := Exists.choose (Exists.choose_spec h_finite)
  let elemsList := (List.finRange n).map f_finite
  List.foldl f init elemsList

/- -- Only meaningful if a set is finite.
noncomputable def fold (f : α → β → β) (b : β) (S : Set α) [∀ x, Decidable (S x)] : β :=
  if h : ∃ xs : List α, (∀ x ∈ xs, S x) ∧ xs.Nodup then
    List.foldr f b h.choose
  else
    b -/

-- CZ: A version based on `finite'`
noncomputable def fold' (S : Set α) (f : β → α → β) (init : β) (h_finite : finite' S α) : β :=
  let f_to_nat : α → Nat := Exists.choose h_finite
  let ub := Exists.choose (Exists.choose_spec h_finite)
  let elemsList := (List.range ub).filterMap (fun i =>
    if h : ∃ a, a ∈ S ∧ f_to_nat a = i then
      some (Classical.choose h)
    else
      none)
  List.foldl f init elemsList

def map (f : α → β) (S : Set α) : Set β :=
  fun y => ∃ x, S x ∧ f x = y

@[simp]
theorem union_compl (S : Set α) : S ∪ compl S = full := by
  ext x
  simp only [mem_full, iff_true]
  apply mem_union_iff.mpr
  exact Decidable.or_iff_not_imp_left.mpr id

/-! # finite -/

-- CC: This proof will very much depend on your definition of `finite`,
--     so be happy with that definition first
theorem finite_empty : finite (∅ : Set α) :=
  ⟨0, Fin.elim0,  -- The empty function from Fin 0 to α
   λ _ =>
     ⟨λ h => False.elim h,  -- Empty set has no elements
      λ ⟨i, _⟩ => Fin.elim0 i⟩  -- Fin 0 is uninhabited
  ⟩

theorem finite_empty' : finite' (∅ : Set α) :=
  ⟨fun _ => 0, 0,
   ⟨λ _ _ h => False.elim h.1,
    λ _ h => False.elim h⟩
  ⟩

-- CZ: I start to prove things only for `finite'`, not sure if it's any easier

-- theorem finite_singleton (a : α) : finite (singleton a) :=
--   by sorry

theorem finite_singleton' (a : α) : finite' (singleton a) :=
  let f := fun x => if x = a then 0 else 1
  ⟨f, 1,
   ⟨λ a1 a2 h => by                 -- Injectivity proof
      simp [contains, Mem, singleton] at h
      have hn : a1 ≠ a2 := h.2.2
      simp [h.1, h.2.1] at hn,
    λ x h => by                     -- Bound proof
      by_cases he : x = a
      . rw [he]
        simp [f]
      . simp [Membership.mem, Mem, singleton] at h
        exact (he h).elim⟩
  ⟩

-- Verus calls this axiom_set_insert_finite
-- theorem finite_insert_of_finite (a : α) (S : Set α) (h : finite S α) :
--     finite (insert a S α) := by
--   sorry

theorem finite_insert_of_finite' (a : α) (S : Set α) (h : finite' S α) :
    finite' (insert a S α) :=
  match h with
  | ⟨f, ub, h_inj, h_bound⟩ =>
    let new_f : α → Nat := fun x => if x = a then ub else f x
    let new_ub := ub + 1
    ⟨new_f, new_ub,
     ⟨fun a1 a2 h => by -- Injectivity proof
        simp [contains, Mem, insert] at h
        let ⟨h1, h2, hne⟩ := h
        have h1' : a1 = a ∨ ¬ a1 = a := Classical.em (a1 = a)
        have h2' : a2 = a ∨ ¬ a2 = a := Classical.em (a2 = a)
        cases h1' with
        | inl ha1 => -- a1 = a
          cases h2 with
          | inl ha2 => -- a2 = a
            exact (hne (trans ha1 ha2.symm)).elim
          | inr ha2S => -- a2 ∈ S
            have ha2_mem : a2 ∈ S := ha2S
            have lhs : new_f a1 = ub := by simp [ha1, new_f]
            have a2_ne_a : a2 ≠ a := by rw [ha1] at hne; exact Ne.symm hne
            have rhs : new_f a2 = f a2 := by simp [a2_ne_a, if_neg, new_f]
            have rhs' : new_f a2 ≠ ub := by simp [rhs, ha2_mem, h_bound, Nat.lt_iff_le_and_ne.1]
            simp [lhs, rhs', Ne.symm]
        | inr ha1n => -- a1 ∈ S
          have h1S : S a1 := by simp [ha1n] at h1; exact h1
          have ha1_mem : a1 ∈ S := h1S
          cases h2' with
          | inl ha2 => -- a2 = a
            have rhs : new_f a2 = ub := by simp [ha2, new_f]
            have lhs : new_f a1 = f a1 := by simp [ha1n, if_neg, new_f]
            have lhs' : new_f a1 ≠ ub := by simp [lhs, ha1_mem, h_bound, Nat.lt_iff_le_and_ne.1]
            simp [lhs', rhs, Ne.symm]
          | inr ha2n => -- a2 ∈ S
            have ha2S : S a2 := by simp [ha2n] at h2; exact h2
            have lhs : new_f a1 = f a1 := by simp [ha1n, if_neg, new_f]
            have rhs : new_f a2 = f a2 := by simp [ha2n, if_neg, new_f]
            rw [lhs, rhs]
            apply h_inj
            simp [contains, Membership.mem, Mem]
            exact ⟨h1S, ha2S, hne⟩,

      fun x h => by -- Bounding proof
        simp [Membership.mem, Mem, insert] at h
        have h' : x = a ∨ ¬ x = a := Classical.em (x = a)
        cases h' with
        | inl hxa =>
          simp [new_f, hxa, new_ub]
        | inr hxan =>
          simp [new_f, hxan]
          have hxS : S x := by simp [hxan] at h; exact h
          apply Nat.lt_trans (h_bound x hxS α) (Nat.lt_succ_self ub)⟩
    ⟩

-- Verus calls this axiom_set_remove_finite
-- theorem finite_remove_of_finite (a : α) (S : Set α) (h : finite S α) :
--     finite (remove a S α) := by
--   sorry

theorem finite_remove_of_finite' (a : α) (S : Set α) (h : finite' S α) :
    finite' (remove a S α) := by
  rcases h with ⟨f, ub, h_inj, h_bound⟩
  refine ⟨f, ub, ?inj, ?bound⟩
  case inj => -- Injectivity proof
    intro a1 a2 h
    simp only [remove, contains, Mem] at h
    exact h_inj a1 a2 ⟨h.1.2, h.2.1.2, h.2.2⟩
  case bound => -- Bounding proof
    intro x hx
    simp only [Membership.mem, remove, contains, Mem] at hx
    exact h_bound x hx.2

-- theorem finite_union (S₁ S₂ : Set α) (h₁ : finite S₁) (h₂ : finite S₂) :
--     finite (S₁ ∪ S₂) := by
--   sorry

theorem finite_union' (S₁ S₂ : Set α) (h₁ : finite' S₁) (h₂ : finite' S₂) :
    finite' (S₁ ∪ S₂) := by
  rcases h₁ with ⟨f₁, ub₁, h_inj₁, h_bound₁⟩
  rcases h₂ with ⟨f₂, ub₂, h_inj₂, h_bound₂⟩

  let new_f : α → Nat := fun x =>
    if S₁ x then f₁ x else ub₁ + f₂ x
  let new_ub := ub₁ + ub₂
  refine ⟨new_f, new_ub, ?inj, ?bound⟩

  -- Injectivity proof
  case inj =>
    intro a1 a2 h
    simp only [contains, Mem, union] at h
    rcases h with ⟨h1, h2, hne⟩
    have h1_cases : S₁ a1 ∨ ¬ S₁ a1 := Classical.em (S₁ a1)
    have h2_cases : S₁ a2 ∨ ¬ S₁ a2 := Classical.em (S₁ a2)
    cases h1_cases <;> cases h2_cases

    -- Case 1: Both in S₁
    case inl.inl h1_S₁ h2_S₁ =>
      simp [new_f, h1_S₁, h2_S₁]
      exact h_inj₁ a1 a2 ⟨h1_S₁, h2_S₁, hne⟩

    -- Case 2: a1 ∈ S₁, a2 ∉ S₁
    case inl.inr h1_S₁ h2_nS₁ =>
      have : f₁ a1 < ub₁ := h_bound₁ a1 h1_S₁
      have lhs : new_f a1 < ub₁ := by simp [this, h1_S₁, new_f]
      have rhs : ub₁ ≤ new_f a2 := by simp [h2_nS₁, new_f]
      simp [Nat.lt_iff_le_and_ne.1, Nat.lt_of_lt_of_le lhs rhs]

    -- Case 3: a1 ∉ S₁, a2 ∈ S₁
    case inr.inl h1_nS₁ h2_S₁ =>
      have : f₁ a2 < ub₁ := h_bound₁ a2 h2_S₁
      have lhs : new_f a2 < ub₁ := by simp [this, h2_S₁, new_f]
      have rhs : ub₁ ≤ new_f a1 := by simp [h1_nS₁, new_f]
      simp [Nat.lt_iff_le_and_ne.1, Nat.lt_of_lt_of_le lhs rhs, Ne.symm]

    -- Case 4: Both ∉ S₁ (must be in S₂)
    case inr.inr h1_nS₁ h2_nS₁ =>
      have h1_S₂ : S₂ a1 := h1.resolve_left h1_nS₁
      have h2_S₂ : S₂ a2 := h2.resolve_left h2_nS₁
      simp [new_f, h1_nS₁, h2_nS₁]
      exact h_inj₂ a1 a2 ⟨h1_S₂, h2_S₂, hne⟩

  -- Bounding proof
  case bound =>
    intro x hx
    simp [Membership.mem, Set.Mem, instUnion, union] at hx
    cases Classical.em (S₁ x) with
    | inl hx₁ =>
      simp [new_f, hx₁]
      exact Nat.lt_of_lt_of_le (h_bound₁ x hx₁) (Nat.le_add_right ub₁ ub₂)
    | inr hnx₁ =>
      have hx₂ : S₂ x := hx.resolve_left hnx₁
      simp [new_f, hnx₁, new_ub]
      exact h_bound₂ x hx₂

-- theorem finite_union_iff (S₁ S₂ : Set α) :
--     finite (S₁ ∪ S₂) ↔ finite S₁ ∧ finite S₂ := by
--   sorry

theorem finite_union_iff' (S₁ S₂ : Set α)
    : finite' (S₁ ∪ S₂) ↔ finite' S₁ ∧ finite' S₂ := by
  constructor
  · intro h
    rcases h with ⟨f, ub, h_inj, h_bound⟩
    constructor
    · -- finite' S₁
      refine ⟨f, ub, ?inj, ?bound⟩
      case inj =>
        intro a1 a2 h
        simp [contains, Mem] at h
        apply h_inj
        simp [instUnion, union, contains, Mem]
        simp [h]
      case bound =>
        intro x hx
        simp [Membership.mem, contains, Mem] at hx
        have hx' : (S₁ ∪ S₂) x := by simp [instUnion, union, contains, Mem, hx]
        apply h_bound x hx'
    · -- finite' S₂
      refine ⟨f, ub, ?inj, ?bound⟩
      case inj =>
        intro a1 a2 h
        simp [contains, Mem] at h
        apply h_inj
        simp [instUnion, union, contains, Mem]
        simp [h]
      case bound =>
        intro x hx
        simp [Membership.mem, contains, Mem] at hx
        have hx' : (S₁ ∪ S₂) x := by simp [instUnion, union, contains, Mem, hx]
        apply h_bound x hx'
  · -- Reverse direction (←)
    intro ⟨h₁, h₂⟩
    exact finite_union' S₁ S₂ h₁ h₂

-- theorem finite_inter_left (S₁ S₂ : Set α) (h : finite S₁) :
--     finite (S₁ ∩ S₂) := by
--   sorry

theorem finite_inter_left' (S₁ S₂ : Set α) (h : finite' S₁)
    : finite' (S₁ ∩ S₂) := by
  rcases h with ⟨f, ub, h_inj, h_bound⟩
  refine ⟨f, ub, ?inj, ?bound⟩

  -- Injectivity proof
  case inj =>
    intro a1 a2 h
    simp [contains, Mem] at h
    exact h_inj a1 a2 ⟨h.1.1, h.2.1.1, h.2.2⟩

  -- Bounding proof
  case bound =>
    intro x hx
    simp [Membership.mem, contains, Mem] at hx
    exact h_bound x hx.1

-- theorem finite_inter_right (S₁ S₂ : Set α) (h : finite S₂) :
--     finite (S₁ ∩ S₂) := by
--   sorry

theorem finite_inter_right' (S₁ S₂ : Set α) (h : finite' S₂)
    : finite' (S₁ ∩ S₂) := by
  have : S₁ ∩ S₂ = S₂ ∩ S₁ := by
    ext x
    simp [Membership.mem, Mem, Inter.inter, inter, and_comm]
  rw [this]
  exact finite_inter_left' S₂ S₁ h

-- CC: Should be a simple lemma of the above two
-- Verus calls this axiom_set_difference_finite
-- theorem finite_inter_of_finite_of_finite (S₁ S₂ : Set α)
--     (h₁ : finite S₁) (h₂ : finite S₂) :
--     finite (S₁ ∩ S₂) := by
--   sorry

theorem finite_inter_of_finite_of_finite' (h₁ : finite' S₁) (_ : finite' S₂)
    : finite' (S₁ ∩ S₂) :=
  finite_inter_left' S₁ S₂ h₁

end Vstd
