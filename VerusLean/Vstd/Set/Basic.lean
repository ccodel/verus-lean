import VerusLean.Vstd.Set.Defs

namespace Vstd

namespace VSetLikeF

variable {S : Type u → Type v} [VSetLikeF S] {α β : Type u}

theorem add_def (s t : S α) : union s t = s ∪ t := rfl

theorem mem_or_not_mem (a : α) (s : S α) : a ∈ s ∨ a ∉ s := by
  by_cases h : a ∈ s
  · exact Or.inl h
  · exact Or.inr h

section
variable (S : Type u → Type v) (α : Type u) [DecidableEq α] [VSetF S] [LawfulVSetF S]
instance : DecidableRel (fun (x : α) (s : S α) => x ∈ s) := by
  rw [DecidableRel]
  intro a s
  exact decidable_of_iff (a ∈ VSetF.toList s) (LawfulVSetF.mem_toList_iff (s := s) a).symm
end

section
variable (S : Type → Type) [VSetF S] [LawfulVSetF S]

example (x : Nat) (s : S Nat) := if x ∈ s then 1 else 0

variable {α : Type} [DecidableEq α]

example : ∀ x (s : S α), x ∈ s ∨ x ∉ s := by
  intro x s
  apply Decidable.em

open Classical
noncomputable section

example (x : Nat → Nat) (s : S (Nat → Nat)) :=
  if x ∈ s then 0 else 1

end

end

/-! # lawful sets -/
open LawfulVSetLikeF

variable {S : Type u → Type v} [VSetLikeF S] [LawfulVSetLikeF S] {α β : Type u}

-- variable {S_decidable : Type u → Type v} [Decidable u] [VSetLikeF S] [LawfulVSetLikeF S] {α β : Type u}

/-! # empty -/

@[simp]
theorem mem_empty_iff_false (a : α) : a ∈ (∅ : S α) ↔ False :=
  Iff.intro
    (fun h => (not_mem_empty a) h)
    (fun h => False.elim h)

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

/-! # subset -/

theorem eq_of_subset_of_subset {s₁ s₂ : S α} : s₁ ⊆ s₂ → s₂ ⊆ s₁ → s₁ = s₂ := by
  simp only [subset_iff]
  intro h₁ h₂
  ext x
  exact ⟨h₁ x, h₂ x⟩

theorem subset_antisymm_iff {s₁ s₂ : S α} : s₁ = s₂ ↔ s₁ ⊆ s₂ ∧ s₂ ⊆ s₁ := by
  constructor
  · rintro rfl
    simp [subset_iff]
  · intro h
    exact eq_of_subset_of_subset h.1 h.2

theorem subset_trans {s₁ s₂ s₃ : S α} : s₁ ⊆ s₂ → s₂ ⊆ s₃ → s₁ ⊆ s₃ := by
  simp only [subset_iff]
  intro h₁ h₂ x h
  exact h₂ _ (h₁ _ h)

theorem le_trans {s₁ s₂ s₃ : S α} : s₁ ≤ s₂ → s₂ ≤ s₃ → s₁ ≤ s₃ :=
  subset_trans

/-! # union -/

omit [LawfulVSetLikeF S] in
@[simp]
theorem union_eq_union_notation (s₁ s₂ : S α) :
  union s₁ s₂ = s₁ ∪ s₂ := rfl

@[symm]
theorem union_comm {s₁ s₂ : S α} : s₁ ∪ s₂ = s₂ ∪ s₁ := by
  ext; simp only [mem_union_iff, or_comm]

theorem union_assoc {s₁ s₂ s₃ : S α} : (s₁ ∪ s₂) ∪ s₃ = s₁ ∪ (s₂ ∪ s₃) := by
  ext; simp only [mem_union_iff, or_assoc]

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

-- Mathlib name `union_eq_right`
theorem subset_iff_union_eq_right {s₁ s₂ : S α} : s₁ ⊆ s₂ ↔ s₁ ∪ s₂ = s₂ := by
  constructor
  . intro h
    ext x
    simp only [mem_union_iff, or_iff_right_iff_imp]
    simp only [subset_iff] at h
    exact h x
  . intro h
    rw [←h]
    simp only [subset_iff]
    intro x hx
    simp [mem_union_iff, hx]

/-! # inter -/

omit [LawfulVSetLikeF S] in
@[simp]
theorem inter_eq_inter_notation (s₁ s₂ : S α) :
  inter s₁ s₂ = (s₁ ∩ s₂) := rfl

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

omit [LawfulVSetLikeF S] in
@[simp]
theorem sdiff_eq_sdiff_notation (s₁ s₂ : S α) :
  sdiff s₁ s₂ = (s₁ \ s₂) := rfl

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

-- theorem sdiff_d (s₁ s₂ : S α) : disjoint s₁ (s₂ \ s₁) := by
--   rw [disjoint_iff]
--   sorry

/-! # insert -/

omit [LawfulVSetLikeF S] in
@[simp]
theorem insert_eq_insert_notation (s : S α) :
  insert s a = s + a := rfl

@[simp]
theorem insert_empty (x : α) : (∅ : S α) + x = {x} := by
  ext; simp only [mem_insert_iff, not_mem_empty, or_false, mem_singleton_iff]

instance instLawfulSingleton : LawfulSingleton α (S α) where
  insert_empty_eq := insert_empty

-- Mathlib name `mem_insert`
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

omit [LawfulVSetLikeF S] in
@[simp]
theorem remove_eq_remove_notation (s : S α) :
  remove a s = s - a := rfl

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
theorem remove_remove_self (a : α) (s : S α) : (s - a) - a = s - a := by
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

/-! # finite sets -/
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

-- Cedar does not seem to have theorems for cardinality? (`size`)

-- CZ: Previous version intends to prove `card_union` (via induction?) then use it to prove `card_disjoint`.
-- I find it easier to prove `card_disjoint` first then use it to prove the general case `card_union`.

-- Define a decidable version of sets
variable {dS : Type u → Type v} (α : Type u) [DecidableEq α] [VSetF dS] [LawfulVSetF dS]

-- instance dr : DecidableRel (fun (x : α) (s : dS α) => x ∈ s) := by infer_instance
  -- rw [DecidableRel]
  -- intro a s
  -- exact decidable_of_iff (a ∈ VSetF.toList s) (LawfulVSetF.mem_toList_iff (s := s) a).symm

-- instance dr' : Decidable (x : α) (s₁ : dS α) (s₂ : dS α) => (a ∈ s₁)) := by
--   intro a s
--   exact decidable_of_iff (a ∈ VSetF.toList s) (LawfulVSetF.mem_toList_iff (s := s) a).symm

-- instance {s₁ s₂ : dS α} : Decidable (disjoint s₁ s₂) := by
--   have h_dec : ∀ a, Decidable (¬(a ∈ s₁ ∧ a ∈ s₂)) := fun a => inferInstance
--   have (s : dS α) : Decidable (s = ∅) := by rw [← card_eq_zero_iff]; exact inferInstance
--   refine decidable_of_iff (s₁ ∩ s₂ = ∅) ?_
--   simp only [disjoint_iff_inter_eq_empty, disjoint_iff]

theorem card_disjoint {s₁ s₂ : dS α} (h_disj : disjoint s₁ s₂) :
    card (s₁ ∪ s₂) = card s₁ + card s₂ := by
  let P (k : Nat) := -- The property we are inducting on for a given cardinality k
  ∀ (s₁_hyp : dS α) (s₂_hyp : dS α),
    card s₂_hyp = k →
    disjoint s₁_hyp s₂_hyp →
    card (union s₁_hyp s₂_hyp) = card s₁_hyp + card s₂_hyp

  suffices Q : ∀ k_val, P k_val by -- First, prove P holds for all natural numbers k_val
    exact Q (card s₂) s₁ s₂ rfl h_disj -- Then apply it to the specific s₁, s₂

  intro k -- Start of the proof for ∀ k, P(k). k is the current cardinality value.
  -- We use WellFounded.induction. ih is the hypothesis for all m < k.
  -- Might be a better practice to use `Nat.strongRecOn`
  induction k using WellFounded.induction with
  | h k_val ih_strong =>
    -- Goal for this step: P(k_val)
    -- P(k_val) is: ∀ s₁_hyp s₂_hyp, card s₂_hyp = k_val → ...
    intro s₁_hyp s₂_hyp h_card_s2_eq_k_val h_disj_hyp_bool

    -- This is the main body of the inductive step, proving P(k_val)
    by_cases h_s2_hyp_empty : s₂_hyp = (∅ : dS α)
    · -- If s₂_hyp is empty, then k_val = 0.
      have : union s₁_hyp ∅ = s₁_hyp := by
        exact union_empty s₁_hyp
      rw [h_s2_hyp_empty, this, card_empty, Nat.add_zero]

    · -- s₂_hyp is not empty
      have h_s2_hyp_ne_empty : s₂_hyp ≠ (∅ : dS α) := h_s2_hyp_empty
      have h_k_val_pos : 0 < k_val := by
        apply Nat.pos_of_ne_zero
        intro hk_val_zero
        rw [hk_val_zero] at h_card_s2_eq_k_val
        rw [card_eq_zero_iff (s:=s₂_hyp)] at h_card_s2_eq_k_val
        exact h_s2_hyp_ne_empty h_card_s2_eq_k_val

      let ⟨a, ha_in_s2_hyp⟩ := (ne_empty_iff_exists_mem (s := s₂_hyp)).mp h_s2_hyp_ne_empty

      let s₂' := remove a s₂_hyp
      have ha_notin_s2' : a ∉ s₂' := not_mem_remove_self a s₂_hyp
      have h_s2_hyp_eq_s2'_insert_a : s₂_hyp = VSetLikeF.insert s₂' a :=
        Eq.symm (insert_remove_of_mem ha_in_s2_hyp)

      have h_card_s2'_eq_k_val_minus_1 : card s₂' = k_val - 1 := by
        -- CZ: redundancy here (fixed by `remove_eq_remove_notation` with @[simp])
        -- have : s₂' = s₂_hyp - a := by
        --   simp only [s₂', instHSubSingleton]
        have : card s₂' = card s₂_hyp - 1 := by
          simp [s₂', card_remove a s₂_hyp, ha_in_s2_hyp]
        rw [this, h_card_s2_eq_k_val]

      have h_card_s2'_lt_k_val : card s₂' < k_val := by
        have : 1 ≤ k_val := by
          false_or_by_contra
          rename_i h_con
          rw [Nat.not_le, Nat.lt_one_iff] at h_con
          rw [h_con] at h_k_val_pos
          contradiction
        rw [h_card_s2'_eq_k_val_minus_1]
        exact Nat.sub_lt_self Nat.zero_lt_one this

      have h_card_s2'_lt_k_val : card s₂' < k_val := by
        simp [h_card_s2'_lt_k_val]

      -- From `disjoint s₁_hyp (insert a s₂')`, deduce `a ∉ s₁_hyp` and `disjoint s₁_hyp s₂'`.
      have h_disj_s1_hyp_s2_hyp_insert_a_true : VSetLikeF.disjoint s₁_hyp (VSetLikeF.insert s₂' a) := by
        rw [←h_s2_hyp_eq_s2'_insert_a]
        exact h_disj_hyp_bool

      have all_notin_inter_s1_hyp_insert : ∀ x, x ∉ inter s₁_hyp (VSetLikeF.insert s₂' a) :=
        (disjoint_iff (s₁ := s₁_hyp) (s₂ := VSetLikeF.insert s₂' a)).mp h_disj_s1_hyp_s2_hyp_insert_a_true

      have a_notin_s1_hyp : a ∉ s₁_hyp := by
        intro contra_a_in_s1_hyp
        -- CZ: very annoying redundancy here, but not sure why `simp [mem_inter_iff]` directly does not work
        -- have h_inter : inter s₁_hyp (VSetLikeF.insert a s₂') = s₁_hyp ∩ (VSetLikeF.insert a s₂') := by
        --   simp only [instInter]
        -- have h_add : VSetLikeF.insert a s₂' = s₂' + a := by
        --   simp only [s₂', instHAddSingleton]
        have a_in_s1_hyp_inter_insert : a ∈ inter s₁_hyp (VSetLikeF.insert s₂' a) := by
          /- CZ: Method 1 is to use `erw` (Extended Rewrite) instead of `rw` or `simp`,
             which performs more aggressive unfolding of defns to make patterns match.
             Method 2 is to include explicit lemmas with @[simp], see e.g. `inter_eq_inter_notation` above -/
          simp [mem_inter_iff, mem_insert_iff]
          simp [contra_a_in_s1_hyp]

        exact (all_notin_inter_s1_hyp_insert a) a_in_s1_hyp_inter_insert

      have h_disj_s1_hyp_s2'_true : disjoint s₁_hyp s₂' := by
        rw [disjoint_iff]
        intro x hx_in_s1_hyp_inter_s2'
        rw [mem_inter_iff] at hx_in_s1_hyp_inter_s2'
        let ⟨hx_in_s1_hyp, hx_in_s2'⟩ := hx_in_s1_hyp_inter_s2'
        have hx_in_insert_a_s2' : x ∈ VSetLikeF.insert s₂' a := mem_insert_of_mem hx_in_s2' a
        have hx_in_s1_hyp_inter_insert_a_s2' : x ∈ inter s₁_hyp (VSetLikeF.insert s₂' a) := by
          simp [mem_inter_iff, hx_in_s1_hyp, hx_in_insert_a_s2', ←insert_eq_insert_notation]
        exact (all_notin_inter_s1_hyp_insert x) hx_in_s1_hyp_inter_insert_a_s2'

      -- Apply inductive hypothesis ih_strong for card s₂' (which is k_val - 1)
      -- ih_strong : ∀ (m : Nat), m < k_val → P m
      -- We need P (card s₂')
      specialize ih_strong (card s₂') h_card_s2'_lt_k_val s₁_hyp s₂' (by rw [h_card_s2'_eq_k_val_minus_1]) h_disj_s1_hyp_s2'_true
      -- ih_strong is now: card (union s₁_hyp s₂') = card s₁_hyp + card s₂'

      -- Rewrite the goal using s₂_hyp = insert a s₂'
      rw [h_s2_hyp_eq_s2'_insert_a]

      have card_s2_hyp_val : card (VSetLikeF.insert s₂' a) = card s₂' + 1 := by
        simp [card_insert, ha_notin_s2']
      rw [card_s2_hyp_val]
      -- Goal: card (union s₁_hyp (insert a s₂')) = card s₁_hyp + (card s₂' + 1)

      simp [union_comm (s₁ := s₁_hyp), insert_union_comm]; rw [union_comm]
      -- LHS is card (insert a (union s₁_hyp s₂'))

      have a_notin_union_s1_hyp_s2' : a ∉ union s₁_hyp s₂' := by
        simp [mem_union_iff, a_notin_s1_hyp, ha_notin_s2']
      simp [←union_eq_union_notation, card_insert, a_notin_union_s1_hyp_s2']
      -- LHS is card (union s₁_hyp s₂') + 1

      -- Goal: card (union s₁_hyp s₂') + 1 = card s₁_hyp + card s₂' + 1
      rw [ih_strong]; rfl

  | hwf => exact Nat.lt_wfRel.wf


theorem card_union (s₁ s₂ : dS α)
    : card (s₁ ∪ s₂) = card s₁ + card s₂ - card (s₁ ∩ s₂) := by
  -- Express s₂ as the union of s₂ \ s₁ and s₁ ∩ s₂
  have h1 : s₂ = (s₂ \ s₁) ∪ (s₁ ∩ s₂) := by
    ext x
    simp only [mem_union_iff, mem_sdiff_iff, mem_inter_iff]
    constructor
    · intro h
      by_cases hx : x ∈ s₁
      · exact Or.inr ⟨hx, h⟩
      · exact Or.inl ⟨h, hx⟩
    · intro h
      cases h <;> simp_all

  -- These two parts are disjoint
  have h2 : disjoint (s₂ \ s₁) (s₁ ∩ s₂) := by
    rw [disjoint_iff_inter_eq_empty]; ext x
    simp [mem_inter_iff, mem_sdiff_iff, not_mem_empty]
    intro h₂ h₁; simp [h₁]

  -- So we can compute card s₂ by invoking the `card_disjoint` theorem
  have h3 : card s₂ = card (s₂ \ s₁) + card (s₁ ∩ s₂) := by
    have hd := card_disjoint α h2
    simp [←h1] at hd; exact hd

  -- Similarly, express s₁ ∪ s₂ as s₁ ∪ (s₂ \ s₁)
  have h4 : s₁ ∪ s₂ = s₁ ∪ (s₂ \ s₁) := by
    ext x
    simp only [mem_union_iff, mem_sdiff_iff]
    constructor
    · intro h
      by_cases hx : x ∈ s₁
      · exact Or.inl hx
      · simp [hx] at h
        exact Or.inr ⟨h, hx⟩
    · intro h
      by_cases hx : x ∈ s₁
      · exact Or.inl hx
      · simp [hx] at h
        exact Or.inr h

  -- These two parts are also disjoint
  have h5 : disjoint s₁ (s₂ \ s₁) := by
    rw [disjoint_iff_inter_eq_empty]; ext x
    simp [mem_inter_iff, mem_sdiff_iff, not_mem_empty]
    intro h₁ h₂; exact h₁

  -- So we can compute card (s₁ ∪ s₂)
  have h6 : card (s₁ ∪ s₂) = card s₁ + card (s₂ \ s₁) := by
    rw [h4, card_disjoint α h5]

  -- Now combine all the equations
  rw [h3, h6, ←Nat.add_assoc, Nat.add_sub_cancel]


end VSetF /- namespace -/

end Vstd
