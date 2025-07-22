import VerusLean.Vstd.Set.Defs

namespace Vstd

namespace Set

variable {α : Type u} {β : Type v} {γ : Type w}

/-! # mem -/

theorem mem_or_not_mem (a : α) (s : Set α) : a ∈ s ∨ a ∉ s := by
  by_cases h : a ∈ s
  · exact Or.inl h
  · exact Or.inr h

/-! # ext_eq -/

@[refl]
theorem ext_eq_refl (s : Set α) : ext_eq s s := by
  simp only [ext_eq_iff, implies_true, true_and]

@[symm]
theorem ext_eq_comm {s₁ s₂ : Set α} : ext_eq s₁ s₂ ↔ ext_eq s₂ s₁ := by
  simp only [ext_eq_iff]
  constructor
  all_goals (
    intro h a
    rw [Iff.comm]
    exact h a
  )

theorem ext_eq_trans {s₁ s₂ s₃ : Set α} : ext_eq s₁ s₂ → ext_eq s₂ s₃ → ext_eq s₁ s₃ := by
  simp only [ext_eq_iff]
  intro h₁ h₂ a
  exact Iff.trans (h₁ a) (h₂ a)

/-! # empty -/

@[simp]
theorem mem_empty_iff_false (a : α) : a ∈ (∅ : Set α) ↔ False :=
  Iff.intro
    (fun h => (not_mem_empty a) h)
    (fun h => False.elim h)

@[simp]
theorem empty_subset (s : Set α) : ∅ ⊆ s := by
  simp only [subset_iff, not_mem_empty, false_implies, implies_true]

@[simp]
theorem subset_empty_iff {s : Set α} : s ⊆ ∅ ↔ ext_eq s ∅ := by
  simp only [subset_iff, not_mem_empty, imp_false, ext_eq_iff, iff_false]

theorem ne_empty_iff_exists_mem {s : Set α} : ¬(ext_eq s ∅) ↔ ∃ x, x ∈ s := by
  simp [eq_empty_iff]

/-! # subset -/

@[refl]
theorem subset_refl (s : Set α) : s ⊆ s := by
  simp only [subset_iff, imp_self, implies_true]

theorem eq_of_subset_of_subset {s₁ s₂ : Set α} : s₁ ⊆ s₂ → s₂ ⊆ s₁ → ext_eq s₁ s₂ := by
  simp only [subset_iff]
  intro h₁ h₂
  simp [ext_eq_iff]
  intro a
  exact ⟨h₁ a, h₂ a⟩

theorem subset_antisymm_iff {s₁ s₂ : Set α} : ext_eq s₁ s₂ ↔ s₁ ⊆ s₂ ∧ s₂ ⊆ s₁ := by
  simp [ext_eq_iff, subset_iff]
  constructor
  · rintro h
    exact ⟨fun a => (h a).mp, fun a => (h a).mpr⟩
  · rintro ⟨h₁, h₂⟩ a
    exact ⟨h₁ a, h₂ a⟩

theorem subset_trans {s₁ s₂ s₃ : Set α} : s₁ ⊆ s₂ → s₂ ⊆ s₃ → s₁ ⊆ s₃ := by
  simp only [subset_iff]
  intro h₁ h₂ x h
  exact h₂ _ (h₁ _ h)

theorem le_trans {s₁ s₂ s₃ : Set α} : s₁ ≤ s₂ → s₂ ≤ s₃ → s₁ ≤ s₃ :=
  subset_trans

theorem subset_left_of_ext_eq_of_subset {s₁ s₂ s₃ : Set α} : ext_eq s₁ s₂ → s₁ ⊆ s₃ → s₂ ⊆ s₃ := by
  simp [ext_eq_iff, subset_iff]
  intro h_iff h_imp a h
  exact h_imp _ <| (h_iff a).mpr h

theorem subset_right_of_ext_eq_of_subset {s₁ s₂ s₃ : Set α} : ext_eq s₂ s₃ → s₁ ⊆ s₂ → s₁ ⊆ s₃ := by
  simp [ext_eq_iff, subset_iff]
  intro h_iff h_imp a h
  exact (h_iff a).mp <| h_imp a h

/-! # union -/

@[simp]
theorem union_eq_union_notation (s₁ s₂ : Set α) : union s₁ s₂ = s₁ ∪ s₂ := rfl

@[symm]
theorem union_comm (s₁ s₂ : Set α) : ext_eq (s₁ ∪ s₂) (s₂ ∪ s₁) := by
  simp only [ext_eq_iff, mem_union_iff, or_comm, implies_true]

theorem union_assoc (s₁ s₂ s₃ : Set α) : ext_eq ((s₁ ∪ s₂) ∪ s₃) (s₁ ∪ (s₂ ∪ s₃)) := by
  simp only [ext_eq_iff, mem_union_iff, or_assoc, implies_true]

-- CC: While the hope would be to show equality, we must revert to ext_eq
@[simp]
theorem union_empty (s : Set α) : ext_eq (s ∪ ∅) s := by
  simp only [ext_eq_iff, mem_union_iff, not_mem_empty, or_false, implies_true]

@[simp]
theorem empty_union (s : Set α) : ext_eq (∅ ∪ s) s := by
  exact ext_eq_trans (union_comm _ _) (union_empty s)

@[simp]
theorem union_self (s : Set α) : ext_eq (s ∪ s) s := by
  simp only [ext_eq_iff, mem_union_iff, or_self, implies_true]

theorem union_of_subset {s₁ s₂ : Set α} : s₁ ⊆ s₂ → ext_eq (s₁ ∪ s₂) s₂ := by
  intro h
  simp [ext_eq_iff, mem_union_iff]
  simp only [subset_iff] at h
  exact h

-- Mathlib name `union_eq_right`
theorem subset_iff_union_eq_right {s₁ s₂ : Set α} : s₁ ⊆ s₂ ↔ ext_eq (s₁ ∪ s₂) s₂ := by
  simp only [subset_iff, ext_eq_iff, mem_union_iff, or_iff_right_iff_imp]

theorem subset_union_left (s₁ s₂ : Set α) : s₁ ⊆ (s₁ ∪ s₂) := by
  simp only [subset_iff, mem_union_iff]
  intro _ h
  exact Or.inl h

theorem subset_union_right (s₁ s₂ : Set α) : s₂ ⊆ (s₁ ∪ s₂) := by
  simp only [subset_iff, mem_union_iff]
  intro _ h
  exact Or.inr h

/-! # inter -/

section inter

variable [DecidableEq α]

@[simp]
theorem inter_eq_inter_notation (s₁ s₂ : Set α) : inter s₁ s₂ = (s₁ ∩ s₂) := rfl

@[symm]
theorem inter_comm (s₁ s₂ : Set α) : ext_eq (s₁ ∩ s₂) (s₂ ∩ s₁) := by
  simp only [ext_eq_iff, mem_inter_iff, and_comm, implies_true]

theorem inter_assoc (s₁ s₂ s₃ : Set α) : ext_eq ((s₁ ∩ s₂) ∩ s₃) (s₁ ∩ (s₂ ∩ s₃)) := by
  simp only [ext_eq_iff, mem_inter_iff, and_assoc, implies_true]

@[simp]
theorem inter_empty (s : Set α) : ext_eq (s ∩ ∅) ∅ := by
  simp only [ext_eq_iff, mem_inter_iff, not_mem_empty, and_false, implies_true]

@[simp]
theorem empty_inter (s : Set α) : ext_eq (∅ ∩ s) ∅ := by
  exact ext_eq_trans (inter_comm _ _) (inter_empty s)

@[simp]
theorem inter_self (s : Set α) : ext_eq (s ∩ s) s := by
  simp only [ext_eq_iff, mem_inter_iff, and_self, implies_true]

@[simp]
theorem inter_subset_left (s₁ s₂ : Set α) : s₁ ∩ s₂ ⊆ s₁ := by
  simp only [subset_iff, mem_inter_iff, and_imp]
  intros
  assumption

@[simp]
theorem inter_subset_right (s₁ s₂ : Set α) : s₁ ∩ s₂ ⊆ s₂ := by
  simp only [subset_iff, mem_inter_iff, and_imp]
  intros
  assumption

@[simp]
theorem inter_union_left (s₁ s₂ : Set α) : ext_eq (s₁ ∩ (s₁ ∪ s₂)) s₁ := by
  simp only [ext_eq_iff, mem_inter_iff, mem_union_iff, and_iff_left_iff_imp]
  intro _ h
  exact Or.inl h

@[simp]
theorem inter_union_right (s₁ s₂ : Set α) : ext_eq (s₁ ∩ (s₂ ∪ s₁)) s₁ := by
  simp only [ext_eq_iff, mem_inter_iff, mem_union_iff, and_iff_left_iff_imp]
  intro _ h
  exact Or.inr h

@[simp]
theorem union_inter_left (s₁ s₂ : Set α) : ext_eq (s₁ ∪ (s₁ ∩ s₂)) s₁ := by
  simp only [ext_eq_iff, mem_union_iff, mem_inter_iff, or_iff_left_iff_imp, and_imp]
  exact fun _ h _ => h

@[simp]
theorem union_inter_right (s₁ s₂ : Set α) : ext_eq (s₁ ∪ (s₂ ∩ s₁)) s₁ := by
  simp only [ext_eq_iff, mem_union_iff, mem_inter_iff, or_iff_left_iff_imp,
    and_imp, imp_self, implies_true]

theorem union_inter_distrib (s₁ s₂ s₃ : Set α)
    : ext_eq ((s₁ ∪ s₂) ∩ s₃) ((s₁ ∩ s₃) ∪ (s₂ ∩ s₃)) := by
  simp only [ext_eq_iff, mem_inter_iff, mem_union_iff, or_and_right, implies_true]

theorem inter_union_distrib (s₁ s₂ s₃ : Set α)
    : ext_eq ((s₁ ∩ s₂) ∪ s₃) ((s₁ ∪ s₃) ∩ (s₂ ∪ s₃)) := by
  simp only [ext_eq_iff, mem_union_iff, mem_inter_iff, and_or_right, implies_true]

end inter /- section -/

/-! # sdiff -/

section sdiff

variable [DecidableEq α]

@[simp]
theorem sdiff_eq_sdiff_notation (s₁ s₂ : Set α) :
  sdiff s₁ s₂ = (s₁ \ s₂) := rfl

@[simp]
theorem sdiff_subset (s₁ s₂ : Set α) : (s₁ \ s₂) ⊆ s₁ := by
  simp only [subset_iff, mem_sdiff_iff, and_imp]
  intros
  assumption

@[simp]
theorem sdiff_empty (s : Set α) : ext_eq (s \ ∅) s := by
  simp only [ext_eq_iff, mem_sdiff_iff, not_mem_empty, not_false_eq_true, and_true, implies_true]

@[simp]
theorem empty_sdiff (s : Set α) : ext_eq (∅ \ s) ∅ := by
  simp only [ext_eq_iff, mem_sdiff_iff, not_mem_empty, false_and, implies_true]

theorem sdiff_sdiff (s₁ s₂ s₃ : Set α) : ext_eq ((s₁ \ s₂) \ s₃) (s₁ \ (s₂ ∪ s₃)) := by
  simp only [ext_eq_iff, mem_sdiff_iff, and_assoc, mem_union_iff, not_or, implies_true]

theorem sdiff_sdiff_comm (s₁ s₂ s₃ : Set α)
    : ext_eq ((s₁ \ s₂) \ s₃) ((s₁ \ s₃) \ s₂) := by
  simp only [ext_eq_iff, mem_sdiff_iff, and_assoc, and_congr_right_iff]
  simp only [and_comm, implies_true]

@[simp]
theorem sdiff_union_left (s₁ s₂ : Set α) : ext_eq ((s₁ \ s₂) ∪ s₁) s₁ := by
  simp only [ext_eq_iff, mem_union_iff, mem_sdiff_iff, or_iff_right_iff_imp, and_imp]
  exact fun _ h _ => h

@[simp]
theorem sdiff_union_right (s₁ s₂ : Set α) : ext_eq ((s₁ \ s₂) ∪ s₂) (s₁ ∪ s₂) := by
  simp only [ext_eq_iff, mem_union_iff, mem_sdiff_iff]
  intro a
  rcases mem_or_not_mem a s₂ with (h | h)
  <;> simp [h]

end sdiff /- section -/

/-! # insert -/

section insert

variable [DecidableEq α]

@[simp]
theorem insert_eq_insert_notation (a : α) (s : Set α) : insert s a = s + a := rfl

-- set_option trace.Meta.Tactic.simp true
@[simp]
theorem insert_empty (x : α) : ext_eq ((∅ : Set α) + x) {x} := by
  simp only [ext_eq_iff, mem_insert_iff, not_mem_empty, or_false,
    mem_singleton_iff, implies_true]

-- Mathlib name `mem_insert`
@[simp]
theorem mem_insert_self (a : α) (s : Set α) : a ∈ (s + a) := by
  simp only [mem_insert_iff, true_or]

theorem mem_insert_of_mem {b : α} {s : Set α} (h : b ∈ s) (a : α) : b ∈ (s + a) := by
  simp only [mem_insert_iff, h, or_true]

@[simp]
theorem insert_insert_self (a : α) (s : Set α) : ext_eq (s + a + a) (s + a) := by
  simp only [ext_eq_iff, mem_insert_iff, or_self_left, implies_true]

@[simp]
theorem insert_remove_of_mem {a : α} {s : Set α} (h : a ∈ s)
    : ext_eq (s - a + a) s := by
  simp only [ext_eq_iff, mem_insert_iff, mem_remove_iff, ne_eq]
  intro x
  constructor
  · rintro (rfl | ⟨_, h_mem⟩)
    <;> assumption
  · intro h_mem
    by_cases h_eq : x = a
    · exact Or.inl h_eq
    · exact Or.inr ⟨h_eq, h_mem⟩

theorem insert_insert_comm (a b : α) (s : Set α) : ext_eq (s + a + b) (s + b + a) := by
  simp only [ext_eq_iff, mem_insert_iff]
  intro x
  rw [← or_assoc, @or_comm (x = b) (x = a), or_assoc]

theorem insert_union_comm (a : α) (s₁ s₂ : Set α) : ext_eq ((s₁ + a) ∪ s₂) ((s₁ ∪ s₂) + a) := by
  rw [ext_eq_iff]; intro x
  simp only [mem_union_iff, mem_insert_iff, or_assoc]

theorem insert_eq_union_singleton (a : α) (s : Set α) : ext_eq (s + a) (s ∪ {a}) := by
  rw [ext_eq_iff]; intro x
  simp only [mem_insert_iff, mem_union_iff, mem_singleton_iff, or_comm]

end insert /- section -/

/-! # remove -/

section remove

variable [DecidableEq α]

@[simp]
theorem remove_eq_remove_notation (a : α) (s : Set α) : remove s a = s - a := rfl

@[simp]
theorem remove_empty (a : α) : ext_eq ((∅ : Set α) - a) ∅ := by
  rw [ext_eq_iff]; intro x
  simp only [mem_remove_iff, ne_eq, not_mem_empty, and_false]

@[simp]
theorem remove_singleton_self (a : α) : ext_eq (({a} : Set α) - a) ∅ := by
  rw [ext_eq_iff]; intro x
  simp only [mem_remove_iff, ne_eq, mem_singleton_iff, not_and_self, not_mem_empty]

@[simp]
theorem remove_singleton_eq_empty_iff (a b : α) : ext_eq (({a} : Set α) - b) ∅ ↔ a = b := by
  constructor
  · intro h
    have h_iff := ext_eq_iff.mp h
    simp only [mem_remove_iff, ne_eq, mem_singleton_iff,
        not_mem_empty, iff_false, not_and] at h_iff
    false_or_by_contra
    rename_i h_con
    have := h_iff a h_con
    contradiction
  · rintro rfl
    simp only [remove_singleton_self]

@[simp]
theorem not_mem_remove_self (a : α) (s : Set α) : a ∉ s - a := by
  simp only [mem_remove_iff, ne_eq, not_true_eq_false, false_and, not_false_eq_true]

theorem not_mem_remove_iff {a b : α} {s : Set α} : b ∉ (s - a) ↔ b = a ∨ b ∉ s := by
  simp only [mem_remove_iff, ne_eq, not_and]
  constructor
  · intro h_imp
    by_cases hba : b = a
    · exact Or.inl hba
    · exact Or.inr <| h_imp hba
  · rintro (rfl | h_mem)
    · simp only [not_true_eq_false, false_implies]
    · exact fun _ => h_mem

theorem remove_of_not_mem {a : α} {s : Set α} (h : a ∉ s) : ext_eq (s - a) s := by
  simp only [ext_eq_iff, mem_remove_iff]
  intro x
  constructor
  . intro hs
    exact hs.2
  . intro hs
    have hne : x ≠ a := by
      intro h_eq
      rw [h_eq] at hs
      exact h hs
    exact ⟨hne, hs⟩

@[simp]
theorem remove_remove_self (a : α) (s : Set α) : ext_eq (s - a - a) (s - a) := by
  rw [ext_eq_iff]; intro x
  simp only [mem_remove_iff, ne_eq, and_self_left]

theorem sdiff_singleton_eq_remove (a : α) (s : Set α)
    : ext_eq (s \ {a}) (s - a) := by
  rw [ext_eq_iff]; intro x
  simp only [mem_remove_iff, ne_eq, mem_sdiff_iff, mem_singleton_iff, and_comm]

end remove /- section -/

/-! # disjoint -/

section disjoint

variable [DecidableEq α]

theorem disjoint_iff_inter_eq_empty {s₁ s₂ : Set α} :
    disjoint s₁ s₂ ↔ ext_eq (s₁ ∩ s₂) ∅ := by
  simp only [disjoint_iff, mem_inter_iff, not_and]

theorem disjoint_comm {s₁ s₂ : Set α} : disjoint s₁ s₂ ↔ disjoint s₂ s₁ := by
  simp only [disjoint_iff]
  have h := inter_comm s₁ s₂
  constructor
  · intro h'
    exact ext_eq_trans (ext_eq_comm.1 h) h'
  . intro h'
    exact ext_eq_trans h h'

@[simp]
theorem disjoint_empty (s : Set α) : disjoint s ∅ := by
  simp only [disjoint_iff_inter_eq_empty, inter_empty]

@[simp]
theorem empty_disjoint (s : Set α) : disjoint ∅ s := by
  simp only [disjoint_iff_inter_eq_empty, empty_inter]

@[simp]
theorem disjoint_self_iff (s : Set α) : disjoint s s ↔ ext_eq s ∅ := by
  simp [disjoint_iff]
  have := inter_self s
  constructor
  · intro h
    rw [ext_eq_comm] at h ⊢
    exact ext_eq_trans h this
  · intro h
    exact ext_eq_trans this h

@[simp]
theorem disjoint_sdiff (s₁ s₂ : Set α) : disjoint s₁ (s₂ \ s₁) := by
  simp [disjoint_iff, ext_eq_iff, mem_inter_iff, mem_sdiff_iff]
  exact fun _ h _ => h

end disjoint /- section -/

/-! # filter -/

section filter

@[simp]
theorem filter_subset (p : α → Bool) (s : Set α) :
    filter s p ⊆ s := by
  simp only [subset_iff, mem_filter_iff, and_imp]
  intros
  assumption

@[simp]
theorem filter_trivial_true (s : Set α) : ext_eq (filter s (fun _ => true)) s := by
  rw [ext_eq_iff]; intro x
  simp only [mem_filter_iff, and_true]

@[simp]
theorem filter_trivial_false (s : Set α) : ext_eq (filter s (fun _ => false)) ∅ := by
  rw [ext_eq_iff]; intro x
  simp only [mem_filter_iff, Bool.false_eq_true, and_false, not_mem_empty]

@[simp]
theorem filter_filter_self (p : α → Bool) (s : Set α) :
    ext_eq (filter (filter s p) p) (filter s p) := by
  rw [ext_eq_iff]; intro x
  simp only [mem_filter_iff, and_self_right]

@[simp]
theorem filter_filter (p q : α → Bool) (s : Set α) :
    ext_eq (filter (filter s p) q) (filter s (fun x => p x && q x)) := by
  rw [ext_eq_iff]; intro x
  simp only [mem_filter_iff, and_assoc, Bool.and_eq_true]

theorem filter_filter_comm (p q : α → Bool) (s : Set α) :
    ext_eq (filter (filter s p) q) (filter (filter s q) p) := by
  rw [ext_eq_iff]; intro x
  simp only [filter_filter, mem_filter_iff, and_assoc, and_comm (a := p x) (b := q x)]

theorem filter_subset_filter_of_subset {s₁ s₂ : Set α}
    : s₁ ⊆ s₂ → ∀ (p : α → Bool), filter s₁ p ⊆ filter s₂ p := by
  intro h p
  simp only [subset_iff, mem_filter_iff, and_imp]
  intro a h_mem hp
  exact ⟨(subset_iff.mp h) _ h_mem, hp⟩

theorem filter_subset_of_subset {s₁ s₂ : Set α}
    : s₁ ⊆ s₂ → ∀ (p : α → Bool), filter s₁ p ⊆ s₂ :=
  fun h p => subset_trans (filter_subset_filter_of_subset h p) (filter_subset _ _)

end filter /- section -/

/-! # map -/

section map

theorem map_eq_of_ext_eq (f : α → β) (s₁ s₂ : Set α)
    : ext_eq s₁ s₂ → ext_eq (s₁.map f) (s₂.map f) := by
  simp [ext_eq_iff]
  intro h
  simp only [mem_map_iff, exists_eq_left]
  intro x
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, (h x).1 hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, (h x).2 hx, rfl⟩

theorem functor_map_eq_of_ext_eq {α β : Type u} (f : α → β) (s₁ s₂ : Set α)
    : ext_eq s₁ s₂ → ext_eq (f <$> s₁) (f <$> s₂) := by
  apply map_eq_of_ext_eq

-- TODO Might want to use `ext_eq` instead of `=` here, because otherwise we break the API
@[simp]
theorem map_empty (f : α → β) : ((∅ : Set α).map f) = ∅ := by
  simp [map, empty]; rfl

theorem map_map (f : α → β) (g : β → γ) (s : Set α)
    : (s.map f).map g = s.map (g ∘ f) := by
  simp [map]

@[simp]
theorem map_singleton (f : α → β) (a : α) : (({a} : Set α).map f) = ({f a} : Set β) := by
  -- TODO breaks API
  simp [map, singleton]; rfl

theorem map_union (f : α → β) (s₁ s₂ : Set α)
    : ext_eq ((s₁ ∪ s₂).map f) ((s₁.map f) ∪ (s₂.map f)) := by
  rw [ext_eq_iff]; intro x
  simp only [mem_map_iff, mem_union_iff, or_and_right, exists_or]

theorem map_ofList (f : α → β) (l : List α)
    : ext_eq ((ofList l : Set α).map f) (ofList (l.map f)) := by
  rw [ext_eq_iff]; intro x
  simp only [mem_map_iff, mem_ofList_iff, List.mem_map]

variable [DecidableEq α] [DecidableEq β]

theorem map_inter (f : α → β) (S₁ S₂ : Set α)
    : (S₁ ∩ S₂).map f ⊆ (S₁.map f) ∩ (S₂.map f) := by
  simp [subset_iff, mem_map_iff, mem_inter_iff]
  rintro b a ha₁ ha₂ rfl
  exact ⟨⟨a, ha₁, rfl⟩, ⟨a, ha₂, rfl⟩⟩

theorem map_insert (f : α → β) (a : α) (s : Set α)
    : ext_eq ((s + a).map f) ((s.map f) + (f a)) := by
  simp only [ext_eq_iff, mem_map_iff, mem_insert_iff, exists_eq_or_imp]
  intro x
  constructor
  all_goals (
    rintro (rfl | h)
    · exact Or.inl rfl
    · exact Or.inr h
  )

end map /- section -/

/-! # cardinality -/

section card

variable [DecidableEq α]

-- Helper Lemma for `card_ge_one_of_mem`
theorem card_ge_one_of_ne_nil {l : List α} (h_ne_nil : l ≠ []) : card (mk l) ≥ 1 := by
  -- We prove this by induction on the list `l`.
  induction l with
  | nil => contradiction
  | cons x xs ih => -- Inductive Step: `l` is `x :: xs`.
    simp only [card]
    split <;> rename_i h_mem -- Split on whether `x` is in the tail `xs`.
    · -- Case 1: `x ∈ xs`. The card is `card (mk xs)`.
      have h_xs_ne_nil : xs ≠ [] := by
        rintro rfl; simp_all
      exact ih h_xs_ne_nil -- apply ih to the non-empty tail
    · -- Case 2: `x ∉ xs`. The card is `card (mk xs) + 1` which is always ≥ 1.
      exact Nat.succ_le_succ (Nat.zero_le _)

-- Helper Lemma for `card_eq_zero_iff`: If a set has a member, its card is ≥ 1.
theorem card_ge_one_of_mem {a : α} {s : Set α} (h_mem : a ∈ s) : s.card ≥ 1 := by
  have h_ne_nil : s.toList ≠ [] := by
    intro h_nil
    rw [←mem_toList_iff, h_nil] at h_mem
    contradiction
  exact card_ge_one_of_ne_nil h_ne_nil

theorem card_eq_zero_iff (s : Set α) : card s = 0 ↔ ext_eq s ∅ := by
  rw [eq_empty_iff]
  constructor
  · -- Direction 1: card s = 0 → ∀ a, a ∉ s
    intro h_card_zero
    intro a ha
    have hh := card_ge_one_of_mem ha
    rw [h_card_zero] at hh
    contradiction
  · -- Direction 2: (∀ a, a ∉ s) → card s = 0
    intro h_all_not_mem
    match s with
    | mk l =>
      induction l with
      | nil => simp [card]
      | cons x xs ih =>
        have h_x_in : x ∈ x :: xs := by simp
        specialize h_all_not_mem x
        contradiction

@[simp]
theorem card_singleton (a : α) : card ({a} : Set α) = 1 := by
  change card ((∅ : Set α) + a) = 1
  simp [card_insert]

@[simp]
theorem card_pos_iff_ne_empty {s : Set α} : 0 < card s ↔ ¬(ext_eq s ∅) := by
  -- TODO: Probably a one-line proof via `mt` or something similar
  constructor
  · intro h h_con
    rw [(card_eq_zero_iff (s := s)).mpr h_con] at h
    contradiction
  · rw [← Nat.ne_zero_iff_zero_lt]
    intro h h_con
    have := (card_eq_zero_iff (s := s)).mp h_con
    contradiction

end card /- section -/

end Set /- namespace -/

end Vstd

#exit

instance instLawfulSingleton : LawfulSingleton α (Set α) where
  insert_empty_eq := insert_empty

end VSetLikeF /- namespace -/

/-! # finite sets -/
namespace VSetF

open VSetLikeF LawfulVSetLikeF LawfulVSetF

variable {S : Type u → Type v} [VSetF S] [LawfulVSetF S] [∀ (a : α) (s : Set α), Decidable (a ∈ s)]

/-! # card -/

-- Cedar does not seem to have theorems for cardinality? (`size`)

-- CZ: Previous version intends to prove `card_union` (via induction?) then use it to prove `card_disjoint`.
-- I find it easier to prove `card_disjoint` first then use it to prove the general case `card_union`.

-- Define a decidable version of sets
variable {dS : Type u → Type v} (α : Type u) [DecidableEq α] [VSetF dS] [LawfulVSetF dS]

-- instance dr : DecidableRel (fun (x : α) (s : dSet α) => x ∈ s) := by infer_instance
  -- rw [DecidableRel]
  -- intro a s
  -- exact decidable_of_iff (a ∈ VSetF.toList s) (LawfulVSetF.mem_toList_iff (s := s) a).symm

-- instance dr' : Decidable (x : α) (s₁ : dSet α) (s₂ : dSet α) => (a ∈ s₁)) := by
--   intro a s
--   exact decidable_of_iff (a ∈ VSetF.toList s) (LawfulVSetF.mem_toList_iff (s := s) a).symm

-- instance {s₁ s₂ : dSet α} : Decidable (disjoint s₁ s₂) := by
--   have h_dec : ∀ a, Decidable (¬(a ∈ s₁ ∧ a ∈ s₂)) := fun a => inferInstance
--   have (s : dSet α) : Decidable (s = ∅) := by rw [← card_eq_zero_iff]; exact inferInstance
--   refine decidable_of_iff (s₁ ∩ s₂ = ∅) ?_
--   simp only [disjoint_iff_inter_eq_empty, disjoint_iff]

theorem card_disjoint {s₁ s₂ : dSet α} (h_disj : disjoint s₁ s₂) :
    card (s₁ ∪ s₂) = card s₁ + card s₂ := by
  let P (k : Nat) := -- The property we are inducting on for a given cardinality k
  ∀ (s₁_hyp : dSet α) (s₂_hyp : dSet α),
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
    by_cases h_s2_hyp_empty : s₂_hyp = (∅ : dSet α)
    · -- If s₂_hyp is empty, then k_val = 0.
      have : union s₁_hyp ∅ = s₁_hyp := by
        exact union_empty s₁_hyp
      rw [h_s2_hyp_empty, this, card_empty, Nat.add_zero]

    · -- s₂_hyp is not empty
      have h_s2_hyp_ne_empty : s₂_hyp ≠ (∅ : dSet α) := h_s2_hyp_empty
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


theorem card_union (s₁ s₂ : dSet α)
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
