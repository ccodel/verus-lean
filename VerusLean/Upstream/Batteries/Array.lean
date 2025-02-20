import Batteries.Data.Array

namespace Array

@[simp] theorem zipWith_empty_left {α β γ : Type u} (f : α → β → γ) (as : Array β) : zipWith f #[] as = #[] := rfl
@[simp] theorem zipWith_empty_right {α β γ : Type u} (f : α → β → γ) (as : Array α) : zipWith f as #[] = #[] := by
  have ⟨as⟩ := as
  induction as <;> simp

@[simp] theorem zipWith_nil_left {α β γ : Type u} (f : α → β → γ) (as : Array β) : zipWith f ({ toList := [] } : Array α) as = #[] := rfl
@[simp] theorem zipWith_nil_right {α β γ : Type u} (f : α → β → γ) (as : Array α) : zipWith f as ({ toList := [] } : Array β) = #[] := by
  have ⟨as⟩ := as
  induction as <;> simp

end Array
