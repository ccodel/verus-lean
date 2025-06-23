import VerusLean.Vstd.Set.Defs
import VerusLean.Vstd.Map.Defs

namespace Vstd

namespace VMapLikeF

/-! # lawful maps -/
open LawfulVMapLikeF

variable {M : Type u → Type v → Type w}
variable {S_key : Type u → Type w_key} [VSetLikeF S_key] [LawfulVSetLikeF S_key]
variable {S_val : Type v → Type w_val} [VSetLikeF S_val] [LawfulVSetLikeF S_val]
variable [LawfulVMapLikeF M S_key S_val]

variable {α : Type u} {β : Type v} [DecidableEq α]

-- CZ: If M is a lawful map, can we show that its domain is a lawful set?
-- Maybe not - let's try write this as a definition

omit [DecidableEq α]  in
theorem map_empty : keys (∅ : M α β) = ∅ := by
  simp

theorem map_insert_domain (m : M α β) (key : α) (value : β):
  keys (insert m key value) = VSetLikeF.insert (keys m) key := by
  apply LawfulVSetLikeF.ext
  intro x
  by_cases h : x = key
  . simp [h]
    simp only [←memKeys_iff, memKeys_insert]
  . simp [LawfulVSetLikeF.mem_insert_iff, h]
    rw [memKeys_insert_iff]
    simp [h]
    exact value -- why do we need to show that `keys m` is inhabited?

theorem map_insert_same (m : M α β) (key : α) (value : β):
  get? (insert m key value) key = some value := by
  simp [get?_insert]

theorem map_insert_different (m : M α β) (key₁ key₂: α) (value : β) (h : key₁ ≠ key₂):
  get? (insert m key₂ value) key₁ = get? m key₁ := by
  simp [get?_insert]
  intro h'; rw [h'] at h
  contradiction

theorem map_remove_domain (m : M α β) (key : α):
  keys (remove m key) = VSetLikeF.remove key (keys m) := by
  apply LawfulVSetLikeF.ext
  intro x
  by_cases h : x = key
  . simp [h, memKeys_remove_iff]
  . simp [h, memKeys_remove_iff, LawfulVSetLikeF.mem_remove_iff]

theorem map_remove_different (m : M α β) (key₁ key₂: α) (h : key₁ ≠ key₂):
  get? (remove m key₂) key₁ = get? m key₁ := by
  simp [get?_remove]
  intro h'; rw [h'] at h
  contradiction

theorem map_ext_equal (m₁ m₂ : M α β) :
  (∀ (k : α), k ∈ keys m₁ ↔ k ∈ keys m₂ ∧ get? m₁ k = get? m₂ k) → m₁ = m₂ := by
  apply LawfulVMapLikeF.ext

@[simp]
theorem insert_insert (m : M α β) (k : α) (v₁ v₂ : β) :
    insert (insert m k v₁) k v₂ = insert m k v₂ := by
  apply LawfulVMapLikeF.ext
  intro x
  by_cases h : x = k
  . simp only [h, memKeys_insert_iff]
    simp [get?_insert, ←memKeys_iff, memKeys_insert]
  . rw [get?_insert]
    have h' : ¬k = x := by
      intro p; have p' := p.symm; contradiction
    simp [h', get?_insert]
    rw [memKeys_insert_iff]
    . simp [h]
      rw [memKeys_insert_iff]
      . simp [h]
        rw [memKeys_insert_iff]
        . simp [h]
        . exact v₁
      . exact v₁
    . exact v₁

end VMapLikeF /- namespace -/

namespace VMap

end VMap
