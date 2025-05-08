import VerusLean.Vstd.Map.Defs

namespace Vstd

namespace VMapLikeF

variable {M : Type u → Type v → Type w} [VMapLikeF M] [LawfulVMapLikeF M] {α : Type u} {β : Type v}

@[simp]
theorem insert_insert (m : M α β) (k : α) (v₁ v₂ : β) :
    insert (insert m k v₁) k v₂ = insert m k v₂ := by
  ext
  stop
  done

end VMapLikeF /- namespace -/

namespace VMap

end VMap
