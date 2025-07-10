import VerusLean.Vstd.Set
#exit
namespace Vstd

/--
  Verus `Vstd` maps.
-/
class VMapLikeF (M : Type u → Type v → Type w)
  (S_key : outParam (Type u → Type x)) [VSetLikeF S_key]
  (S_val : outParam (Type v → Type y)) [VSetLikeF S_val]
  where
  empty : M α β
  -- do we want an infinite map type class?
  total : (α → β) → M α β
  new : (α → Bool) → (α → β) → M α β
  fromSet : (S_key α) → (α → β) → M α β
  -- keys : M α β → Set α
  -- values : M α β → Set β
  keys : M α β → S_key α
  values : M α β → S_val β
  memKeys [DecidableEq α] : M α β → α → Prop :=
    fun m k => k ∈ keys m
  memValues : M α β → β → Prop :=
    fun m v => v ∈ values m
  -- CZ: how does implementation guarantee this is decidable?
  -- memKeys [DecidableEq α] [Decidable (k ∈ keys m)] : M α β → α → Bool
    -- := fun m k => decide (k ∈ keys m)
  -- memValues : M α β → β → Bool
  get? [DecidableEq α] : M α β → α → Option β
  get [DecidableEq α] [Inhabited β] : (m : M α β) → (k : α) → (h : memKeys m k) → β
  get! [DecidableEq α] [Inhabited β] : (m : M α β) → (k : α) → β
  insert : (m : M α β) → (k : α) → (v : β) → M α β
  remove : (m : M α β) → (k : α) → M α β
  removeKeys : (m : M α β) → (ks : Set α) → M α β
  restrict : (m : M α β) → (ks : Set α) → M α β
  isEqualOnKey [DecidableEq α] [DecidableEq β] : (m₁ m₂ : M α β) → (k : α) → Bool
  agrees [DecidableEq α] [DecidableEq β] : (m₁ m₂ : M α β) → Bool
  size : M α β → Nat
  submapOf {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β] : M α β → M α β → Bool
  union_prefer_right [DecidableEq α] : (m₁ m₂ : M α β) → M α β
  union_prefer_left [DecidableEq α] : (m₁ m₂ : M α β) → M α β :=
    fun m₁ m₂ => union_prefer_right m₂ m₁
  mapEntires : (m : M α β) → (f : α → β → γ) → M α γ
  mapValues : (m : M α β) → (f : β → γ) → M α γ
  isInjective : (m : M α β) → Bool
  ofList : List (α × β) → M α β :=
    fun l => l.foldl (fun m p => insert m p.1 p.2) empty

namespace VMapLikeF

-- variable {M : Type u → Type v → Type w} [VMapLikeF M] {α : Type u} {β : Type v}
variable {M : Type u → Type v → Type w} {S_key : Type u → Type w_key} [VSetLikeF S_key]
  {S_val : Type v → Type w_val} [VSetLikeF S_val] [VMapLikeF M S_key S_val] {α : Type u} {β : Type v}

abbrev domain (m : M α β) : S_key α := keys m
abbrev range (m : M α β) : S_val β := values m
abbrev codomain (m : M α β) : S_val β := values m

instance instEmptyCollection : EmptyCollection (M α β) := ⟨empty⟩
instance instInhabited : Inhabited (M α β) := ⟨empty⟩
instance instSingleton : Singleton (α × β) (M α β) := ⟨fun p => insert ∅ p.1 p.2⟩
instance instInsert : Insert (α × β) (M α β) := ⟨fun p m => insert m p.1 p.2⟩
instance instMembershipKeys [DecidableEq α] : Membership α (M α β) := ⟨fun m k => memKeys m k = true⟩
instance instMembershipValues : Membership β (M α β) := ⟨fun m v => memValues m v = true⟩
instance instMembership [DecidableEq α] [Inhabited β] : Membership (α × β) (M α β) := ⟨fun m p => p.1 ∈ keys m ∧ p.2 ∈ values m ∧ get! m p.1 = p.2⟩
instance instUnion [DecidableEq α] : Union (M α β) := ⟨union_prefer_right⟩
instance instCoeOfList : Coe (List (α × β)) (M α β) := ⟨ofList⟩
instance instGetElem [DecidableEq α] [Inhabited β] : GetElem (M α β) α β (fun m k => memKeys m k) := ⟨get⟩
instance instGetElem? [DecidableEq α] [Inhabited β] : GetElem? (M α β) α β (fun m k => memKeys m k) where
  getElem? := get?
  getElem! := get!

end VMapLikeF /- namespace -/

class LawfulVMapLikeF
  (M : Type u₁ → Type v₁ → Type w₁)
  (S_key : outParam (Type u₁ → Type w_key)) [VSetLikeF S_key] [LawfulVSetLikeF S_key]
  (S_val : outParam (Type v₁ → Type w_val)) [VSetLikeF S_val] [LawfulVSetLikeF S_val]
  extends
    VMapLikeF M S_key S_val
  where
  protected ext [DecidableEq α] (m₁ m₂ : M α β) : (∀ (k : α), k ∈ keys m₁ ↔ k ∈ keys m₂ ∧ get? m₁ k = get? m₂ k) → m₁ = m₂
  keys_empty : keys (∅ : M α β) = ∅
  values_empty : values (∅ : M α β) = ∅
  memKeys_iff [DecidableEq α] : ∀ (m : M α β) (k : α), memKeys m k ↔ k ∈ keys m
  memValues_iff : ∀ (m : M α β) (v : β), memValues m v ↔ v ∈ values m
  mem_insert_iff {α β} [DecidableEq α] [Inhabited β] {k₁ k₂ : α} {v₁ v₂ : β} {m : M α β} :
    (k₂, v₂) ∈ (insert m k₁ v₁) ↔ (k₁ = k₂ ∧ v₁ = v₂) ∨ (k₂, v₂) ∈ m
  memKeys_insert_iff {α β} {k₁ k₂ : α} {v₁ v₂ : β} {m : M α β} :
    k₂ ∈ keys (insert m k₁ v₁) ↔ k₂ = k₁ ∨ k₂ ∈ keys m
  mem_remove_iff {α β} [DecidableEq α] [Inhabited β] {k₁ k₂ : α} {v : β} {m : M α β} :
    (k₂, v) ∈ (remove m k₁) ↔ k₂ ≠ k₁ ∧ (k₂, v) ∈ m
  memKeys_remove_iff {α β} [DecidableEq α] {k₁ k₂ : α} {m : M α β} :
    k₂ ∈ keys (remove m k₁) ↔ k₂ ≠ k₁ ∧ k₂ ∈ keys m

  get?_insert [DecidableEq α] (k₁ k₂ : α) (v : β) (m : M α β) :
    get? (insert m k₁ v) k₂ = if k₁ = k₂ then some v else get? m k₂
  get?_remove [DecidableEq α] (k₁ k₂ : α) (m : M α β) :
    get? (remove m k₁) k₂ = if k₁ = k₂ then none else get? m k₂

  memKeys_insert {α β} [DecidableEq α] (k : α) (v : β) (m : M α β) :
    memKeys (insert m k v) k

open LawfulVMapLikeF in
attribute [simp] keys_empty values_empty
-- attribute [ext] LawfulVMapLikeF.ext

-- class VMapF (M : Type u → Type v → Type w)
--   extends
--     VMapLikeF M

-- class VMap (M : Type u → Type v → Type w) (α : Type u) (β : Type v)
--   extends VMapLikeF M

-- class LawfulVMap (M : Type u → Type v → Type w) (α : Type u) (β : Type v)
--   extends
--     LawfulVMapLikeF M,
--     LawfulGetElem (M α β) α β (fun m k => memKeys m k)
--   where


end Vstd
