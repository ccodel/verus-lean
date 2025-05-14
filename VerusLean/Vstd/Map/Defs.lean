import VerusLean.Vstd.Set

namespace Vstd

/--
  Verus `Vstd` maps.
-/
class VMapLikeF (M : Type u → Type v → Type w)

  where
  empty : M α β
  keys : M α β → Set α
  values : M α β → Set β
  memKeys : M α β → α → Prop :=
    fun m k => k ∈ keys m
  memValues : M α β → β → Prop :=
    fun m v => v ∈ values m
  get? : M α β → α → Option β
  get : (m : M α β) → (k : α) → (h : memKeys m k) → β
  get! {α : Type u} {β : Type v} [Inhabited β] : (m : M α β) → (k : α) → β
  insert : (m : M α β) → (k : α) → (v : β) → M α β
  remove : (m : M α β) → (k : α) → M α β
  union_prefer_right : (m₁ m₂ : M α β) → M α β
  union_prefer_left : (m₁ m₂ : M α β) → M α β :=
    fun m₁ m₂ => union_prefer_right m₂ m₁
  mapValues : (m : M α β) → (f : β → γ) → M α γ
  ofList : List (α × β) → M α β :=
    fun l => l.foldl (fun m p => insert m p.1 p.2) empty

namespace VMapLikeF

variable {M : Type u → Type v → Type w} [VMapLikeF M] {α : Type u} {β : Type v}

abbrev domain (m : M α β) : Set α := keys m
abbrev range (m : M α β) : Set β := values m
abbrev codomain (m : M α β) : Set β := values m

instance instEmptyCollection : EmptyCollection (M α β) := ⟨empty⟩
instance instInhabited : Inhabited (M α β) := ⟨empty⟩
instance instSingleton : Singleton (α × β) (M α β) := ⟨fun p => insert ∅ p.1 p.2⟩
instance instInsert : Insert (α × β) (M α β) := ⟨fun p m => insert m p.1 p.2⟩
instance instMembershipKeys : Membership α (M α β) := ⟨memKeys⟩
instance instMembershipValues : Membership β (M α β) := ⟨memValues⟩
instance instMembership : Membership (α × β) (M α β) := ⟨fun m p => p.1 ∈ m ∧ p.2 ∈ m⟩
instance instUnion : Union (M α β) := ⟨union_prefer_right⟩
instance instCoeOfList : Coe (List (α × β)) (M α β) := ⟨ofList⟩
instance instGetElem : GetElem (M α β) α β (fun m k => memKeys m k) := ⟨get⟩
instance instGetElem? : GetElem? (M α β) α β (fun m k => memKeys m k) where
  getElem? := get?
  getElem! := get!

end VMapLikeF /- namespace -/

class LawfulVMapLikeF (M : Type u → Type v → Type w)
  extends
    VMapLikeF M
  where
  protected ext (m₁ m₂ : M α β) : (∀ (k : α), k ∈ keys m₁ ↔ k ∈ keys m₂) → (∀ (k : α), get? m₁ k = get? m₂ k) → m₁ = m₂
  keys_empty : keys (∅ : M α β) = ∅
  values_empty : values (∅ : M α β) = ∅
  memKeys_iff : ∀ (m : M α β) (k : α), memKeys m k ↔ k ∈ keys m
  memValues_iff : ∀ (m : M α β) (v : β), memValues m v ↔ v ∈ values m
  mem_insert_iff {k k' : α} {v v' : β} {m : M α β}
      : (k', v') ∈ (insert m k v) ↔ (k = k' ∧ v = v') ∨ (k', v') ∈ m

open LawfulVMapLikeF in
attribute [simp] keys_empty values_empty
attribute [ext] LawfulVMapLikeF.ext

class VMapF (M : Type u → Type v → Type w)
  extends
    VMapLikeF M

class VMap (M : Type u → Type v → Type w) (α : Type u) (β : Type v)
  extends VMapLikeF M

class LawfulVMap (M : Type u → Type v → Type w) (α : Type u) (β : Type v)
  extends
    LawfulVMapLikeF M,
    LawfulGetElem (M α β) α β (fun m k => memKeys m k)

end Vstd
