import VerusLean.Vstd.Set

namespace Vstd

open Set

inductive Map (α : Type u) (β : Type v)
  | mk (elems : Set (α × β))

namespace Map

variable {α : Type u} {β : Type v} {γ : Type w}

-- SHIM
def empty : Map α β :=
  mk ∅

instance instEmptyCollection : EmptyCollection (Map α β) where
  emptyCollection := empty

instance instInhabited : Inhabited (Map α β) where
  default := ∅

-- SHIM
def singleton (a : α) (b : β) : Map α β :=
  mk {(a, b)}

instance instSingleton : Singleton (α × β) (Map α β) where
  singleton := fun p => singleton p.1 p.2

def fromSet (s : Set α) (f : α → β) : Map α β :=
  mk <| s.map (fun a => (a, f a))

-- SHIM
def keys (m : Map α β) : Set α :=
  match m with
  | mk elems => elems.map Prod.fst

-- SHIM
def values (m : Map α β) : Set β :=
  match m with
  | mk elems => elems.map Prod.snd

/-

-- CC: TODO insert a `bmem` section?

-/

section get

-- CC: Ideally, we don't need `DecidableEq β` or `Inhabited` here, but I'm lazy atm
variable [DecidableEq α] [DecidableEq β] [Inhabited α] [Inhabited β]

-- SHIM
def get? (m : Map α β) (k : α) : Option β :=
  match m with
  | mk elems =>
    -- TODO: Not very efficient, but works for now
    if k ∈ m.keys then
      some <| Prod.snd <| Set.choose <| elems.filter (·.1 = k)
    else
      none

-- SHIM
def get (m : Map α β) (k : α) (h : k ∈ keys m) : β :=
  match m with
  | mk elems =>
    Prod.snd <| Set.choose <| elems.filter (·.1 = k)

-- SHIM
def get! (m : Map α β) (k : α) : β :=
  match get? m k with
  | some v => v
  | none => default

instance instGetElem : GetElem (Map α β) α β (fun m k => k ∈ keys m) where
  getElem := get

instance instGetElem? : GetElem? (Map α β) α β (fun m k => k ∈ keys m) where
  getElem? := get?

end get /- section -/

-- CC: Remove these later? I'm lazy
variable [DecidableEq α] [DecidableEq β] [Inhabited α] [Inhabited β]

def ext_eq (m₁ m₂ : Map α β) : Prop :=
  ∀ (k : α), k ∈ keys m₁ ↔ k ∈ keys m₂ ∧ m₁[k]? = m₂[k]?

-- SHIM
def insert (m : Map α β) (k : α) (v : β) : Map α β :=
  match m with
  | mk elems =>
    mk <|
      if k ∈ keys m then
        let elems' := elems.filter (fun p => p.1 ≠ k)
        elems' + (k, v)
      else
        elems + (k, v)

-- SHIM
def remove (m : Map α β) (k : α) : Map α β :=
  match m with
  | mk elems =>
    mk <| elems.filter (fun p => p.1 ≠ k)

-- CC TODO: What's the best name to use here? Verus uses "len"
def size (m : Map α β) : Nat :=
  match m with
  | mk elems => card elems


/-! # lemmas -/

set_option linter.unusedSectionVars false

-- SHIM
@[simp]
theorem keys_empty : keys (∅ : Map α β) = ∅ := by
  simp [keys, empty]

-- SHIM
@[simp]
theorem values_empty : values (∅ : Map α β) = ∅ := by
  simp [values, empty]

-- SHIM?
@[simp]
theorem keys_singleton (a : α) (b : β) : keys ({(a, b)} : Map α β) = {a} := by
  simp [keys, singleton]

-- SHIM?
@[simp]
theorem values_singleton (a : α) (b : β) : values ({(a, b)} : Map α β) = {b} := by
  simp [values, singleton]

-- SHIM
theorem keys_insert (m : Map α β) (k : α) (v : β)
    : keys (insert m k v) = if k ∈ keys m then keys m else keys m + k := by
  simp [insert]
  by_cases h : k ∈ keys m
  · simp [h]
    stop
    done
  · stop
    done
  done

end Map

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
  -- CZ: how does implementation guarantee this is decidable?
  -- memKeys [DecidableEq α] [Decidable (k ∈ keys m)] : M α β → α → Bool
    -- := fun m k => decide (k ∈ keys m)
  -- memValues : M α β → β → Bool
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
