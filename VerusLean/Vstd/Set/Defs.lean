import VerusLean.Vstd.Seq
import Std.Data.HashMap

namespace Vstd

/--
  Verus `Vstd` sets.
-/
-- TODO: consider the following approach to make it
-- so in the testfile, either a generic `S` or a specific `Set` can be used?
-- instead of {S: } [], write [S: ]
class VSetLikeF (S : Type u → Type v)
  extends
    Functor S
  where
  map' : {α β : Type u} → (s : S α) → (f : α → β) → S β := fun s f => Functor.map f s
  mem : {α : Type u} → S α → α → Prop
  -- mem : {α : Type u} → S α → α → Bool -- if [DecidableEq α] here then Shim.lean can be Cedar's defn, but then not sure how to satisfy `instance instMembership`
  empty : {α : Type u} → S α -- why is the empty set an infinite set in Verus?
  insert : {α : Type u} → S α → α → S α
  remove : {α : Type u} → α → S α → S α
  singleton : {α : Type u} → α → S α :=
    fun a => insert empty a
  -- To get around `noncomputable instance` for `Shim.lean`, we enforce that `α` be inhabited.
  -- choose {α : Type u} [Inhabited α] : (s : S α) → (h : ∃ x, mem s x) → α
  /- CZ: How about that we don't require (h : ∃ x, mem s x), and just say we
     don't care what ∅.choose returns, as long as α is inhabited it's fine -/
  choose {α : Type u} [Inhabited α] : S α → α
  subset : {α : Type u} → S α → S α → Prop := -- Cedar's defn is Bool instead of Prop, same below
    fun s₁ s₂ => ∀ a, mem s₁ a → mem s₂ a
  union : {α : Type u} → S α → S α → S α
  inter : {α : Type u} → S α → S α → S α
  sdiff : {α : Type u} → S α → S α → S α
  symmDiff : {α : Type u} → S α → S α → S α :=
    fun s₁ s₂ => union (sdiff s₁ s₂) (sdiff s₂ s₁)
  disjoint : {α : Type u} → S α → S α → Prop :=
    fun s₁ s₂ => ∀ a, ¬(mem (inter s₁ s₂) a)
  -- filter {α : Type u} (s : S α) (pred : α → Bool) : S α
  filter : {α : Type u} → (s : S α) → (pred : α → Bool) → S α
  ofList : {α : Type u} → List α → (S α) :=
    fun l => l.foldl (fun a s => insert a s) empty
  isEmpty : S α → Prop :=
    fun s => s = empty
  isSingleton : {α : Type u} → S α → Prop :=
    fun s => ∃ a, s = singleton a
  findUniqueMinimal {α : Type u} [Inhabited α] : (S α) → (r : α → α → Bool) → α
  findUniqueMaximal {α : Type u} [Inhabited α] : (S α) → (r : α → α → Bool) → α
  all : {α : Type u} → (S α) → (α → Bool) → Prop :=
    fun s p => ∀ a, mem s a → p a
  any : {α : Type u} → (S α) → (α → Bool) → Prop :=
    fun s p => ∃ a, mem s a ∧ p a
  filterMap : {α β : Type u} → (α → Option β) → (S α) → S β
  setIntRange : {α : Type u} → (a b : Int) → S α

  fromSeq : {α : Type u} → Seq α → S α

-- export VSetLikeF (symmDiff disjoint filter ofList)

namespace VSetLikeF

variable {S : Type u → Type v} [VSetLikeF S]

instance instEmptyCollection : EmptyCollection (S α) := ⟨empty⟩
instance instInhabited : Inhabited (S α) := ⟨∅⟩
instance instSingleton : Singleton α (S α) := ⟨singleton⟩
instance instMembership : Membership α (S α) := ⟨mem⟩
instance instInsert : Insert α (S α) := ⟨fun a s => insert s a⟩
instance instHasSubset : HasSubset (S α) := ⟨subset⟩
instance instLE : LE (S α) := ⟨subset⟩
instance instLT : LT (S α) := ⟨fun s₁ s₂ => s₁ ⊆ s₂ ∧ ¬(s₂ ⊆ s₁)⟩
instance instUnion : Union (S α) := ⟨union⟩
instance instInter : Inter (S α) := ⟨inter⟩
instance instSDiff : SDiff (S α) := ⟨sdiff⟩
instance instHAdd : HAdd (S α) (S α) (S α) := ⟨(· ∪ ·)⟩
instance instHSub : HSub (S α) (S α) (S α) := ⟨(· \ ·)⟩
instance instHMul : HMul (S α) (S α) (S α) := ⟨(· ∩ ·)⟩
instance instHAddSingleton : HAdd (S α) α (S α) := ⟨fun s a => insert s a⟩
instance instHSubSingleton : HSub (S α) α (S α) := ⟨fun s a => remove a s⟩
instance instCoeList : Coe (List α) (S α) := ⟨ofList⟩

end VSetLikeF

class VSetF (S : Type u → Type v)
  extends
    VSetLikeF S
  where
  /-- The cardinality of the set. -/
  card : S α → Nat
  /-- Dedup-ed list. Ordering not specified. -/
  toList : {α : Type u} → S α → List α
  fold {α : Type u} {β : Type u} (s : S α) (init : β) (f : β → α → β) : β

class VSetInfF (S : Type u → Type v)
  extends VSetLikeF S
  where
  /- The set of all elements. -/
  full : S α
  /- Creates a new set from the given predicate. -/
  new (p : α → Prop) : S α
  compl : S α → S α
  /-- The cardinality of the set. -/
  card : S α → Option Nat
  isFinite : S α → Bool :=
    fun s => card s ≠ none
  toList : {α : Type u} → (s : S α) → (h_finite : isFinite s) → List α
  fold {α : Type u} {β : Type u} (s : S α) (init : β) (f : β → α → β) : (h_finite : isFinite s) → β
  isFull : S α → Prop := fun s => s = full

open VSetLikeF in
class LawfulVSetLikeF (S : Type u → Type v) [VSetLikeF S]
  extends
    LawfulFunctor S
  where
  protected ext (s₁ s₂ : S α) : (∀ (x : α), x ∈ s₁ ↔ x ∈ s₂) → s₁ = s₂
  not_mem_empty : ∀ (a : α), a ∉ (∅ : S α)
  mem_insert_iff {a b : α} {s : S α} : b ∈ (s + a) ↔ b = a ∨ b ∈ s
  mem_remove_iff {a b : α} {s : S α} : b ∈ (s - a) ↔ b ≠ a ∧ b ∈ s
  mem_singleton_iff {a b : α} : b ∈ ({a} : S α) ↔ b = a
  -- choose_mem {α : Type u} [Inhabited α] : ∀ (s : S α) (h : ∃ x, x ∈ s), choose s h ∈ s
  choose_mem {α : Type u} [Inhabited α] : ∀ (s : S α), (h : ∃ x, x ∈ s) → choose s ∈ s
  subset_iff {s₁ s₂ : S α} : s₁ ⊆ s₂ ↔ ∀ a, a ∈ s₁ → a ∈ s₂
  mem_union_iff  {a : α} {s₁ s₂ : S α} : a ∈ s₁ ∪ s₂ ↔ a ∈ s₁ ∨ a ∈ s₂
  mem_inter_iff  {a : α} {s₁ s₂ : S α} : a ∈ s₁ ∩ s₂ ↔ a ∈ s₁ ∧ a ∈ s₂
  mem_sdiff_iff  {a : α} {s₁ s₂ : S α} : a ∈ s₁ \ s₂ ↔ a ∈ s₁ ∧ a ∉ s₂
  mem_symmDiff_iff {a : α} {s₁ s₂ : S α} : a ∈ symmDiff s₁ s₂ ↔ (a ∈ s₁ \ s₂ ∨ a ∈ s₂ \ s₁)
  disjoint_iff {s₁ s₂ : S α} : disjoint s₁ s₂ ↔ ∀ a, a ∉ s₁ ∩ s₂
  mem_filter_iff {p : α → Bool} {s : S α} {a : α} : a ∈ filter s p ↔ a ∈ s ∧ p a
  mem_ofList_iff {a : α} {l : List α} : a ∈ (ofList l : S α) ↔ a ∈ l
  mem_map_iff {f : α → β} {s : S α} {b : β}
    : b ∈ f <$> s ↔ ∃ a, a ∈ s ∧ f a = b
  mem_filterMap_iff {α β : Type u} {f : α → Option β} {s : S α} {b : β}
    : b ∈ filterMap f s ↔ ∃ a, a ∈ s ∧ f a = some b

open LawfulVSetLikeF in
attribute [simp] not_mem_empty mem_singleton_iff mem_ofList_iff
attribute [ext] LawfulVSetLikeF.ext

open VSetLikeF VSetF in
class LawfulVSetF (S : Type u → Type v) [VSetF S]
  extends
    LawfulVSetLikeF S
  where
  card_empty : card (∅ : S α) = 0
  card_insert : ∀ (a : α) (s : S α) [Decidable (a ∈ s)],
      card (s + a) = if a ∈ s then card s else card s + 1
  mem_toList_iff {s : S α} : ∀ (a : α), a ∈ s ↔ a ∈ toList s
  fold_empty : ∀ {β : Type u} (f : β → α → β) (init : β), fold (∅ : S α) init f = init
  fold_mem : ∀ {β : Type u} (f : β → α → β) [FoldCommutative f] (init : β) {s : S α} (a : α),
      a ∈ s → fold s init f = fold (s - a) (f init a) f

open LawfulVSetF in
attribute [simp] card_empty fold_empty


end Vstd
