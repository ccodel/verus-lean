import VerusLean.Vstd.Seq
import Std.Data.HashMap

namespace Vstd

/--
  Verus `Vstd` sets.
-/
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
  fold {α : Type u} {β : Type u} (f : β → α → β) (init : β) : S α → β

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
  fold {α : Type u} {β : Type u} (f : β → α → β) (init : β) : (s : S α) → (h_finite : isFinite s) → β
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
  fold_empty : ∀ {β : Type u} (f : β → α → β) (init : β), fold f init (∅ : S α) = init
  fold_mem : ∀ {β : Type u} (f : β → α → β) [FoldCommutative f] (init : β) {s : S α} (a : α),
      a ∈ s → fold f init s = fold f (f init a) (s - a)

open LawfulVSetF in
attribute [simp] card_empty fold_empty

open Std in
def SetVstdTranslationNames : HashMap Lean.Name Lean.Name := HashMap.ofList <|
  List.map (f := fun ⟨x, y⟩ => (String.toName s!"Vstd.Set.{x}", String.toName y)) <| [
  /- from current set.rs -/
  -- Verus has no entry for `singleton`
  ("empty", "VSetLikeF.empty"), -- or do we translate them to VSetF, by default assuming finite sets?
  ("new", "VSetInfF.new"),
  ("full", "VSetInfF.full"), -- might be an infinite set
  ("contains", "VSetLikeF.mem"),
  ("spec_has", "VSetLikeF.mem"),
  ("subset_of", "VSetLikeF.subset"),
  ("spec_le", "VSetLikeF.subset"),
  ("insert", "VSetLikeF.insert"),
  ("remove", "VSetLikeF.remove"),
  ("union", "VSetLikeF.union"),
  ("spec_add", "VSetLikeF.union"),
  ("intersect", "VSetLikeF.inter"),
  ("spec_mul", "VSetLikeF.inter"),
  ("difference", "VSetLikeF.sdiff"),
  ("spec_sub", "VSetLikeF.sdiff"),
  ("complement", "VSetInfF.compl"), -- might become an infinite set when taking complement
  ("filter", "VSetLikeF.filter"),
  ("finite", "VSetInfF.isFinite"), -- should be a property of the generic VSetLikeF instead
  ("len", "VSetF.card"), -- assuming finiteness
  -- CZ: the signature now matches, if we don't require a hypothesis that the set is inhabited
  ("choose", "VSetLikeF.choose"), -- The signatures for choose don't match
  ("mk_map", ""), -- ignored for now as Lean doesn't support build cycle, see Map/Defs.lean
  ("disjoint", "VSetLikeF.disjoint"),
]

open Std in
def SetLibVstdTranslationNames : HashMap Lean.Name Lean.Name := HashMap.ofList <|
  List.map (f := fun ⟨x, y⟩ => (String.toName s!"Vstd.Set_lib.{x}", String.toName y)) <| [
  /- from current set_lib.rs -/
  ("is_full", "VSetInfF.isFull"),
  ("is_empty", "VSetLikeF.isEmpty"),
  ("map", "VSetLikeF.map'"),
  ("to_seq", ""),
  ("to_sorted_seq", ""),
  ("is_singleton", "VSetLikeF.isSingleton"),
  ("find_unique_minimal", "VSetLikeF.findUniqueMinimal"),
  ("find_unique_maximal", "VSetLikeF.findUniqueMaximal"),
  ("to_multiset", ""), -- ignored for now
  ("all", "VSetLikeF.all"),
  ("any", "VSetLikeF.any"),
  ("filter_map", "VSetLikeF.filterMap"),
  ("flatten", ""), -- ignored for now, as its type is different
  ("set_int_range", "VSetLikeF.setIntRange"), -- if a set contains ints in [a,b), its size is bounded by b-a
]

end Vstd
