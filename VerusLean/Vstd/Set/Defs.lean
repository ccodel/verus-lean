import VerusLean.Vstd.Seq
import Std.Data.HashMap

namespace Vstd

/--
  Verus finite Sets.

  This is a true shim layer: replace the underlying definitions,
  and prove that they obey the minimal set of theorems at the end of the file.
  Then all theorems in `Set.Basic.lean` should be proven.

  These `Set`s need to be `inductive`, or else other inductive types
  struggle to prove termination, e.g., with

  ```
  inductive MyType where
  | mk : (s : Set MyType) → MyType
  ```
-/

inductive Set (α : Type u) : Type u
  -- If swapping out implementations, refer to something else here
  | mk (s : List α) : Set α

namespace Set

variable {α : Type u} {β : Type v} {γ : Type w}

def empty : Set α :=
  mk []

instance instInhabited : Inhabited (Set α) where
  default := empty

instance instEmptyCollection : EmptyCollection (Set α) where
  emptyCollection := Set.empty

def singleton (a : α) : Set α :=
  mk [a]

instance instSingleton : Singleton α (Set α) where
  singleton := Set.singleton

def card (s : Set α) : Nat :=
  match s with
  | mk l => l.length

/-
  CC: In some sense, including these two functions are sufficient to define
      all other functions. Just convert the set into a List, and then
      use a List function. Maybe this is the right approach...
-/
def ofList (l : List α) : Set α :=
  mk l

-- CC: No guarantees on ordering, or the inclusion of duplicates.
def toList (s : Set α) : List α :=
  match s with
  | mk l => l

/-
  CC: There's a tension between making the return type of membership
      be `Bool` or `Prop`. I believe that Cedar prefers Bool, since
      Bool is computable/decidable, whereas Prop is not. This matters
      to them because they ultimately have to compute with their Set types.
      In our case, Set will mostly stand as a Prop.

      My compromise for now is to define this section with boolean operations.
      If this is defined, then pure membership is as well.
      Otherwise, this section can be omitted,
      and pure membership can be defined on its own instead.
-/

section BoolOps

variable [BEq α]

-- The order of the arguments is reversed from the `Membership` class
def bmem (s : Set α) (a : α) : Bool :=
  match s with
  | mk l => l.contains a

def bsubset (s₁ s₂ : Set α) : Bool :=
  match s₁, s₂ with
  | mk l₁, mk l₂ => l₁.all (l₂.contains ·)

/--
  Boolean equality between two sets.

  CC: Unfortunately, without a canonical sorting function, or even duplicate
  removal, the best we can do is test that both sets are subsets of each other.
  This isn't efficient, but we aren't going for efficiency here.
-/
def beq (s₁ s₂ : Set α) : Bool :=
  s₁.bsubset s₂ && s₂.bsubset s₁

end BoolOps /- section -/

def mem (s : Set α) (a : α) : Prop :=
  match s with
  | mk l => a ∈ l

instance instMembership {α : Type u} : Membership α (Set α) where
  mem := mem

instance instDecidableMembership [DecidableEq α] (a : α) (s : Set α) : Decidable (a ∈ s) := by
  match s with
  | mk l =>
    by_cases h : a ∈ l
    · apply isTrue h
    · apply isFalse h

def subset (s₁ s₂ : Set α) : Prop :=
  match s₁, s₂ with
  | mk l₁, mk l₂ => ∀ x ∈ l₁, x ∈ l₂

instance instHasSubset : HasSubset (Set α) where
  Subset := subset

instance instLE : LE (Set α) where
  le := subset

def disjoint (s₁ s₂ : Set α) : Prop :=
  match s₁, s₂ with
  | mk l₁, mk l₂ => ∀ x ∈ l₁, x ∉ l₂

-- CC: Because we don't have a canonical sorting function,
--     we can't define equality with "strict equality".
--     Instead, we define "extensional equality" (which is not the correct
--     term, but we are using it in the same way).
def ext_eq (s₁ s₂ : Set α) : Prop :=
  s₁ ⊆ s₂ ∧ s₂ ⊆ s₁

def choose (s : Set α) [Inhabited α] : α :=
  match s with
  | mk [] => default
  | mk (a :: _) => a

/- # functions that modify the sets -/

-- Blindly insert the element. Who cares about duplicates!
-- CC: Alternatively, implement a `binsert` that depends on `BEq α`.
--     The problem with this is that this requires you to implement `bunion`, `binter`, etc.
--     Essentially, the whole set of boolean-based operations, which may not be desirable.
def insert (s : Set α) (a : α) : Set α :=
  match s with
  | mk l => mk <| a :: l

/-
CC: Alternate implementation
def insert' [DecidableEq α] (s : Set α) (a : α) : Set α :=
  match s with
  | mk l => mk <| if a ∈ l then l else a :: l
-/

instance instInsert : Insert α (Set α) where
  insert := (fun a s => insert s a)

def remove [DecidableEq α] (s : Set α) (a : α) : Set α :=
  match s with
  | mk l => mk <| l.filter (fun x => x ≠ a)

def union (s₁ s₂ : Set α) : Set α :=
  match s₁, s₂ with
  | mk l₁, mk l₂ => mk <| l₁ ++ l₂

instance instUnion : Union (Set α) where
  union := union

def inter [DecidableEq α] (s₁ s₂ : Set α) : Set α :=
  match s₁, s₂ with
  | mk l₁, mk l₂ => mk <| l₁.filter (fun x => x ∈ l₂)

instance instInter [DecidableEq α] : Inter (Set α) where
  inter := inter

def sdiff [DecidableEq α] (s₁ s₂ : Set α) : Set α :=
  match s₁, s₂ with
  | mk l₁, mk l₂ => mk <| l₁.filter (fun x => x ∉ l₂)

instance instSDiff [DecidableEq α] : SDiff (Set α) where
  sdiff := sdiff

def symmDiff [DecidableEq α] (s₁ s₂ : Set α) : Set α :=
  (s₁ \ s₂) ∪ (s₂ \ s₁)

/-! # higher order functions -/

def map (f : α → β) : Set α → Set β :=
  fun | mk l => mk <| l.map f

def mapConst (b : β) : Set α → Set β :=
  fun | mk l => mk <| l.map (fun _ => b)

instance instFunctor : Functor Set where
  map := map
  mapConst := mapConst

def filter (s : Set α) (pred : α → Bool) : Set α :=
  match s with
  | mk l => mk <| l.filter pred

/-! # correctness theorems -/

/-
  In this section, keep the theorem names, attributes,
  and statements, but change the proofs to fit the above definitions.
-/

@[simp]
theorem not_mem_empty : ∀ (a : α), a ∉ (∅ : Set α) := by
  intro a h_contra; cases h_contra

-- Something is an element of the set if it is a member of the underlying data structure.
-- CC: A bit interface breaking...
theorem mem_iff {a : α} {s : Set α} : a ∈ s ↔ a ∈ (match s with | mk l => l) := by
  rfl

theorem subset_iff {s₁ s₂ : Set α} : s₁ ⊆ s₂ ↔ ∀ a, a ∈ s₁ → a ∈ s₂ := by
  rfl

theorem ext_eq_iff {s₁ s₂ : Set α} : ext_eq s₁ s₂ ↔ ∀ a, a ∈ s₁ ↔ a ∈ s₂ := by
  match s₁, s₂ with
  | mk l₁, mk l₂ =>
    simp [ext_eq, subset_iff, mem_iff]
    constructor
    · intro ⟨h₁, h₂⟩ a
      exact ⟨fun h => h₁ _ h, fun h => h₂ _ h⟩
    · intro h
      exact ⟨fun _ ha => (h _).mp ha, fun _ ha => (h _).mpr ha⟩

@[simp]
theorem toList_ofList (l : List α) : toList (ofList l) = l :=
  rfl

@[simp]
theorem ofList_toList (s : Set α) : ofList (toList s) = s :=
  rfl

theorem eq_empty_iff {s : Set α} : ext_eq s ∅ ↔ ∀ a, a ∉ s := by
  match s with
  | mk l => simp only [ext_eq, subset_iff, not_mem_empty, imp_false,
                        false_implies, implies_true, and_true]

@[simp]
theorem mem_singleton_iff {a b : α} : b ∈ ({a} : Set α) ↔ b = a := by
  simp [Singleton.singleton, singleton, mem_iff]

theorem mem_insert_iff {a b : α} {s : Set α} : b ∈ (s.insert a) ↔ b = a ∨ b ∈ s := by
  match s with
  | mk l => simp only [insert, mem_iff, List.mem_cons]

theorem mem_remove_iff [DecidableEq α] {a b : α} {s : Set α}
    : b ∈ (s.remove a) ↔ b ≠ a ∧ b ∈ s := by
  match s with
  | mk l =>
    simp only [remove, ne_eq, decide_not, mem_iff, List.mem_filter,
      Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
    exact And.comm

theorem choose_mem [Inhabited α] {s : Set α} : (∃ x, x ∈ s) → s.choose ∈ s := by
  intro h
  match s with
  | mk [] => simp only [mem_iff, List.not_mem_nil, exists_const] at h
  | mk (a :: _) => simp only [choose, mem_iff, List.mem_cons, true_or]

theorem mem_union_iff {a : α} {s₁ s₂ : Set α}
    : a ∈ (s₁ ∪ s₂) ↔ a ∈ s₁ ∨ a ∈ s₂ := by
  match s₁, s₂ with
  | mk l₁, mk l₂ => simp only [union, mem_iff, List.mem_append]

theorem mem_inter_iff [DecidableEq α] {a : α} {s₁ s₂ : Set α}
    : a ∈ (s₁ ∩ s₂) ↔ a ∈ s₁ ∧ a ∈ s₂ := by
  match s₁, s₂ with
  | mk l₁, mk l₂ => simp only [mem_iff, inter, List.mem_filter, decide_eq_true_eq]

theorem mem_sdiff_iff [DecidableEq α] {a : α} {s₁ s₂ : Set α}
    : a ∈ (s₁ \ s₂) ↔ a ∈ s₁ ∧ a ∉ s₂ := by
  match s₁, s₂ with
  | mk l₁, mk l₂ =>
    simp only [mem_iff, sdiff, decide_not, List.mem_filter,
      Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]

theorem mem_symmDiff_iff [DecidableEq α] {a : α} {s₁ s₂ : Set α}
    : a ∈ symmDiff s₁ s₂ ↔ (a ∈ s₁ \ s₂ ∨ a ∈ s₂ \ s₁) := by
  simp only [symmDiff, mem_union_iff]

theorem disjoint_iff [DecidableEq α] {s₁ s₂ : Set α} : disjoint s₁ s₂ ↔ ext_eq (s₁ ∩ s₂) ∅ := by
  match s₁, s₂ with
  | mk l₁, mk l₂ =>
    -- CC: Doesn't get to a stable simp normal form here, need to split to two lines
    simp only [disjoint, eq_empty_iff, mem_inter_iff, not_and]
    simp only [mem_iff]

theorem disjoint_iff_not_mem_inter [DecidableEq α] {s₁ s₂ : Set α}
    : disjoint s₁ s₂ ↔ ∀ a, a ∉ (s₁ ∩ s₂) := by
  rw [disjoint_iff, eq_empty_iff]

theorem mem_filter_iff {p : α → Bool} {s : Set α} {a : α}
    : a ∈ filter s p ↔ a ∈ s ∧ p a := by
  match s with
  | mk l => simp only [filter, mem_iff, List.mem_filter]

theorem mem_map_iff {α β : Type u} {f : α → β} {s : Set α} {b : β}
    : b ∈ f <$> s ↔ ∃ a, a ∈ s ∧ f a = b := by
  match s with
  | mk l => simp only [map, mem_iff, List.mem_map, exists_prop]

theorem map_const {α β : Type u}
    : (Functor.mapConst : β → Set α → Set β) = Functor.map ∘ Function.const α := by
  ext b s
  match s with
  | mk l => rfl

@[simp]
theorem id_map {α : Type u} (s : Set α) : id <$> s = s := by
  match s with
  | mk l => simp only [Functor.map, map, List.map_id_fun, id_eq]

@[simp]
theorem comp_map {α β γ : Type u} (g : α → β) (h : β → γ) (s : Set α) :
    (h ∘ g) <$> s = h <$> g <$> s := by
  match s with
  | mk l => simp only [Functor.map, map, List.map_map]

instance instLawfulFunctor : LawfulFunctor Set where
  map_const := map_const
  id_map := id_map
  comp_map := comp_map

/-! # derived operations and lemmas -/

-- CC: The correctness of the above should imply the correctness of these?

def filterMap {α β : Type u} (f : α → Option β) (s : Set α) : Set β :=
  match s with
  | mk l => mk <| l.filterMap f

def any {α : Type u} (s : Set α) (p : α → Bool) : Prop :=
  ∃ a, a ∈ s ∧ p a

def all {α : Type u} (s : Set α) (p : α → Bool) : Prop :=
  ∀ a, a ∈ s → p a

#exit

  protected ext (s₁ s₂ : S α) : (∀ (x : α), x ∈ s₁ ↔ x ∈ s₂) → s₁ = s₂
  disjoint_iff {s₁ s₂ : S α} : disjoint s₁ s₂ ↔ ∀ a, a ∉ s₁ ∩ s₂
  mem_ofList_iff {a : α} {l : List α} : a ∈ (ofList l : S α) ↔ a ∈ l
  mem_map_iff {f : α → β} {s : S α} {b : β}
    : b ∈ f <$> s ↔ ∃ a, a ∈ s ∧ f a = b
  mem_filterMap_iff {α β : Type u} {f : α → Option β} {s : S α} {b : β}
    : b ∈ filterMap f s ↔ ∃ a, a ∈ s ∧ f a = some b


end Set /- namespace -/

#exit


/--
  Verus `Vstd` sets.
-/
-- TODO: consider the following approach to make it
-- so in the testfile, either a generic `S` or a specific `Set` can be used?
-- instead of {S: } [], write [S: ]
-- class VSetLikeF

class VSetLikeF (S : Type u → Type v) -- Type u → Type u
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

#exit

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
