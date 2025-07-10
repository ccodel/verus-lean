import VerusLean.Vstd.Seq
import Std.Data.HashMap

namespace Vstd

/--
  Verus finite Sets.

  The definitions and theorems in this file are intended to be a shim layer:
  replace the definitions and theorems marked as SHIM, and the remaining
  theorems in this file and in `Basic.lean` should prove automatically.

  Note: whatever definition you use for `Set` needs to be `inductive`,
  or else other inductive types will struggle to prove termination.
  For example,
  ```
  inductive MyType where
  | mk : (s : Set MyType) → MyType
  ```

  List of SHIM functions:
    - `empty`
    - `singleton`
    - `card`
    - `ofList`
    - `toList`
    - `bmem`    (if you prefer a `Bool`-based view of Sets)
    - `bsubset` (if you prefer a `Bool`-based view of Sets)
    - `beq`     (if you prefer a `Bool`-based view of Sets)
    - `mem`     (pure membership, not `bmem`)
    - `choose`
    - `insert`, `remove`
    - `union`, `inter`, `sdiff`  (Set algebra)
    - `map`, `filter`, `fold`    (Higher-order functions)
-/

-- SHIM
inductive Set (α : Type u) : Type u
  -- If swapping out implementations, refer to something else here
  | mk (s : List α) : Set α

namespace Set

variable {α : Type u} {β : Type v} {γ : Type w}

-- SHIM
def empty : Set α :=
  mk []

instance instInhabited : Inhabited (Set α) where
  default := empty

instance instEmptyCollection : EmptyCollection (Set α) where
  emptyCollection := Set.empty

-- SHIM
def singleton (a : α) : Set α :=
  mk [a]

instance instSingleton : Singleton α (Set α) where
  singleton := Set.singleton

-- SHIM
-- This non-trivial implementation is due to the list maybe having duplicates
-- One way to make this simpler is to make the other definitions more complicated.
-- For example, instead of `union` being `List.append` under the hood,
-- do a `fold` across `insert`, which checks for duplicates
def card [DecidableEq α] (s : Set α) : Nat :=
  match s with
  | mk l =>
    match l with
    | [] => 0
    | (x :: xs) =>
      if x ∈ xs then card (mk xs)
      else card (mk xs) + 1

/-
  CC: In some sense, including these two functions are sufficient to define
      all other functions. Just convert the set into a List, and then
      use a List function. Maybe this is the right approach...
-/
-- SHIM
def ofList (l : List α) : Set α :=
  mk l

-- CC: No guarantees on ordering, or the inclusion of duplicates.
-- SHIM
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
-- SHIM
def bmem (s : Set α) (a : α) : Bool :=
  match s with
  | mk l => l.contains a

-- SHIM
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

/-

Uncomment this if `bmem` is the preferred definition.

def mem (s : Set α) (a : α) : Prop :=
  s.bmem a
-/

end BoolOps /- section -/

-- This is the non-`bmem`-based definition
-- SHIM
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
  ∀ x ∈ s₁, x ∈ s₂

instance instHasSubset : HasSubset (Set α) where
  Subset := subset

instance instLE : LE (Set α) where
  le := subset

def disjoint (s₁ s₂ : Set α) : Prop :=
  ∀ x ∈ s₁, x ∉ s₂

-- CC: Because we don't have a canonical sorting function,
--     we can't define equality with "strict equality".
--     Instead, we define "extensional equality" (which is not the correct
--     term, but we are using it in the same way).
def ext_eq (s₁ s₂ : Set α) : Prop :=
  s₁ ⊆ s₂ ∧ s₂ ⊆ s₁

-- SHIM (because the way we choose an element is dependent on the underlying data structure)
def choose (s : Set α) [Inhabited α] : α :=
  match s with
  | mk [] => default
  | mk (a :: _) => a

/- # functions that modify the sets -/

/-
  (Almost) all of these functions are marked as "SHIM"
  because their implementations depend on the underlying data structure.
-/

-- SHIM
-- Insert the element, only if it isn't a duplicate
-- CC: Alternatively, implement a `binsert` that depends on `BEq α`.
--     The problem with this is that this requires you to implement `bunion`, `binter`, etc.
--     Essentially, the whole set of boolean-based operations, which may not be desirable.
def insert [DecidableEq α] (s : Set α) (a : α) : Set α :=
  match s with
  | mk l => if a ∈ l then s else mk <| a :: l

/-
CC: Alternate implementation
def insert' [DecidableEq α] (s : Set α) (a : α) : Set α :=
  match s with
  | mk l => mk <| if a ∈ l then l else a :: l
-/

instance instInsert [DecidableEq α] : Insert α (Set α) where
  insert := (fun a s => insert s a)

-- SHIM
def remove [DecidableEq α] (s : Set α) (a : α) : Set α :=
  match s with
  | mk l => mk <| l.filter (fun x => x ≠ a)

-- SHIM
-- This keeps around duplicates, but is pretty efficient otherwise
def union (s₁ s₂ : Set α) : Set α :=
  match s₁, s₂ with
  | mk l₁, mk l₂ => mk <| l₁ ++ l₂

instance instUnion : Union (Set α) where
  union := union

-- SHIM
def inter [DecidableEq α] (s₁ s₂ : Set α) : Set α :=
  match s₁, s₂ with
  | mk l₁, mk l₂ => mk <| l₁.filter (fun x => x ∈ l₂)

instance instInter [DecidableEq α] : Inter (Set α) where
  inter := inter

-- SHIM
def sdiff [DecidableEq α] (s₁ s₂ : Set α) : Set α :=
  match s₁, s₂ with
  | mk l₁, mk l₂ => mk <| l₁.filter (fun x => x ∉ l₂)

instance instSDiff [DecidableEq α] : SDiff (Set α) where
  sdiff := sdiff

def symmDiff [DecidableEq α] (s₁ s₂ : Set α) : Set α :=
  (s₁ \ s₂) ∪ (s₂ \ s₁)

/-! # higher-order functions -/

-- SHIM
def map (f : α → β) : Set α → Set β :=
  fun | mk l => mk <| l.map f

-- Not SHIM, but can be replaced with a more efficient implementation
def mapConst (b : β) (s : Set α) : Set β :=
  s.map (fun _ => b)

instance instFunctor : Functor Set where
  map := map
  mapConst := mapConst

-- SHIM
def filter (s : Set α) (pred : α → Bool) : Set α :=
  match s with
  | mk l => mk <| l.filter pred

-- SHIM
-- Order and multiplicity of the elements to `f` are not guaranteed,
-- which means that for correctness, `f` needs to be commutative and idempotent-like.
def fold (s : Set α) (init : β) (f : β → α → β) : β :=
  match s with
  | mk l => l.foldl f init

/-! # correctness theorems -/

/-
  In this section, do not edit the theorem names, attributes, and statements,
  but do change the proofs to fit the above definitions.

  Core lemmas that will be affected by a change in the underlying data structure
  are marked SHIM, but depending on what lemmas are imported, some theorems
  might get proven automatically anyways.

  In this section, we prefer `simp` over `simp only` in SHIM lemmas
  to increase the odds that switching out the underlying data structure
  will lead to fewer broken proofs, in case other lemmas on the new
  underlying data structure are in scope.
-/

-- SHIM
@[simp]
theorem not_mem_empty : ∀ (a : α), a ∉ (∅ : Set α) := by
  intro a h_contra; cases h_contra

/--
  Something is an element of the set if it is a member of the underlying data structure.

  SHIM

  Explicitly breaks the API/interface to access the underlying data structure.

  This theorem requires the underlying data structure to support `Membership`,
  but this isn't too much of an ask. (Anything `List`-based will.)

  We use this lemma to derive other lemmas on membership in this file.
-/
theorem mem_iff {a : α} {s : Set α} : a ∈ s ↔ a ∈ (match s with | mk l => l) := by
  rfl

/-
  CC: If using a `bmem`-based definition, a similar set of starting lemmas are needed
      to convert to the `Prop`-based functions. But we should prefer the Prop-based
      functions, to be consistent.

      In fact, we probably will need a `bX_iff_X` for each kind of boolean function.

  SHIM
-/
theorem bmem_iff_mem [BEq α] [LawfulBEq α] {a : α} {s : Set α} : s.bmem a ↔ a ∈ s := by
  match s with
  | mk l => simp [bmem, mem_iff]

theorem subset_iff {s₁ s₂ : Set α} : s₁ ⊆ s₂ ↔ ∀ a, a ∈ s₁ → a ∈ s₂ := by
  rfl

-- SHIM
theorem ext_eq_iff {s₁ s₂ : Set α} : ext_eq s₁ s₂ ↔ ∀ a, a ∈ s₁ ↔ a ∈ s₂ := by
  match s₁, s₂ with
  | mk l₁, mk l₂ =>
    simp [ext_eq, subset_iff, mem_iff]
    constructor
    · intro ⟨h₁, h₂⟩ a
      exact ⟨fun h => h₁ _ h, fun h => h₂ _ h⟩
    · intro h
      exact ⟨fun _ ha => (h _).mp ha, fun _ ha => (h _).mpr ha⟩

-- SHIM
@[simp]
theorem mem_ofList_iff {a : α} {l : List α} : a ∈ (ofList l : Set α) ↔ a ∈ l := by
  simp [ofList, mem_iff]

-- SHIM
@[simp]
theorem mem_toList_iff {a : α} {s : Set α} : a ∈ toList s ↔ a ∈ s := by
  match s with
  | mk l => simp [toList, mem_iff]

theorem eq_empty_iff {s : Set α} : ext_eq s ∅ ↔ ∀ a, a ∉ s := by
  simp only [ext_eq_iff, not_mem_empty, iff_false]

-- SHIM
@[simp]
theorem mem_singleton_iff {a b : α} : b ∈ ({a} : Set α) ↔ b = a := by
  simp [Singleton.singleton, singleton, mem_iff]

-- SHIM
theorem mem_insert_iff [DecidableEq α] {a b : α} {s : Set α} : b ∈ (s.insert a) ↔ b = a ∨ b ∈ s := by
  match s with
  | mk l =>
    simp [insert, mem_iff]
    by_cases h : a ∈ l
    · simp [h]; rintro rfl; exact h
    · simp [h]

-- SHIM
theorem mem_remove_iff [DecidableEq α] {a b : α} {s : Set α}
    : b ∈ (s.remove a) ↔ b ≠ a ∧ b ∈ s := by
  match s with
  | mk l => simp [remove, mem_iff]; exact And.comm

-- SHIM
@[simp]
theorem card_empty [DecidableEq α] : card (∅ : Set α) = 0 := by
  simp [card, EmptyCollection.emptyCollection, empty]

-- SHIM
theorem card_insert [DecidableEq α] (a : α) (s : Set α) :
    card (s.insert a) = if a ∈ s then card s else card s + 1 := by
  match s with
  | mk l =>
    simp only [insert, mem_iff]
    by_cases h : a ∈ l
    · simp [h]
    · simp [h, card]

-- TODO: Can probably prove all other card_X theorems, but we might need more here

-- SHIM
theorem choose_mem [Inhabited α] {s : Set α} : (∃ x, x ∈ s) → s.choose ∈ s := by
  intro h
  match s with
  | mk [] => simp [mem_iff, exists_const] at h
  | mk (a :: _) => simp [choose, mem_iff]

-- SHIM
theorem mem_union_iff {a : α} {s₁ s₂ : Set α}
    : a ∈ (s₁ ∪ s₂) ↔ a ∈ s₁ ∨ a ∈ s₂ := by
  match s₁, s₂ with
  | mk l₁, mk l₂ => simp [union, mem_iff]

-- SHIM
theorem mem_inter_iff [DecidableEq α] {a : α} {s₁ s₂ : Set α}
    : a ∈ (s₁ ∩ s₂) ↔ a ∈ s₁ ∧ a ∈ s₂ := by
  match s₁, s₂ with
  | mk l₁, mk l₂ => simp [mem_iff, inter]

-- SHIM
theorem mem_sdiff_iff [DecidableEq α] {a : α} {s₁ s₂ : Set α}
    : a ∈ (s₁ \ s₂) ↔ a ∈ s₁ ∧ a ∉ s₂ := by
  match s₁, s₂ with
  | mk l₁, mk l₂ => simp [mem_iff, sdiff]

theorem mem_symmDiff_iff [DecidableEq α] {a : α} {s₁ s₂ : Set α}
    : a ∈ symmDiff s₁ s₂ ↔ (a ∈ s₁ \ s₂ ∨ a ∈ s₂ \ s₁) := by
  simp only [symmDiff, mem_union_iff]

theorem disjoint_iff [DecidableEq α] {s₁ s₂ : Set α} : disjoint s₁ s₂ ↔ ext_eq (s₁ ∩ s₂) ∅ := by
  simp only [disjoint, eq_empty_iff, mem_inter_iff, not_and]

theorem disjoint_iff_not_mem_inter [DecidableEq α] {s₁ s₂ : Set α}
    : disjoint s₁ s₂ ↔ ∀ a, a ∉ (s₁ ∩ s₂) := by
  rw [disjoint_iff, eq_empty_iff]

-- SHIM
theorem mem_filter_iff {p : α → Bool} {s : Set α} {a : α}
    : a ∈ filter s p ↔ a ∈ s ∧ p a := by
  match s with
  | mk l => simp [filter, mem_iff]

-- SHIM
theorem mem_map_iff {α β : Type u} {f : α → β} {s : Set α} {b : β}
    : b ∈ f <$> s ↔ ∃ a, a ∈ s ∧ f a = b := by
  match s with
  | mk l => simp [map, mem_iff]

-- SHIM?
theorem map_const {α β : Type u}
    : (Functor.mapConst : β → Set α → Set β) = Functor.map ∘ Function.const α := by
  ext b s
  rfl

-- SHIM
@[simp]
theorem id_map {α : Type u} (s : Set α) : id <$> s = s := by
  match s with
  | mk l => simp [Functor.map, map, id_eq]

-- SHIM
@[simp]
theorem comp_map {α β γ : Type u} (g : α → β) (h : β → γ) (s : Set α) :
    (h ∘ g) <$> s = h <$> g <$> s := by
  match s with
  | mk l => simp only [Functor.map, map, List.map_map]

instance instLawfulFunctor : LawfulFunctor Set where
  map_const := map_const
  id_map := id_map
  comp_map := comp_map

/-! # fold -/

-- SHIM
@[simp]
theorem fold_empty (f : β → α → β) (init : β) :
    fold (∅ : Set α) init f = init := by
  simp [fold, empty]

/-
  For correctness, we require that `f` is commutative and idempotent-like.
-/

class SetFold (f : β → α → β) where
  comm : ∀ (a₁ a₂ : α) (b : β), f (f b a₁) a₂ = f (f b a₂) a₁
  idempotent : ∀ (a : α) (b : β), f (f b a) a = f b a

/-
  CC: TODO. There's a whole bunch of lemmas you could write here.
      This is an exercise to CZ! Perhaps see what Verus does?

      I'll suggest a few lemmas, but this might not be the best course of action.

      Before you start proving things, convince yourself for why `SetFold`
      is a necessary well-behavedness assumption to have around.
      (Perhaps compare and contrast to `FoldCommutative` in `Seq.Defs.lean`)
-/

-- SHIM
@[simp]
theorem fold_insert [DecidableEq α] (s : Set α) (a : α) (f : β → α → β) [SetFold f] (init : β)
    : fold (insert s a) init f = f (fold s init f) a := by
  match s with
  | mk l =>
    simp [insert, fold]
    induction l generalizing init with
    | nil => simp [insert, fold]
    | cons x xs ih =>
      stop
      by_cases h_ax : a = x
      · subst h_ax
        simp [SetFold.comm a _, ih (f init a)]
        done

theorem fold_eq_of_ext_eq {s₁ s₂ : Set α} (f : β → α → β) [SetFold f] (init : β)
    : ext_eq s₁ s₂ → fold s₁ init f = fold s₂ init f := by
  sorry

/-! # derived operations and lemmas -/

-- CC: The correctness of the above should imply the correctness of these?

-- SHIM?
def filterMap (f : α → Option β) (s : Set α) : Set β :=
  match s with
  | mk l => mk <| l.filterMap f

-- TODO: Define `bany` and `ball`?

def any {α : Type u} (s : Set α) (p : α → Bool) : Prop :=
  ∃ a, a ∈ s ∧ p a

def all {α : Type u} (s : Set α) (p : α → Bool) : Prop :=
  ∀ a, a ∈ s → p a

-- SHIM
theorem mem_filterMap_iff {f : α → Option β} {s : Set α} {b : β}
    : b ∈ filterMap f s ↔ ∃ a, a ∈ s ∧ f a = some b := by
  match s with
  | mk l => simp [filterMap, mem_iff]

end Set /- namespace -/

end Vstd

#exit

-- TODO: I've kept anything below this #exit that hasn't been implemented completely above


class VSetLikeF (S : Type u → Type v) -- Type u → Type u
  extends
    Functor S
  where
  findUniqueMinimal {α : Type u} [Inhabited α] : (S α) → (r : α → α → Bool) → α
  findUniqueMaximal {α : Type u} [Inhabited α] : (S α) → (r : α → α → Bool) → α
  all : {α : Type u} → (S α) → (α → Bool) → Prop :=
    fun s p => ∀ a, mem s a → p a
  any : {α : Type u} → (S α) → (α → Bool) → Prop :=
    fun s p => ∃ a, mem s a ∧ p a
  setIntRange : {α : Type u} → (a b : Int) → S α

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

end Vstd
