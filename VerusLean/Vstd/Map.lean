import Lean
import VerusLean.Vstd.Set

namespace Vstd

/-
def Map (α : Type u) (β : Type v) :=
  List (α × β)

namespace Map

def empty (α : Type u) (β : Type v) : Map α β := []

def total (α : Type u) (β : Type v) (fv : α → β) : Map α β :=
  sorry

def new (α : Type u) (β : Type v) (fk : α → Bool) (fv : α → β) : Map α β :=
  List.filter (fun (x,_) => fk x) (total α β fv)

-- CZ: List.contains is inefficient
def dom (m : Map α β) [BEq α] : Set α :=
  fun x => List.contains (m.map fun (x,_) => x) x

def index (m : Map α β) (key : α) [BEq α] [Inhabited β] : β :=
  match List.find? (fun (x,_) => x == key) m with
  | none => default
  | some (_, v) => v

-- CZ: List.insert is inefficient, we don't want to have duplicates if we define
-- `len` as the number of elements in the list, but we can also define it via `dom`
def insert (m : Map α β) (key : α) (value : β) [BEq α] [BEq β] : Map α β :=
  List.insert (key, value) m

def remove (m : Map α β) (key : α) [BEq α] : Map α β :=
  List.filter (fun (x,_) => x != key) m

-- noncomputable def len (m : Map α β) [BEq α] (h : Set.finite m.dom) : Nat :=
--   Set.len (dom m) h
def len (m : Map α β) : Nat := m.length

theorem map_empty [BEq α] : dom (empty α β) = Set.empty := by
  unfold dom empty Set.empty; simp

theorem map_insert_domain [BEq α] [ReflBEq α] [BEq β] (m : Map α β) (key : α) (value : β) :
  dom (insert m key value) = Set.insert key (dom m) := by
  unfold dom insert Set.insert; simp
  apply funext; intro x; simp
  by_cases h : x = key
  . simp [h]
    unfold List.insert List.contains
    simp
    by_cases hh: List.contains m (key, value) = true
    . simp [hh]
      unfold Prod.fst
      apply
      sorry
    . simp [hh]
  . simp [h]
    sorry
-/


-- CZ: Verus' definition for Map

-- def Set (α : Type u) := α → Prop
def Map (α : Type u) (β : Type v) := α → Option β

namespace Map

def empty (α : Type u) (β : Type v) : Map α β := fun _ => none

-- Gives a `Map α β` whose domain contains every key, and maps each key
-- to the value given by `fv`.
def total (α : Type u) (β : Type v) (fv : α → β) : Map α β :=
  fun x => some (fv x)

-- Gives a `Map α β` whose domain is given by the boolean predicate on keys `fk`,
-- and maps each key to the value given by `fv`.
def new (α : Type u) (β : Type v) (fk : α → Bool) (fv : α → β) : Map α β :=
  fun x => if fk x then some (fv x) else none

open Classical
-- The domain of the map as a set.
def dom (m : Map α β) : Set α :=
  fun k => m k != none

-- Gets the value that the given key `key` maps to.
-- For keys not in the domain, the result is meaningless and arbitrary.
def index (m : Map α β) (key : α) [Inhabited β] : β :=
  match m key with
  | none => default
  | some v => v

noncomputable def insert (m : Map α β) (key : α) (value : β) : Map α β :=
  fun k => if k == key then some value else m k

noncomputable def remove (m : Map α β) (key : α) : Map α β :=
  fun k => if k == key then none else m k

noncomputable def len (m : Map α β) (h : Set.finite m.dom) : Nat :=
  Set.len (dom m) h

theorem map_empty : dom (empty α β) = Set.empty := by
  unfold dom empty Set.empty; simp

theorem map_insert_domain (m : Map α β) (key : α) (value : β) :
  dom (insert m key value) = Set.insert key (dom m) := by
  unfold dom insert Set.insert; simp
  apply funext; intro x; simp
  by_cases h : x = key <;> simp [h]

theorem map_insert_same (m : Map α β) (key : α) (value : β) :
  (insert m key value) key = value := by
  unfold insert; simp

theorem map_insert_different (m : Map α β) (key1 key2 : α) (value : β)
  (h : key1 ≠ key2) : (insert m key2 value) key1 = m key1 := by
  unfold insert; simp [h]

theorem map_remove_domain (m : Map α β) (key : α) :
  dom (remove m key) = Set.remove key (dom m) := by
  unfold dom remove Set.remove; simp

theorem map_remove_different (m : Map α β) (key1 key2 : α) (h : key1 ≠ key2) :
  (remove m key2) key1 = m key1 := by
  unfold remove; simp [h]

-- Two maps are equivalent if their domains are equivalent and every key in
-- their domains map to the same value.
theorem map_ext_equal (m1 m2 : Map α β) :
  m1 = m2 ↔ dom m1 == dom m2 && ∀ k, k ∈ dom m1 → m1 k == m2 k := by
  simp
  constructor
  . intro h; constructor
    . rw [h]
    . intro k hk; rw [h]
  . intro h
    unfold dom at h; simp at h
    rcases h with ⟨h1, h2⟩
    apply funext; intro k
    cases Classical.em (m1 k = none) with
    | inl h_none =>
      have h2_none : m2 k = none := by
        have := congrFun h1 k
        simp [h_none] at this
        exact this
      rw [h_none, h2_none]
    | inr h_some => exact h2 k h_some


/-! # map_lib.rs -/



end Map

end Vstd
