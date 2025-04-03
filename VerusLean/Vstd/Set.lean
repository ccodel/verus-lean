
namespace Vstd

def Set (α : Type u) := α → Prop

namespace Set

/-- Membership in a set -/
protected def Mem (s : Set α) (a : α) : Prop :=
  s a

-- CC: Let's have duplicate function names that agree with Vstd
-- CC: Later, I'll develop an attribute (similar to `@[simp]`) that
--     will automatically generate a new definition with the new name.
protected def contains (s : Set α) (a : α) : Prop :=
  Set.Mem s a

instance instMembership : Membership α (Set α) :=
  ⟨Vstd.Set.Mem⟩

def empty {α : outParam (Type u)} : Set α :=
  (fun _ => False)

instance instEmptyCollection : EmptyCollection (Set α) where
  emptyCollection := empty

instance instInhabited : Inhabited (Set α) where
  default := empty

@[ext]
theorem ext {a b : Set α} (h : ∀ (x : α), x ∈ a ↔ x ∈ b) : a = b :=
  funext (fun x ↦ propext (h x))

/-- The subset relation on sets. `s ⊆ t` means that all elements of `s` are elements of `t`.

Note that you should **not** use this definition directly, but instead write `s ⊆ t`. -/
protected def Subset (s₁ s₂ : Set α) :=
  ∀ ⦃a⦄, a ∈ s₁ → a ∈ s₂

/-- We introduce `≤` before `⊆` to help the unifier when applying lattice theorems
to subset hypotheses. -/
instance instLE : LE (Set α) :=
  ⟨Set.Subset⟩

instance instHasSubset : HasSubset (Set α) :=
  ⟨(· ≤ ·)⟩


/-! # Common set operations -/

def singleton (a : α) : Set α :=
  fun x => x = a

instance instSingleton : Singleton α (Set α) := ⟨Set.singleton⟩

def union (S₁ S₂ : Set α) : Set α :=
  fun x => S₁ x ∨ S₂ x

instance instUnion : Union (Set α) := ⟨Set.union⟩

def inter (S₁ S₂ : Set α) : Set α :=
  fun x => S₁ x ∧ S₂ x

instance instInter : Inter (Set α) := ⟨Set.inter⟩

-- CC: Verus' name
def intersect (S₁ S₂ : Set α) : Set α :=
  inter S₁ S₂

def difference (S₁ S₂ : Set α) : Set α :=
  fun x => S₁ x ∧ ¬ S₂ x

instance instSDiff : SDiff (Set α) := ⟨Set.difference⟩

def compl (S : Set α) : Set α :=
  fun x => ¬ S x

def symmDifference (S₁ S₂ : Set α) : Set α :=
  fun x => (S₁ x ∧ ¬ S₂ x) ∨ (¬ S₁ x ∧ S₂ x)

def insert (a : α) (S : Set α) : Set α :=
  fun x => x = a ∨ S x

instance instInsert : Insert α (Set α) := ⟨Set.insert⟩

def remove (a : α) (S : Set α) : Set α :=
  fun x => x ≠ a ∧ S x

def filter (p : α → Prop) (S : Set α) : Set α :=
  inter (p : Set α) S

-- CC: Maybe phrase in terms of Surjectivity in Batteries?
def finite (S : Set α) : Prop :=
  ∃ (n : Nat) (f : Fin n → α), ∀ x, x ∈ S ↔ ∃ i, f i = x

def card (S : Set α) (h_finite : finite S) : Nat :=
  -- CC: Have fun!
  -- There's probably some assumptions about the minimial `n` you need under `finite`
  sorry

def disjoint (S₁ S₂ : Set α) : Prop :=
  ∀ ⦃x⦄, x ∈ S₁ → x ∈ S₂ → False
  -- CC: Alternatively, `S₁ ∩ S₂ = ∅`

-- CC: Think about whether this is the right definition
noncomputable def choose (S : Set α) (h : ∃ x, x ∈ S) : α :=
  h.choose

-- CC: This is broken, due to possibly needing `DecidableEq α`.
--     Ponder this. Verus seems to really like fold.
--     But don't spend too much time here, since Verus seemed to take a long time to build it up
noncomputable def fold (S : Set α) (f : α → β → α) (init : β) : β :=
  if h : ∃ x, x ∈ S then
    let x := S.choose h
    fold (S.remove x) f (f x init)
  else
    init

def map (f : α → β) (S : Set α) : Set β :=
  fun y => ∃ x, S x ∧ f x = y

/-! # Lemmas -/

-- CC: At this point, you can probably start copying basic theorem from Mathlib.Data.Set.Basic
-- CC: For example, the below proof works straight from Mathlib
@[simp]
theorem empty_union (S : Set α) : ∅ ∪ S = S :=
  ext fun _ => iff_of_eq (false_or _)

@[simp]
theorem union_empty (S : Set α) : S ∪ ∅ = S := by sorry

theorem union_comm (S₁ S₂ : Set α) : S₁ ∪ S₂ = S₂ ∪ S₁ := by sorry

theorem union_assoc (S₁ S₂ S₃ : Set α) : (S₁ ∪ S₂) ∪ S₃ = S₁ ∪ (S₂ ∪ S₃)  := by sorry

@[simp]
theorem empty_inter (S : Set α) : ∅ ∩ S = ∅ := by sorry

@[simp]
theorem inter_empty (S : Set α) : S ∩ ∅ = ∅ := by sorry

theorem mem_union (S₁ S₂ : Set α) (x : α) :
    x ∈ S₁ ∪ S₂ ↔ x ∈ S₁ ∨ x ∈ S₂ := by
  sorry

theorem mem_inter (S₁ S₂ : Set α) (x : α) :
    x ∈ S₁ ∩ S₂ ↔ x ∈ S₁ ∧ x ∈ S₂ := by
  sorry

theorem mem_diff (S₁ S₂ : Set α) (x : α) :
    x ∈ S₁ \ S₂ ↔ x ∈ S₁ ∧ ¬ x ∈ S₂ := by
  sorry

@[simp]
theorem not_mem_empty (x : α) : x ∉ (∅ : Set α) := by
  sorry

@[simp]
theorem not_mem_remove (S : Set α) (x : α) :
    x ∉ S.remove x := by
  sorry

-- Verus calls this: axiom_set_remove_different
theorem mem_of_ne_of_mem_remove (S : Set α) (x y : α) (h : x ≠ y) :
    x ∈ S.remove y ↔ x ∈ S := by
  sorry

-- CC: This proof will very much depend on your definition of `finite`,
--     so be happy with that definition first
theorem finite_empty : finite (∅ : Set α) := by
  sorry

theorem finite_singleton (a : α) : finite (singleton a) := by
  sorry

-- Verus calls this axiom_set_insert_finite
theorem finite_insert_of_finite (a : α) (S : Set α) (h : finite S) :
    finite (insert a S) := by
  sorry

-- Verus calls this axiom_set_remove_finite
theorem finite_remove_of_finite (a : α) (S : Set α) (h : finite S) :
    finite (remove a S) := by
  sorry

theorem finite_union (S₁ S₂ : Set α) (h₁ : finite S₁) (h₂ : finite S₂) :
    finite (S₁ ∪ S₂) := by
  sorry

theorem finite_union_iff (S₁ S₂ : Set α) :
    finite (S₁ ∪ S₂) ↔ finite S₁ ∧ finite S₂ := by
  sorry

theorem finite_inter_left (S₁ S₂ : Set α) (h : finite S₁) :
    finite (S₁ ∩ S₂) := by
  sorry

theorem finite_inter_right (S₁ S₂ : Set α) (h : finite S₂) :
    finite (S₁ ∩ S₂) := by
  sorry

-- CC: Should be a simple lemma of the above two
-- Verus calls this axiom_set_difference_finite
theorem finite_inter_of_finite_of_finite (S₁ S₂ : Set α)
    (h₁ : finite S₁) (h₂ : finite S₂) :
    finite (S₁ ∩ S₂) := by
  sorry

-- CC: The proof of this might be sketchy. See mathlib
theorem choose_mem (S : Set α) (h : ∃ x, x ∈ S) :
    S.choose h ∈ S := by
  sorry

@[simp]
theorem map_empty (f : α → β) : map f ∅ = ∅ := by
  sorry

@[simp]
theorem map_singleton (f : α → β) (a : α) :
    map f (singleton a) = singleton (f a) := by
  sorry

-- CC: I'm not sure if some of these theorems are true.
--     They just intuitively make sense to me.
--     But if you find that a theorem doesn't go through, then I'm wrong!

@[simp]
theorem map_union (f : α → β) (S₁ S₂ : Set α) :
    map f (S₁ ∪ S₂) = map f S₁ ∪ map f S₂ := by
  sorry

@[simp]
theorem map_inter (f : α → β) (S₁ S₂ : Set α) :
    map f (S₁ ∩ S₂) = map f S₁ ∩ map f S₂ := by
  sorry

-- CC: At the bottom of `set.rs` is a variety of theorems about how
--     cardinality commutes with ∪, ∩, insert, etc.
--     Try writing some theorem statements and proofs.

end Set

end Vstd
