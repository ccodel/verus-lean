import Lean

namespace Vstd

/--
  Verus `Vstd` sets.

  By default, we use the definition name from Verus.
  Separately, we show that the set is an instance of
  certain Lean type classes.

  We use a type class for the operations,
  and a separate type class for lawfulness,
  to allow for plug-and-play implementations.
-/
class VSetLike (S : Type u) (α : outParam $ Type v)
  extends
    EmptyCollection S,
    Singleton α S,
    Membership α S,
    Insert α S,
    HasSubset S,
    Union S,
    Inter S,
    SDiff S
  where
  ofList : List α → S :=
    fun l => l.foldl (fun a s => insert s a) (∅ : S)
  remove : α → S → S
  symmDiff : S → S → S :=
    fun s₁ s₂ => (s₁ \ s₂) ∪ (s₂ \ s₁)
  disjoint : S → S → Prop :=
    fun s₁ s₂ => ∀ a, a ∉ s₁ ∩ s₂
  filter (s : S) (pred : α → Bool) : S

class VSetF (S : Type u → Type v)
  extends Functor S  -- Gives `map` and `mapConst`

class VSet (S : Type u) (α : outParam $ Type v)
  extends VSetLike S α
  where
  /- The set of all elements. -/
  full : S
  /- Creates a new set from the given predicate. -/
  new (p : α → Bool) : S
  /- The cardinality of the set. -/
  card : S → Option Nat
  isFinite : S → Bool :=
    fun s => card s ≠ none
  compl : S → S

class FiniteVSet (S : Type u) (α : outParam $ Type v)
  extends VSetLike S α
  where
  card : S → Nat
  /-- Dedup-ed list. Ordering not specified. -/
  toList : S → List α
  fold (f : β → α → β) (init : β) : S → β


namespace VSetLike

variable [VSetLike S α]

-- instance instBEq [VSetLike S α] : BEq S := ⟨beq⟩
instance instInhabited : Inhabited (S) := ⟨∅⟩
instance instLE : LE S := ⟨(· ⊆ ·)⟩
instance instLT : LT S := ⟨fun s₁ s₂ => s₁ ⊆ s₂ ∧ ¬(s₂ ⊆ s₁)⟩
instance instHAddSingleton : HAdd S α S := ⟨fun s a => insert a s⟩
instance instHSubSingleton : HSub S α S := ⟨fun s a => remove a s⟩
instance instHAdd : HAdd S S S := ⟨(· ∪ ·)⟩
instance instHSub : HSub S S S := ⟨(· \ ·)⟩
instance instHMul : HMul S S S := ⟨(· ∩ ·)⟩

noncomputable def choose [VSetLike S α] {s : S} (h : ∃ x, x ∈ s) : α :=
  h.choose

end VSetLike


open VSetLike in
class LawfulVSetLike (S : Type u) (α : outParam $ Type v) [VSetLike S α] where
  protected ext (s₁ s₂ : S) : (∀ (x : α), x ∈ s₁ ↔ x ∈ s₂) → s₁ = s₂
  not_mem_empty : ∀ (a : α), a ∉ (∅ : S)
  mem_singleton_iff {a b : α} : b ∈ ({a} : S) ↔ b = a
  mem_ofList_iff {a : α} {l : List α} : a ∈ (ofList l : S) ↔ a ∈ l
  subset_iff {s₁ s₂ : S} : s₁ ⊆ s₂ ↔ ∀ a, a ∈ s₁ → a ∈ s₂
  mem_union_iff  {a : α} {s₁ s₂ : S} : a ∈ s₁ ∪ s₂ ↔ a ∈ s₁ ∨ a ∈ s₂
  mem_inter_iff  {a : α} {s₁ s₂ : S} : a ∈ s₁ ∩ s₂ ↔ a ∈ s₁ ∧ a ∈ s₂
  mem_sdiff_iff  {a : α} {s₁ s₂ : S} : a ∈ s₁ \ s₂ ↔ a ∈ s₁ ∧ a ∉ s₂
  mem_remove_iff {a b : α} {s : S} : b ∈ (s - a) ↔ b ≠ a ∧ b ∈ s
  mem_symmDiff_iff {a : α} {s₁ s₂ : S} : a ∈ symmDiff s₁ s₂ ↔ (a ∈ s₁ \ s₂ ∨ a ∈ s₂ \ s₁)
  mem_insert_iff {a b : α} {s : S} : b ∈ (s + a) ↔ b = a ∨ b ∈ s
  disjoint_iff {s₁ s₂ : S} : disjoint s₁ s₂ ↔ ∀ a, a ∉ s₁ ∩ s₂
  mem_filter_iff {p : α → Bool} {s : S} {a : α} : a ∈ filter s p ↔ a ∈ s ∧ p a

open LawfulVSetLike in
attribute [simp] not_mem_empty mem_singleton_iff
attribute [ext] LawfulVSetLike.ext

open VSetLike VSet in
class LawfulVSet (S : Type u) (α : outParam $ Type v) [VSet S α]
  extends LawfulVSetLike S α
  where
  mem_full (a : α) : a ∈ (full : S)
  mem_new (a : α) (p : α → Bool) : a ∈ (new p : S) ↔ p a
  mem_compl (s : S) (a : α) : a ∈ compl s ↔ a ∉ s
  -- full : S
  -- new (p : α → Bool) : S
  -- card : S → Nat
  -- isFinite : S → Bool := fun s => card s ≠ none
  -- compl : S → S

namespace VSetLike

open LawfulVSetLike

variable [VSetLike S α] [LawfulVSetLike S α]

omit [LawfulVSetLike S α] in
theorem mem_or_not_mem (a : α) (s : S) : a ∈ s ∨ a ∉ s := by
  by_cases h : a ∈ s
  · exact Or.inl h
  · exact Or.inr h

/-! # subset -/

theorem eq_of_subset_of_subset {s₁ s₂ : S} : s₁ ⊆ s₂ → s₂ ⊆ s₁ → s₁ = s₂ := by
  simp only [subset_iff]
  intro h₁ h₂
  ext x
  exact ⟨h₁ x, h₂ x⟩

theorem subset_trans {s₁ s₂ s₃ : S} : s₁ ⊆ s₂ → s₂ ⊆ s₃ → s₁ ⊆ s₃ := by
  simp only [subset_iff]
  intro h₁ h₂ x h
  exact h₂ _ (h₁ _ h)

theorem le_trans {s₁ s₂ s₃ : S} : s₁ ≤ s₂ → s₂ ≤ s₃ → s₁ ≤ s₃ :=
  subset_trans

/-! # union -/

@[symm]
theorem union_comm {s₁ s₂ : S} : s₁ ∪ s₂ = s₂ ∪ s₁ := by
  ext; simp only [mem_union_iff, or_comm]

theorem union_assoc {s₁ s₂ s₃ : S} : (s₁ ∪ s₂) ∪ s₃ = s₁ ∪ (s₂ ∪ s₃) := by
  ext; simp only [mem_union_iff, or_assoc]

@[simp]
theorem mem_empty_iff_false (a : α) : a ∈ (∅ : S) ↔ False :=
  Iff.intro
    (fun h => (not_mem_empty a) h)
    (fun h => False.elim h)

@[simp]
theorem union_empty (s : S) : s ∪ ∅ = s := by
  ext; simp only [mem_union_iff, not_mem_empty, or_false]

@[simp]
theorem empty_union (s : S) : ∅ ∪ s = s := by
  rw [union_comm]
  exact union_empty s

@[simp]
theorem union_self (s : S) : s ∪ s = s := by
  ext; simp only [mem_union_iff, or_self]

theorem union_of_subset {s₁ s₂ : S} : s₁ ⊆ s₂ → s₁ ∪ s₂ = s₂ := by
  intro h
  ext x
  simp only [mem_union_iff, or_iff_right_iff_imp]
  simp only [subset_iff] at h
  exact h x

/-! # inter -/

@[symm]
theorem inter_comm (s₁ s₂ : S) : s₁ ∩ s₂ = s₂ ∩ s₁ := by
  ext; simp only [mem_inter_iff, and_comm]

theorem inter_assoc (s₁ s₂ s₃ : S) : (s₁ ∩ s₂) ∩ s₃ = s₁ ∩ (s₂ ∩ s₃) := by
  ext; simp only [mem_inter_iff, and_assoc]

@[simp]
theorem inter_empty (s : S) : s ∩ ∅ = ∅ := by
  ext; simp only [mem_inter_iff, not_mem_empty, and_false]

@[simp]
theorem empty_inter (s : S) : ∅ ∩ s = ∅ := by
  rw [inter_comm]
  exact inter_empty s

@[simp]
theorem inter_self (s : S) : s ∩ s = s := by
  ext; simp only [mem_inter_iff, and_self]

@[simp]
theorem inter_subset_left (s₁ s₂ : S) : s₁ ∩ s₂ ⊆ s₁ := by
  simp only [subset_iff, mem_inter_iff, and_imp]
  intros
  assumption

@[simp]
theorem inter_subset_right (s₁ s₂ : S) : s₁ ∩ s₂ ⊆ s₂ := by
  rw [inter_comm]
  exact inter_subset_left s₂ s₁

@[simp]
theorem inter_union_left (s₁ s₂ : S) : s₁ ∩ (s₁ ∪ s₂) = s₁ := by
  ext; simp only [mem_inter_iff, mem_union_iff, and_iff_left_iff_imp]
  exact (Or.inl ·)

@[simp]
theorem inter_union_right (s₁ s₂ : S) : s₁ ∩ (s₂ ∪ s₁) = s₁ := by
  rw [union_comm]
  exact inter_union_left s₁ s₂

@[simp]
theorem union_inter_left (s₁ s₂ : S) : s₁ ∪ (s₁ ∩ s₂) = s₁ := by
  ext; simp only [mem_union_iff, mem_inter_iff, or_iff_left_iff_imp, and_imp]
  intros; assumption

@[simp]
theorem union_inter_right (s₁ s₂ : S) : s₁ ∪ (s₂ ∩ s₁) = s₁ := by
  rw [inter_comm]
  exact union_inter_left s₁ s₂

theorem union_inter_distrib (s₁ s₂ s₃ : S)
    : (s₁ ∪ s₂) ∩ s₃ = (s₁ ∩ s₃) ∪ (s₂ ∩ s₃) := by
  ext; simp only [mem_union_iff, mem_inter_iff, or_and_right]

theorem inter_union_distrib (s₁ s₂ s₃ : S)
    : (s₁ ∩ s₂) ∪ s₃ = (s₁ ∪ s₃) ∩ (s₂ ∪ s₃) := by
  ext; simp only [mem_union_iff, mem_inter_iff, and_or_right]

/-! # sdiff -/

@[simp]
theorem sdiff_subset (s₁ s₂ : S) : (s₁ \ s₂) ⊆ s₁ := by
  simp only [subset_iff, mem_sdiff_iff, and_imp]
  intros
  assumption

@[simp]
theorem sdiff_empty (s : S) : s \ ∅ = s := by
  ext; simp only [mem_sdiff_iff, not_mem_empty, not_false_eq_true, and_true]

@[simp]
theorem empty_sdiff (s : S) : ∅ \ s = ∅ := by
  ext; simp only [mem_sdiff_iff, not_mem_empty, false_and]

theorem sdiff_sdiff (s₁ s₂ s₃ : S) : (s₁ \ s₂) \ s₃ = s₁ \ (s₂ ∪ s₃) := by
  ext; simp only [mem_sdiff_iff, and_assoc, mem_union_iff, not_or]

theorem sdiff_sdiff_comm (s₁ s₂ s₃ : S) :
    (s₁ \ s₂) \ s₃ = (s₁ \ s₃) \ s₂ := by
  ext; simp only [mem_sdiff_iff, and_assoc, and_congr_right_iff]
  intro
  exact And.comm

@[simp]
theorem sdiff_union_left (s₁ s₂ : S) : (s₁ \ s₂) ∪ s₁ = s₁ := by
  ext; simp only [mem_union_iff, mem_sdiff_iff, or_iff_right_iff_imp, and_imp]
  intros
  assumption

@[simp]
theorem sdiff_union_right (s₁ s₂ : S) : (s₁ \ s₂) ∪ s₂ = s₁ ∪ s₂ := by
  ext x; simp only [mem_union_iff, mem_sdiff_iff]
  constructor
  · rintro (⟨h, _⟩ | h)
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h₁ | h₁)
    · by_cases h₂ : x ∈ s₂
      · exact Or.inr h₂
      · exact Or.inl ⟨h₁, h₂⟩
    · exact Or.inr h₁

/-! # insert -/

@[simp]
theorem insert_empty_eq (x : α) : (∅ : S) + x = {x} := by
  ext; simp only [mem_insert_iff, not_mem_empty, or_false, mem_singleton_iff]

instance instLawfulSingleton : LawfulSingleton α S where
  insert_empty_eq := insert_empty_eq

@[simp]
theorem mem_insert_self (a : α) (s : S) : a ∈ (s + a) := by
  simp only [mem_insert_iff, true_or]

theorem mem_insert_of_mem {b : α} {s : S} (h : b ∈ s) (a : α) : b ∈ (s + a) := by
  simp only [mem_insert_iff, h, or_true]

@[simp]
theorem insert_insert_self (a : α) (s : S) : (s + a) + a = s + a := by
  ext; simp only [mem_insert_iff, or_self_left]

@[simp]
theorem insert_remove_of_mem {a : α} {s : S} (h : a ∈ s)
    : (s - a) + a = s := by
  ext x
  simp only [mem_insert_iff, mem_remove_iff, ne_eq]
  constructor
  · rintro (rfl | ⟨_, h_mem⟩)
    <;> assumption
  · intro h_mem
    by_cases h_eq : x = a
    · exact Or.inl h_eq
    · exact Or.inr ⟨h_eq, h_mem⟩

theorem insert_insert_comm (a b : α) (s : S) : (s + a) + b = (s + b) + a := by
  ext x; simp only [mem_insert_iff]; rw [← or_assoc, @or_comm (x = b) (x = a), or_assoc]

theorem insert_union_comm (a : α) (s₁ s₂ : S) : (s₁ + a) ∪ s₂ = (s₁ ∪ s₂) + a := by
  ext x; simp only [mem_union_iff, mem_insert_iff, or_assoc]

theorem insert_eq_union_singleton (a : α) (s : S) : (s + a) = s ∪ {a} := by
  ext x; simp only [mem_insert_iff, mem_union_iff, mem_singleton_iff, or_comm]

/-! # remove -/

@[simp]
theorem remove_empty (a : α) : (∅ : S) - a = ∅ := by
  ext; simp only [mem_remove_iff, ne_eq, not_mem_empty, and_false]

@[simp]
theorem remove_singleton_self (a : α) : ({a} : S) - a = ∅ := by
  ext; simp only [mem_remove_iff, ne_eq, mem_singleton_iff, not_and_self, not_mem_empty]

@[simp]
theorem remove_singleton_eq_empty_iff (a b : α)
    : ({a} : S) - b = ∅ ↔ a = b := by
  constructor
  · intro h
    have h_iff := LawfulVSetLike.ext_iff.mp h
    simp only [mem_remove_iff, ne_eq, mem_singleton_iff,
        not_mem_empty, iff_false, not_and] at h_iff
    false_or_by_contra
    rename_i h_con
    have := h_iff a h_con
    contradiction
  · rintro rfl
    simp only [remove_singleton_self]

@[simp]
theorem not_mem_remove_self (a : α) (s : S) : a ∉ (s - a) := by
  simp only [mem_remove_iff, ne_eq, not_true_eq_false, false_and, not_false_eq_true]

theorem not_mem_remove_iff {a b : α} {s : S} : b ∉ (s - a) ↔ b = a ∨ b ∉ s := by
  simp only [mem_remove_iff, ne_eq, not_and]
  constructor
  · intro h_imp
    by_cases hba : b = a
    · exact Or.inl hba
    · exact Or.inr <| h_imp hba
  · rintro (rfl | h_mem)
    · simp only [not_true_eq_false, false_implies]
    · exact fun _ => h_mem

@[simp]
theorem remove_remove (a : α) (s : S) : (s - a) - a = s - a := by
  ext; simp only [mem_remove_iff, ne_eq, and_self_left]

theorem remove_eq_sdiff_singleton (a : α) (s : S) :
    s - a = s \ {a} := by
  ext x; simp only [mem_remove_iff, ne_eq, mem_sdiff_iff, mem_singleton_iff, and_comm]

/-! # disjoint -/

theorem disjoint_iff_inter_eq_empty {s₁ s₂ : S} :
    disjoint s₁ s₂ ↔ (s₁ ∩ s₂) = ∅ := by
  simp only [disjoint_iff, mem_inter_iff, not_and]
  constructor
  · intro h
    ext
    simp only [mem_inter_iff, not_mem_empty, iff_false, not_and]
    exact h _
  · intro h a h₁ h₂
    have := mem_inter_iff.mpr ⟨h₁, h₂⟩
    rw [h] at this
    exact absurd this (not_mem_empty _)

theorem disjoint_comm {s₁ s₂ : S} : disjoint s₁ s₂ ↔ disjoint s₂ s₁ := by
  simp only [disjoint_iff, inter_comm]

@[simp]
theorem disjoint_empty (s : S) : disjoint s ∅ := by
  rw [disjoint_iff_inter_eq_empty, inter_empty]

@[simp]
theorem empty_disjoint (s : S) : disjoint ∅ s := by
  rw [disjoint_iff_inter_eq_empty, empty_inter]

@[simp]
theorem disjoint_self_iff (s : S) : disjoint s s ↔ s = ∅ := by
  rw [disjoint_iff_inter_eq_empty, inter_self]

/-! # filter -/

@[simp]
theorem filter_subset (p : α → Bool) (s : S) :
    filter s p ⊆ s := by
  simp only [subset_iff, mem_filter_iff, and_imp]
  intros
  assumption

@[simp]
theorem filter_trivial_true (s : S) : filter s (fun _ => true) = s := by
  ext; simp only [mem_filter_iff, and_true]

@[simp]
theorem filter_trivial_false (s : S) : filter s (fun _ => false) = ∅ := by
  ext; simp only [mem_filter_iff, Bool.false_eq_true, and_false, not_mem_empty]

@[simp]
theorem filter_filter_self (p : α → Bool) (s : S) :
    filter (filter s p) p = filter s p := by
  ext; simp only [mem_filter_iff, and_self_right]

@[simp]
theorem filter_filter (p q : α → Bool) (s : S) :
    filter (filter s p) q = filter s (fun x => p x && q x) := by
  ext; simp only [mem_filter_iff, and_assoc, Bool.and_eq_true]

theorem filter_filter_comm (p q : α → Bool) (s : S) :
    filter (filter s p) q = filter (filter s q) p := by
  ext; simp only [filter_filter, mem_filter_iff, Bool.and_eq_true, and_comm]

theorem filter_subset_filter_of_subset {s₁ s₂ : S}
    : s₁ ⊆ s₂ → ∀ (p : α → Bool), filter s₁ p ⊆ filter s₂ p := by
  intro h p
  simp only [subset_iff, mem_filter_iff, and_imp]
  intro a h_mem hp
  exact ⟨(subset_iff.mp h) _ h_mem, hp⟩

theorem filter_subset_of_subset {s₁ s₂ : S}
    : s₁ ⊆ s₂ → ∀ (p : α → Bool), filter s₁ p ⊆ s₂ :=
  fun h p => subset_trans (filter_subset_filter_of_subset h p) (filter_subset _ _)

/-! # map -/

section map

instance instMapped [VSetF SF] [VSetLike (SF α) α] : VSetLike (SF β) β := by

  done

variable {SF : Type u → Type v} {α : Type u} [VSetF SF] [VSetLike (SF α) α] [LawfulVSetLike (SF α) α]


end map /- section -/

end VSetLike

namespace VSet

open LawfulVSetLike LawfulVSet

variable [VSet S α] [LawfulVSet S α]

@[simp]
theorem union_full (s : S) : s ∪ full = full := by
  ext; simp only [mem_union_iff, mem_full, or_true]

@[simp]
theorem full_union (s : S) : full ∪ s = full := by
  ext; simp only [mem_union_iff, mem_full, true_or]

@[simp]
theorem inter_full (s : S) : s ∩ full = s := by
  ext; simp only [mem_inter_iff, mem_full, and_true]

@[simp]
theorem full_inter (s : S) : full ∩ s = s := by
  ext; simp only [mem_inter_iff, mem_full, true_and]

end VSet

#exit


inductive YourSet (α : Type u) where
  | mk (elems : List α)

#check Fin
inductive MySet (α : Type u) where
  | finite (elems : List α)
  | inf (f : α → Bool)

def Set (α : Type u) :=
  α → Prop

inductive Foo (α : Type) where
  | bar
  | foo (f : MySet (Foo α))

#exit

namespace Set

/-- Membership in a set -/
-- protected def Mem (s : Set α) (a : α) : Prop :=
def Mem (s : Set α) (a : α) : Prop :=
  s a

-- CC: Let's have duplicate function names that agree with Vstd
-- CC: Later, I'll develop an attribute (similar to `@[simp]`) that
--     will automatically generate a new definition with the new name.
-- protected def contains (s : Set α) (a : α) : Prop :=
abbrev contains (s : Set α) (a : α) : Prop :=
  Set.Mem s a

instance instMembership : Membership α (Set α) :=
  ⟨Vstd.Set.Mem⟩

def empty {α : outParam (Type u)} : Set α :=
  (fun _ => False)

def full {α : outParam (Type u)} : Set α :=
  (fun _ => True)

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

-- def Set.SSubset (s₁ s₂ : Set α) :=
--   ∀ ⦃a⦄, a ∈ s₁ → a ∈ s₂ ∧ s₁ ≠ s₂
-- instance instLT : LT (Set α) := ⟨Set.SSubset⟩
-- instance instHasSSubset : HasSSubset (Set α) :=
--   ⟨(· < ·)⟩

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
abbrev intersect (S₁ S₂ : Set α) : Set α :=
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
-- CZ: can't find anything about `Surjective` in Batteries
-- A type is `Finite` if it is in bijective correspondence to some `Fin n`
def finite (S : Set α) : Prop :=
  ∃ (n : Nat) (f : Fin n → α), ∀ x, (x ∈ S ↔ ∃ i, f i = x)

def surj_on (f : α → β) (S : Set α) : Prop :=
  ∀ (a1 a2), S.contains a1 ∧ S.contains a2 ∧ a1 ≠ a2 → f a1 ≠ f a2

-- CZ: An alternate definition of `finite`, a direct translation of `finite` in Vstd
-- Note that this version has no bijection, so `ub` is not the cardinality
def finite' (S : Set α) : Prop :=
  ∃ (f : α → Nat) (ub : Nat), surj_on f S ∧ ∀ a, a ∈ S → f a < ub

noncomputable def card (S : Set α) (h_finite : finite S) : Nat :=
  -- CC: Have fun!
  -- There's probably some assumptions about the minimal `n` you need under `finite`
  Exists.choose h_finite

noncomputable def card' (S : Set α) (h_finite : finite' S) : Nat :=
  Exists.choose (Exists.choose_spec h_finite)

def disjoint (S₁ S₂ : Set α) : Prop :=
  ∀ ⦃x⦄, x ∈ S₁ → x ∈ S₂ → False
  -- CC: Alternatively, `S₁ ∩ S₂ = ∅`

-- CC: Think about whether this is the right definition
noncomputable def choose (S : Set α) (h : ∃ x, x ∈ S) : α :=
  h.choose

open Classical

-- CC: This is broken, due to possibly needing `DecidableEq α`.
--     Ponder this. Verus seems to really like fold.
--     But don't spend too much time here, since Verus seemed to take a long time to build it up
/- noncomputable def fold (S : Set α) (f : α → β → α) (init : β) : β :=
  if h : ∃ x, x ∈ S then
    let x := S.choose h
    fold (S.remove x) f (f x init)
  else
    init -/

-- Only meaningful if a set is finite.
noncomputable def fold (S : Set α) (f : β → α → β) (init : β) (h_finite : finite S) : β :=
  let n := Exists.choose h_finite
  let f_finite : Fin n → α := Exists.choose (Exists.choose_spec h_finite)
  let elemsList := (List.finRange n).map f_finite
  List.foldl f init elemsList

/- -- Only meaningful if a set is finite.
noncomputable def fold (f : α → β → β) (b : β) (S : Set α) [∀ x, Decidable (S x)] : β :=
  if h : ∃ xs : List α, (∀ x ∈ xs, S x) ∧ xs.Nodup then
    List.foldr f b h.choose
  else
    b -/

-- CZ: A version based on `finite'`
noncomputable def fold' (S : Set α) (f : β → α → β) (init : β) (h_finite : finite' S) : β :=
  let f_to_nat : α → Nat := Exists.choose h_finite
  let ub := Exists.choose (Exists.choose_spec h_finite)
  let elemsList := (List.range ub).filterMap (fun i =>
    if h : ∃ a, a ∈ S ∧ f_to_nat a = i then
      some (Classical.choose h)
    else
      none)
  List.foldl f init elemsList

-- CZ: Cardinality based on fold, a direct translation of Vstd `len`
noncomputable def len (S : Set α) (h_finite : finite S) : Nat :=
  fold S (fun acc _ => acc + 1) 0 h_finite

def map (f : α → β) (S : Set α) : Set β :=
  fun y => ∃ x, S x ∧ f x = y

/-! # Lemmas -/

-- CC: At this point, you can probably start copying basic theorem from Mathlib.Data.Set.Basic
-- CC: For example, the below proof works straight from Mathlib

/-! # mem -/

@[simp]
theorem not_mem_empty (x : α) : x ∉ (∅ : Set α) :=
  id

@[simp]
theorem mem_full (x : α) : x ∈ full :=
  trivial

@[simp]
theorem not_mem_remove (S : Set α) (x : α) :
    x ∉ S.remove x :=
  fun h => h.1 rfl

-- Verus calls this: axiom_set_remove_different
theorem mem_of_ne_of_mem_remove (S : Set α) (x y : α) (h : x ≠ y) :
    x ∈ S.remove y ↔ x ∈ S :=
  Iff.intro
    (fun h' => h'.2)
    (fun h' => ⟨h, h'⟩)

/-! # union -/

@[simp]
theorem empty_union (S : Set α) : ∅ ∪ S = S :=
  ext fun _ => iff_of_eq (false_or _)

@[simp]
theorem union_empty (S : Set α) : S ∪ ∅ = S :=
  ext fun _ => iff_of_eq (or_false _)

@[simp]
theorem full_union (S : Set α) : full ∪ S = full :=
  ext fun _ => iff_of_eq (true_or _)

@[simp]
theorem union_full (S : Set α) : S ∪ full = full :=
  ext fun _ => iff_of_eq (or_true _)

@[simp]
theorem union_self (S : Set α) : S ∪ S = S :=
  ext fun _ => iff_of_eq (or_self _)

theorem mem_union_iff {S₁ S₂ : Set α} {x : α} :
    x ∈ S₁ ∪ S₂ ↔ x ∈ S₁ ∨ x ∈ S₂ :=
  Iff.rfl

@[simp]
theorem union_compl (S : Set α) : S ∪ compl S = full := by
  ext x
  simp only [mem_full, iff_true]
  apply mem_union_iff.mpr
  exact Decidable.or_iff_not_imp_left.mpr id

theorem union_comm (S₁ S₂ : Set α) : S₁ ∪ S₂ = S₂ ∪ S₁ :=
  ext fun _ => or_comm

theorem union_assoc (S₁ S₂ S₃ : Set α) : (S₁ ∪ S₂) ∪ S₃ = S₁ ∪ (S₂ ∪ S₃) :=
  ext fun _ => or_assoc

/-! # inter -/

@[simp]
theorem empty_inter (S : Set α) : ∅ ∩ S = ∅ :=
  ext fun _ => iff_of_eq (false_and _)

@[simp]
theorem inter_empty (S : Set α) : S ∩ ∅ = ∅ :=
  ext fun _ => iff_of_eq (and_false _)

@[simp]
theorem full_inter (S : Set α) : full ∩ S = S :=
  ext fun _ => iff_of_eq (true_and _)

@[simp]
theorem inter_full (S : Set α) : S ∩ full = S :=
  ext fun _ => iff_of_eq (and_true _)

-- Verus name: axiom_set_intersect
theorem mem_inter_iff (S₁ S₂ : Set α) (x : α) :
    x ∈ S₁ ∩ S₂ ↔ x ∈ S₁ ∧ x ∈ S₂ :=
  Iff.rfl

theorem mem_diff (S₁ S₂ : Set α) (x : α) :
    x ∈ S₁ \ S₂ ↔ x ∈ S₁ ∧ ¬ x ∈ S₂ :=
  Iff.rfl

/-! # finite -/

-- CC: This proof will very much depend on your definition of `finite`,
--     so be happy with that definition first
theorem finite_empty : finite (∅ : Set α) :=
  ⟨0, Fin.elim0,  -- The empty function from Fin 0 to α
   λ _ =>
     ⟨λ h => False.elim h,  -- Empty set has no elements
      λ ⟨i, _⟩ => Fin.elim0 i⟩  -- Fin 0 is uninhabited
  ⟩

theorem finite_empty' : finite' (∅ : Set α) :=
  ⟨fun _ => 0, 0,
   ⟨λ _ _ h => False.elim h.1,
    λ _ h => False.elim h⟩
  ⟩

-- CZ: I start to prove things only for `finite'`, not sure if it's any easier

-- theorem finite_singleton (a : α) : finite (singleton a) :=
--   by sorry

theorem finite_singleton' (a : α) : finite' (singleton a) :=
  let f := fun x => if x = a then 0 else 1
  ⟨f, 1,
   ⟨λ a1 a2 h => by                 -- Injectivity proof
      simp [contains, Mem, singleton] at h
      have hn : a1 ≠ a2 := h.2.2
      simp [h.1, h.2.1] at hn,
    λ x h => by                     -- Bound proof
      by_cases he : x = a
      . rw [he]
        simp [f]
      . simp [Membership.mem, Mem, singleton] at h
        exact (he h).elim⟩
  ⟩

-- Verus calls this axiom_set_insert_finite
-- theorem finite_insert_of_finite (a : α) (S : Set α) (h : finite S) :
--     finite (insert a S) := by
--   sorry

theorem finite_insert_of_finite' (a : α) (S : Set α) (h : finite' S) :
    finite' (insert a S) :=
  match h with
  | ⟨f, ub, h_inj, h_bound⟩ =>
    let new_f : α → Nat := fun x => if x = a then ub else f x
    let new_ub := ub + 1
    ⟨new_f, new_ub,
     ⟨fun a1 a2 h => by -- Injectivity proof
        simp [contains, Mem, insert] at h
        let ⟨h1, h2, hne⟩ := h
        have h1' : a1 = a ∨ ¬ a1 = a := Classical.em (a1 = a)
        have h2' : a2 = a ∨ ¬ a2 = a := Classical.em (a2 = a)
        cases h1' with
        | inl ha1 => -- a1 = a
          cases h2 with
          | inl ha2 => -- a2 = a
            exact (hne (trans ha1 ha2.symm)).elim
          | inr ha2S => -- a2 ∈ S
            have ha2_mem : a2 ∈ S := ha2S
            have lhs : new_f a1 = ub := by simp [ha1, new_f]
            have a2_ne_a : a2 ≠ a := by rw [ha1] at hne; exact Ne.symm hne
            have rhs : new_f a2 = f a2 := by simp [a2_ne_a, if_neg, new_f]
            have rhs' : new_f a2 ≠ ub := by simp [rhs, ha2_mem, h_bound, Nat.lt_iff_le_and_ne.1]
            simp [lhs, rhs', Ne.symm]
        | inr ha1n => -- a1 ∈ S
          have h1S : S a1 := by simp [ha1n] at h1; exact h1
          have ha1_mem : a1 ∈ S := h1S
          cases h2' with
          | inl ha2 => -- a2 = a
            have rhs : new_f a2 = ub := by simp [ha2, new_f]
            have lhs : new_f a1 = f a1 := by simp [ha1n, if_neg, new_f]
            have lhs' : new_f a1 ≠ ub := by simp [lhs, ha1_mem, h_bound, Nat.lt_iff_le_and_ne.1]
            simp [lhs', rhs, Ne.symm]
          | inr ha2n => -- a2 ∈ S
            have ha2S : S a2 := by simp [ha2n] at h2; exact h2
            have lhs : new_f a1 = f a1 := by simp [ha1n, if_neg, new_f]
            have rhs : new_f a2 = f a2 := by simp [ha2n, if_neg, new_f]
            rw [lhs, rhs]
            apply h_inj
            simp [contains, Membership.mem, Mem]
            exact ⟨h1S, ha2S, hne⟩,

      fun x h => by -- Bounding proof
        simp [Membership.mem, Mem, insert] at h
        have h' : x = a ∨ ¬ x = a := Classical.em (x = a)
        cases h' with
        | inl hxa =>
          simp [new_f, hxa, new_ub]
        | inr hxan =>
          simp [new_f, hxan]
          have hxS : S x := by simp [hxan] at h; exact h
          apply Nat.lt_trans (h_bound x hxS) (Nat.lt_succ_self ub)⟩
    ⟩

-- Verus calls this axiom_set_remove_finite
-- theorem finite_remove_of_finite (a : α) (S : Set α) (h : finite S) :
--     finite (remove a S) := by
--   sorry

theorem finite_remove_of_finite' (a : α) (S : Set α) (h : finite' S) :
    finite' (remove a S) := by
  rcases h with ⟨f, ub, h_inj, h_bound⟩
  refine ⟨f, ub, ?inj, ?bound⟩
  case inj => -- Injectivity proof
    intro a1 a2 h
    simp only [remove, contains, Mem] at h
    exact h_inj a1 a2 ⟨h.1.2, h.2.1.2, h.2.2⟩
  case bound => -- Bounding proof
    intro x hx
    simp only [Membership.mem, remove, contains, Mem] at hx
    exact h_bound x hx.2

-- theorem finite_union (S₁ S₂ : Set α) (h₁ : finite S₁) (h₂ : finite S₂) :
--     finite (S₁ ∪ S₂) := by
--   sorry

theorem finite_union' (S₁ S₂ : Set α) (h₁ : finite' S₁) (h₂ : finite' S₂) :
    finite' (S₁ ∪ S₂) := by
  rcases h₁ with ⟨f₁, ub₁, h_inj₁, h_bound₁⟩
  rcases h₂ with ⟨f₂, ub₂, h_inj₂, h_bound₂⟩

  let new_f : α → Nat := fun x =>
    if S₁ x then f₁ x else ub₁ + f₂ x
  let new_ub := ub₁ + ub₂
  refine ⟨new_f, new_ub, ?inj, ?bound⟩

  -- Injectivity proof
  case inj =>
    intro a1 a2 h
    simp only [contains, Mem, union] at h
    rcases h with ⟨h1, h2, hne⟩
    have h1_cases : S₁ a1 ∨ ¬ S₁ a1 := Classical.em (S₁ a1)
    have h2_cases : S₁ a2 ∨ ¬ S₁ a2 := Classical.em (S₁ a2)
    cases h1_cases <;> cases h2_cases

    -- Case 1: Both in S₁
    case inl.inl h1_S₁ h2_S₁ =>
      simp [new_f, h1_S₁, h2_S₁]
      exact h_inj₁ a1 a2 ⟨h1_S₁, h2_S₁, hne⟩

    -- Case 2: a1 ∈ S₁, a2 ∉ S₁
    case inl.inr h1_S₁ h2_nS₁ =>
      have : f₁ a1 < ub₁ := h_bound₁ a1 h1_S₁
      have lhs : new_f a1 < ub₁ := by simp [this, h1_S₁, new_f]
      have rhs : ub₁ ≤ new_f a2 := by simp [h2_nS₁, new_f]
      simp [Nat.lt_iff_le_and_ne.1, Nat.lt_of_lt_of_le lhs rhs]

    -- Case 3: a1 ∉ S₁, a2 ∈ S₁
    case inr.inl h1_nS₁ h2_S₁ =>
      have : f₁ a2 < ub₁ := h_bound₁ a2 h2_S₁
      have lhs : new_f a2 < ub₁ := by simp [this, h2_S₁, new_f]
      have rhs : ub₁ ≤ new_f a1 := by simp [h1_nS₁, new_f]
      simp [Nat.lt_iff_le_and_ne.1, Nat.lt_of_lt_of_le lhs rhs, Ne.symm]

    -- Case 4: Both ∉ S₁ (must be in S₂)
    case inr.inr h1_nS₁ h2_nS₁ =>
      have h1_S₂ : S₂ a1 := h1.resolve_left h1_nS₁
      have h2_S₂ : S₂ a2 := h2.resolve_left h2_nS₁
      simp [new_f, h1_nS₁, h2_nS₁]
      exact h_inj₂ a1 a2 ⟨h1_S₂, h2_S₂, hne⟩

  -- Bounding proof
  case bound =>
    intro x hx
    simp [Membership.mem, Set.Mem, instUnion, union] at hx
    cases Classical.em (S₁ x) with
    | inl hx₁ =>
      simp [new_f, hx₁]
      exact Nat.lt_of_lt_of_le (h_bound₁ x hx₁) (Nat.le_add_right ub₁ ub₂)
    | inr hnx₁ =>
      have hx₂ : S₂ x := hx.resolve_left hnx₁
      simp [new_f, hnx₁, new_ub]
      exact h_bound₂ x hx₂

-- theorem finite_union_iff (S₁ S₂ : Set α) :
--     finite (S₁ ∪ S₂) ↔ finite S₁ ∧ finite S₂ := by
--   sorry

theorem finite_union_iff' (S₁ S₂ : Set α) :
    finite' (S₁ ∪ S₂) ↔ finite' S₁ ∧ finite' S₂ := by
  constructor
  · intro h
    rcases h with ⟨f, ub, h_inj, h_bound⟩
    constructor
    · -- finite' S₁
      refine ⟨f, ub, ?inj, ?bound⟩
      case inj =>
        intro a1 a2 h
        simp [contains, Mem] at h
        apply h_inj
        simp [instUnion, union, contains, Mem]
        simp [h]
      case bound =>
        intro x hx
        simp [Membership.mem, contains, Mem] at hx
        have hx' : (S₁ ∪ S₂) x := by simp [instUnion, union, contains, Mem, hx]
        apply h_bound x hx'
    · -- finite' S₂
      refine ⟨f, ub, ?inj, ?bound⟩
      case inj =>
        intro a1 a2 h
        simp [contains, Mem] at h
        apply h_inj
        simp [instUnion, union, contains, Mem]
        simp [h]
      case bound =>
        intro x hx
        simp [Membership.mem, contains, Mem] at hx
        have hx' : (S₁ ∪ S₂) x := by simp [instUnion, union, contains, Mem, hx]
        apply h_bound x hx'
  · -- Reverse direction (←)
    intro ⟨h₁, h₂⟩
    exact finite_union' S₁ S₂ h₁ h₂

-- theorem finite_inter_left (S₁ S₂ : Set α) (h : finite S₁) :
--     finite (S₁ ∩ S₂) := by
--   sorry

theorem finite_inter_left' (S₁ S₂ : Set α) (h : finite' S₁) :
    finite' (S₁ ∩ S₂) := by
  rcases h with ⟨f, ub, h_inj, h_bound⟩
  refine ⟨f, ub, ?inj, ?bound⟩

  -- Injectivity proof
  case inj =>
    intro a1 a2 h
    simp [contains, Mem] at h
    exact h_inj a1 a2 ⟨h.1.1, h.2.1.1, h.2.2⟩

  -- Bounding proof
  case bound =>
    intro x hx
    simp [Membership.mem, contains, Mem] at hx
    exact h_bound x hx.1

-- theorem finite_inter_right (S₁ S₂ : Set α) (h : finite S₂) :
--     finite (S₁ ∩ S₂) := by
--   sorry

theorem finite_inter_right' (S₁ S₂ : Set α) (h : finite' S₂) :
    finite' (S₁ ∩ S₂) := by
  have : S₁ ∩ S₂ = S₂ ∩ S₁ := by
    ext x
    simp [Membership.mem, Mem, Inter.inter, inter, and_comm]
  rw [this]
  exact finite_inter_left' S₂ S₁ h

-- CC: Should be a simple lemma of the above two
-- Verus calls this axiom_set_difference_finite
-- theorem finite_inter_of_finite_of_finite (S₁ S₂ : Set α)
--     (h₁ : finite S₁) (h₂ : finite S₂) :
--     finite (S₁ ∩ S₂) := by
--   sorry

theorem finite_inter_of_finite_of_finite' (h₁ : finite' S₁) (_ : finite' S₂)
    : finite' (S₁ ∩ S₂) :=
  finite_inter_left' S₁ S₂ h₁

theorem choose_mem (S : Set α) (h : ∃ x, x ∈ S) : S.choose h ∈ S :=
  Classical.choose_spec h

@[simp]
theorem map_empty (f : α → β) : map f ∅ = ∅ := by
  ext; simp [map, Membership.mem, Mem, instEmptyCollection, empty]

@[simp]
theorem map_singleton (f : α → β) (a : α) :
    map f (singleton a) = singleton (f a) := by
  ext; simp [map, Membership.mem, Mem, singleton]; apply eq_comm

-- CC: I'm not sure if some of these theorems are true.
--     They just intuitively make sense to me.
--     But if you find that a theorem doesn't go through, then I'm wrong!

@[simp]
theorem map_union (f : α → β) (S₁ S₂ : Set α) :
    map f (S₁ ∪ S₂) = map f S₁ ∪ map f S₂ := by
  ext y
  simp [map, union, Membership.mem, Mem, instUnion]
  constructor
  · intro ⟨x, hx, hfx⟩
    cases hx with
    | inl h₁ => left; exact ⟨x, h₁, hfx⟩
    | inr h₂ => right; exact ⟨x, h₂, hfx⟩
  · intro h
    rcases h with ⟨x, h₁, hfx⟩ | ⟨x, h₂, hfx⟩
    · exact ⟨x, Or.inl h₁, hfx⟩
    · exact ⟨x, Or.inr h₂, hfx⟩

@[simp]
theorem map_inter (f : α → β) (S₁ S₂ : Set α) :
    map f (S₁ ∩ S₂) ⊆ map f S₁ ∩ map f S₂ := by
  intro y hy
  simp [map, inter, Membership.mem, Mem]
  obtain ⟨x, ⟨h₁, h₂⟩, rfl⟩ := hy
  exact ⟨⟨x, h₁, rfl⟩, ⟨x, h₂, rfl⟩⟩

-- CC: At the bottom of `set.rs` is a variety of theorems about how
--     cardinality commutes with ∪, ∩, insert, etc.
--     Try writing some theorem statements and proofs.

-- theorem set_empty_len : card (∅ : Set α) (h : finite ∅) = 0 := by sorry

-- theorem set_empty_len' : len (∅ : Set α) (h : finite ∅) = 0 := by sorry


end Set

end Vstd
