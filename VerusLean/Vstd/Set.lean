import Lean

namespace Vstd

def Set (α : Type u) := α → Prop

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

def insert (a : α) (S : Set α) : Set α :=
  fun x => x = a ∨ S x

instance instInsert : Insert α (Set α) := ⟨Set.insert⟩

def remove (a : α) (S : Set α) : Set α :=
  fun x => x ≠ a ∧ S x

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

def filter (p : α → Prop) (S : Set α) : Set α :=
  inter (p : Set α) S

-- A type is `finite'` if it is in bijective correspondence to some `Fin n`
-- def finite' (S : Set α) : Prop :=
--   ∃ (n : Nat) (f : Fin n → α), ∀ x, (x ∈ S ↔ ∃ i, f i = x)

def surj_on (f : α → β) (S : Set α) : Prop :=
  ∀ (a1 a2), S.contains a1 ∧ S.contains a2 ∧ a1 ≠ a2 → f a1 ≠ f a2

-- CZ: A direct translation of `finite` in Vstd
def finite (S : Set α) : Prop :=
  ∃ (f : α → Nat) (ub : Nat), (surj_on f S) ∧ (∀ a, a ∈ S → f a < ub)

-- CZ: Current definition of `finite'` does not guarantee that `f` is injective,
-- so this can be larger than the real cardinality
-- noncomputable def card' (S : Set α) (h_finite : finite' S) : Nat :=
--   Exists.choose h_finite
-- noncomputable def card (S : Set α) (h_finite : finite S) : Nat :=
--   Exists.choose (Exists.choose_spec h_finite)

-- CC: Think about whether this is the right definition
noncomputable def choose (S : Set α) (h : ∃ x, x ∈ S) : α :=
  h.choose

def disjoint (S₁ S₂ : Set α) : Prop :=
  ∀ ⦃x⦄, x ∈ S₁ → x ∈ S₂ → False
  -- CC: Alternatively, `S₁ ∩ S₂ = ∅`

open Classical

/- -- Only meaningful if a set is finite.
noncomputable def fold'' (f : α → β → β) (b : β) (S : Set α) [∀ x, Decidable (S x)] : β :=
  if h : ∃ xs : List α, (∀ x ∈ xs, S x) ∧ xs.Nodup then
    List.foldr f b h.choose
  else
    b -/

def commutative (f : β → α → β) : Prop :=
  ∀ a₁ a₂ b, f (f b a₂) a₁ = f (f b a₁) a₂

-- commutative f
noncomputable def fold (S : Set α) (f : β → α → β) (init : β)
  (h_finite : finite S) : β :=
  let f_to_nat : α → Nat := Exists.choose h_finite
  let ub := Exists.choose (Exists.choose_spec h_finite)
  let elemsList := (List.range ub).filterMap (fun i =>
    if h : ∃ a, a ∈ S ∧ f_to_nat a = i then
      some (Classical.choose h)
    else
      none)
  List.foldl f init elemsList

-- CZ: A version based on `finite'`
-- noncomputable def fold (S : Set α) (f : β → α → β) (init : β) (h_finite : finite' S) : β :=
--   let n := Exists.choose h_finite
--   let f_finite : Fin n → α := Exists.choose (Exists.choose_spec h_finite)
--   let elemsList := (List.finRange n).map f_finite
--   List.foldl f init elemsList

-- CZ: Cardinality based on `fold`, a direct translation of Vstd `len`
noncomputable def len (S : Set α) (h_finite : finite S) : Nat :=
  fold S (fun acc _ => acc + 1) 0 h_finite

def map (f : α → β) (S : Set α) : Set β :=
  fun y => ∃ x, S x ∧ f x = y

/-! # Lemmas -/
-- CZ: Some proofs are taken from `Mathlib.Data.Set.Basic`

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

-- Verus name: axiom_set_union
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

-- Verus name: axiom_set_difference
theorem mem_diff (S₁ S₂ : Set α) (x : α) :
    x ∈ S₁ \ S₂ ↔ x ∈ S₁ ∧ ¬ x ∈ S₂ :=
  Iff.rfl

/-! # finite -/

-- theorem finite_empty : finite' (∅ : Set α) :=
--   ⟨0, Fin.elim0,  -- The empty function from Fin 0 to α
--    λ _ =>
--      ⟨λ h => False.elim h,  -- Empty set has no elements
--       λ ⟨i, _⟩ => Fin.elim0 i⟩  -- Fin 0 is uninhabited
--   ⟩

-- Verus name: axiom_set_empty_finite
theorem finite_empty : finite (∅ : Set α) :=
  ⟨fun _ => 0, 0,
   ⟨λ _ _ h => False.elim h.1,
    λ _ h => False.elim h⟩
  ⟩

theorem finite_singleton (a : α) : finite (singleton a) :=
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
theorem finite_insert_of_finite (a : α) (S : Set α) (h : finite S) :
    finite (insert a S) :=
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
theorem finite_remove_of_finite (a : α) (S : Set α) (h : finite S) :
    finite (remove a S) := by
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

-- Verus name: axiom_set_union_finite
theorem finite_union (S₁ S₂ : Set α) (h₁ : finite S₁) (h₂ : finite S₂) :
    finite (S₁ ∪ S₂) := by
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

theorem finite_union_iff (S₁ S₂ : Set α) :
    finite (S₁ ∪ S₂) ↔ finite S₁ ∧ finite S₂ := by
  constructor
  · intro h
    rcases h with ⟨f, ub, h_inj, h_bound⟩
    constructor
    · -- finite S₁
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
    · -- finite S₂
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
    exact finite_union S₁ S₂ h₁ h₂

theorem finite_inter_left (S₁ S₂ : Set α) (h : finite S₁) :
    finite (S₁ ∩ S₂) := by
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

theorem finite_inter_right (S₁ S₂ : Set α) (h : finite S₂) :
    finite (S₁ ∩ S₂) := by
  have : S₁ ∩ S₂ = S₂ ∩ S₁ := by
    ext x
    simp [Membership.mem, Mem, Inter.inter, inter, and_comm]
  rw [this]
  exact finite_inter_left S₂ S₁ h

-- CC: Should be a simple lemma of the above two
-- Verus calls this axiom_set_difference_finite
theorem finite_inter_of_finite_of_finite (h₁ : finite S₁) (_ : finite S₂)
    : finite (S₁ ∩ S₂) :=
  finite_inter_left S₁ S₂ h₁

-- Verus name: axiom_set_difference_finite
theorem finite_diff (S₁ S₂ : Set α) (h₁ : finite S₁) : finite (S₁ \ S₂) := by
  sorry

theorem choose_mem (S : Set α) (h : ∃ x, x ∈ S) : S.choose h ∈ S :=
  Classical.choose_spec h

@[simp]
theorem map_empty (f : α → β) : map f ∅ = ∅ := by
  ext; simp [map, Membership.mem, Mem, instEmptyCollection, empty]

@[simp]
theorem map_singleton (f : α → β) (a : α) :
    map f (singleton a) = singleton (f a) := by
  ext; simp [map, Membership.mem, Mem, singleton]; apply eq_comm

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

theorem fold_insert (S : Set α) (a : α) (f : β → α → β) (init : β)
  (h_finite : finite S) (h : a ∉ S) (h_comm : commutative f) :
  fold (insert a S) f init (finite_insert_of_finite a S h_finite) = f (fold S f init h_finite) a := by
  sorry

theorem fold_empty (f : β → α → β) (init : β) :
  fold (∅ : Set α) f init finite_empty = init := by
  sorry

theorem set_empty (a : α) : a ∉ (∅ : Set α) := by simp [empty]

theorem set_insert_same (S : Set α) (a : α) : a ∈ insert a S := by
  simp [insert, Membership.mem, Mem]

theorem set_insert_different (S : Set α) (a₁ : α) (a₂ : α) (h : a₁ ≠ a₂) :
  a₁ ∈ (insert a₂ S) ↔ a₁ ∈ S := by simp [Membership.mem, Mem, insert, h]

theorem set_remove_same (S : Set α) (a : α) : a ∉ remove a S := by
  simp [remove]

theorem set_remove_insert (S : Set α) (a : α) (h : a ∈ S) :
  insert a (remove a S) = S := by
  ext x
  simp_all [Membership.mem, Mem, insert, remove]
  constructor
  . intro h'
    cases h' with
    | inl h₁ => simp [h₁, h]
    | inr h₂ => exact And.right h₂
  . intro h'
    cases Classical.em (x = a) with
    | inl heq => left; exact heq
    | inr hne => right; exact ⟨hne, h'⟩

abbrev set_remove_different (S : Set α) (a₁ : α) (a₂ : α) :=
  mem_of_ne_of_mem_remove S a₁ a₂

-- theorem set_union
-- theorem set_intersect
-- theorem set_difference
theorem set_complement (S : Set α) (a : α) : a ∈ compl S ↔ a ∉ S := by
  simp [compl, Membership.mem, Mem]

theorem set_ext_equal (S₁ S₂ : Set α) : S₁ = S₂ ↔ ∀ x, x ∈ S₁ ↔ x ∈ S₂ := by
  constructor
  . intro h; simp [h]
  . exact ext

-- CC: At the bottom of `set.rs` is a variety of theorems about how
--     cardinality commutes with ∪, ∩, insert, etc.
--     Try writing some theorem statements and proofs.

/-! # len -/

theorem set_empty_len : len (∅ : Set α) (h : finite ∅) = 0 := by
  simp [len, fold_empty]

theorem set_insert_len (S : Set α) (a : α) (h : finite S) :
  len (insert a S) (finite_insert_of_finite a S h) = len S h + if a ∈ S then 0 else 1 := by
  cases Classical.em (a ∈ S) with
  | inl h_inS =>
    have heq : S = insert a S := by ext x; simp_all [insert, Membership.mem, Mem]
    simp [h_inS, ← heq]
  | inr h_ninS =>
    simp [h_ninS, len]
    exact fold_insert S a (fun acc _ => acc + 1) 0 h h_ninS (by simp [commutative])

theorem set_remove_len (S : Set α) (a : α) (h : finite S) :
  len (remove a S) (finite_remove_of_finite a S h) = len S h - if a ∈ S then 1 else 0 := by
  cases Classical.em (a ∈ S) with
  | inl h_inS =>
    have heq : insert a (remove a S) = S := (set_remove_insert S a) h_inS
    have k := set_insert_len (remove a S) a (finite_remove_of_finite a S h)
    simp [heq] at k
    simp [h_inS, k]
  | inr h_ninS =>
    have heq : S = remove a S := by
      ext x; simp [remove, Membership.mem, Mem]; intro hx hxa; simp [hxa] at hx; contradiction
    simp [h_ninS, ← heq]

theorem set_contains_len (S : Set α) (a : α) (h : finite S) :
  a ∈ S → len S h ≠ 0 := by
  intro h_inS
  have heq : insert a (remove a S) = S := (set_remove_insert S a) h_inS
  have h' := finite_remove_of_finite a S h
  have h'' := finite_insert_of_finite a (remove a S) h'
  have k := set_insert_len (remove a S) a h'
  simp [heq] at k
  simp [k]

theorem nonempty_of_len_ne_zero (S : Set α) (h_finite : finite S) (h_len : len S h_finite ≠ 0) :
  ∃ x, x ∈ S := by
  unfold len at h_len
  -- unfold fold at h_len
  let f := Exists.choose h_finite
  let ub := Exists.choose (Exists.choose_spec h_finite)
  let ⟨h_inj, h_bound⟩ := Exists.choose_spec (Exists.choose_spec h_finite)
  sorry

-- A finite set `S` contains the element `S.choose()` if it has length greater than 0.
theorem set_choose_len (S : Set α) (h : finite S) (h_len : len S h ≠ 0) :
  choose S (nonempty_of_len_ne_zero S h h_len) ∈ S := by
  sorry

end Set

end Vstd
