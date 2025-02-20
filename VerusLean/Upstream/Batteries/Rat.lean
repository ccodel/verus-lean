/-

LICENSE.

-/

import Batteries.Data.Rat.Lemmas
import VerusLean.Upstream.Batteries.Int
import VerusLean.Upstream.Batteries.Nat

namespace NNRat

instance instCoeRat : Coe ℚ≥0 ℚ := ⟨Subtype.val⟩

/-- The numerator of a nonnegative rational. -/
def num (q : ℚ≥0) : ℕ := (q : ℚ).num.natAbs

/-- The denominator of a nonnegative rational. -/
def den (q : ℚ≥0) : ℕ := (q : ℚ).den

theorem den_coe : (q : ℚ).den = q.den := rfl

end NNRat

namespace Rat

instance instInv : Inv ℚ := ⟨Rat.inv⟩

-- CC: To get around neeting Mathlib's `Logic.eq_or_ne` and `Classical`
protected theorem eq_or_ne (a b : ℚ) : a = b ∨ a ≠ b := by
  by_cases h : a = b
  · exact Or.inl h
  · exact Or.inr h

variable (a b c : ℚ)

theorem mk'_num_den (q : ℚ) : mk' q.num q.den q.den_nz q.reduced = q := rfl

@[simp]
protected theorem add_zero : a + 0 = a := by
  simp [add_def, normalize_eq_mkRat]
  exact mkRat_self _

@[simp]
protected theorem zero_add : 0 + a = a := by
  simp [add_def, normalize_eq_mkRat]
  exact mkRat_self _

protected theorem add_comm : a + b = b + a := by
  simp [add_def, Int.add_comm, Int.mul_comm, Nat.mul_comm]

-- TODO: Rename `Rat.divInt_self` to `Rat.num_divInt_den` in Batteries
theorem num_divInt_den (q : ℚ) : q.num /. q.den = q := divInt_self _

theorem mk'_eq_divInt {n d h c} : (⟨n, d, h, c⟩ : ℚ) = n /. d := (num_divInt_den _).symm
theorem mkRat_eq_divInt (n d) : mkRat n d = n /. d := rfl

theorem intCast_eq_divInt (z : ℤ) : (z : ℚ) = z /. 1 := mk'_eq_divInt

@[simp] theorem divInt_one (n : ℤ) : n /. 1 = n := by simp [divInt, mkRat, normalize]
@[simp] theorem mkRat_one (n : ℤ) : mkRat n 1 = n := by simp [mkRat_eq_divInt]
theorem divInt_one_one : 1 /. 1 = 1 := by rw [divInt_one, intCast_one]

@[simp]
theorem divInt_eq_zero {a b : ℤ} (b0 : b ≠ 0) : a /. b = 0 ↔ a = 0 := by
  rw [← zero_divInt b, divInt_eq_iff b0 b0, Int.zero_mul, Int.mul_eq_zero, or_iff_left b0]

theorem divInt_ne_zero {a b : ℤ} (b0 : b ≠ 0) : a /. b ≠ 0 ↔ a ≠ 0 :=
  not_congr (divInt_eq_zero b0)

@[simp]
protected theorem zero_ne_one : 0 ≠ (1 : ℚ) := by
  rw [ne_comm, ← divInt_one_one, divInt_ne_zero] <;> omega

/-- Define a (dependent) function or prove `∀ r : ℚ, p r` by dealing with rational
numbers of the form `n /. d` with `0 < d` and coprime `n`, `d`. -/
@[elab_as_elim]
def numDenCasesOn.{u} {C : ℚ → Sort u} :
    ∀ (a : ℚ) (_ : ∀ n d, 0 < d → (Int.natAbs n).Coprime d → C (n /. d)), C a
  | ⟨n, d, h, c⟩, H => by rw [mk'_eq_divInt]; exact H n d (Nat.pos_of_ne_zero h) c

/-- Define a (dependent) function or prove `∀ r : ℚ, p r` by dealing with rational
numbers of the form `n /. d` with `d ≠ 0`. -/
@[elab_as_elim]
def numDenCasesOn'.{u} {C : ℚ → Sort u} (a : ℚ) (H : ∀ (n : ℤ) (d : ℕ), d ≠ 0 → C (n /. d)) :
    C a :=
  numDenCasesOn a fun n d h _ => H n d (Nat.ne_of_lt h).symm

/-- Define a (dependent) function or prove `∀ r : ℚ, p r` by dealing with rational
numbers of the form `mk' n d` with `d ≠ 0`. -/
@[elab_as_elim]
def numDenCasesOn''.{u} {C : ℚ → Sort u} (a : ℚ)
    (H : ∀ (n : ℤ) (d : ℕ) (nz red), C (mk' n d nz red)) : C a :=
  numDenCasesOn a fun n d h h' ↦ by
    rw [← mk_eq_divInt _ _ (Nat.ne_of_lt h).symm h']
    exact H n d (Nat.ne_of_lt h).symm _

@[simp] theorem den_ne_zero (q : ℚ) : q.den ≠ 0 := (Nat.ne_of_lt q.den_pos).symm

protected theorem add_assoc : a + b + c = a + (b + c) :=
  numDenCasesOn' a fun n₁ d₁ h₁ ↦ numDenCasesOn' b fun n₂ d₂ h₂ ↦ numDenCasesOn' c fun n₃ d₃ h₃ ↦ by
    simp only [ne_eq, Int.natCast_eq_zero, h₁, not_false_eq_true, h₂, divInt_add_divInt,
      Int.mul_eq_zero, or_self, h₃]
    rw [Int.mul_assoc, Int.add_mul, Int.add_mul, Int.mul_assoc, Int.add_assoc]
    congr 2
    ac_rfl

protected theorem neg_add_cancel : -a + a = 0 := by
  simp [add_def, normalize_eq_mkRat, Int.neg_mul, Int.add_comm, ← Int.sub_eq_add_neg]

protected theorem mul_assoc : a * b * c = a * (b * c) :=
  numDenCasesOn' a fun n₁ d₁ h₁ =>
    numDenCasesOn' b fun n₂ d₂ h₂ =>
      numDenCasesOn' c fun n₃ d₃ h₃ => by
        simp only [divInt_ofNat, mkRat_mul_mkRat, Int.mul_comm, Int.mul_left_comm, Nat.mul_assoc]

protected theorem add_mul : (a + b) * c = a * c + b * c :=
  numDenCasesOn' a fun n₁ d₁ h₁ ↦ numDenCasesOn' b fun n₂ d₂ h₂ ↦ numDenCasesOn' c fun n₃ d₃ h₃ ↦ by
    simp only [ne_eq, Int.natCast_eq_zero, h₁, not_false_eq_true, h₂, divInt_add_divInt,
      Int.mul_eq_zero, or_self, h₃, divInt_mul_divInt]
    rw [← divInt_mul_right (Int.natCast_ne_zero.2 h₃), Int.add_mul, Int.add_mul]
    ac_rfl

protected theorem mul_add : a * (b + c) = a * b + a * c := by
  rw [Rat.mul_comm, Rat.add_mul, Rat.mul_comm, Rat.mul_comm c a]

instance instPowNat : Pow ℚ ℕ where
  pow q n := ⟨q.num ^ n, q.den ^ n, by simp [Nat.pow_eq_zero], by
    rw [Int.natAbs_pow]; exact q.reduced.pow _ _⟩

theorem pow_def (q : ℚ) (n : ℕ) :
    q ^ n = ⟨q.num ^ n, q.den ^ n,
      by simp [Nat.pow_eq_zero],
      by rw [Int.natAbs_pow]; exact q.reduced.pow _ _⟩ := rfl

@[simp] theorem num_pow (q : ℚ) (n : ℕ) : (q ^ n).num = q.num ^ n := rfl
@[simp] theorem den_pow (q : ℚ) (n : ℕ) : (q ^ n).den = q.den ^ n := rfl

@[simp] theorem mk'_pow (num : ℤ) (den : ℕ) (hd hdn) (n : ℕ) :
    mk' num den hd hdn ^ n = mk' (num ^ n) (den ^ n)
      (by simp [Nat.pow_eq_zero, hd]) (by rw [Int.natAbs_pow]; exact hdn.pow _ _) := rfl

theorem mk'_mul_mk' (n₁ n₂ : ℤ) (d₁ d₂ : ℕ) (hd₁ hd₂ hnd₁ hnd₂) (h₁₂ : n₁.natAbs.Coprime d₂)
    (h₂₁ : n₂.natAbs.Coprime d₁) :
    mk' n₁ d₁ hd₁ hnd₁ * mk' n₂ d₂ hd₂ hnd₂ = mk' (n₁ * n₂) (d₁ * d₂) (Nat.mul_ne_zero hd₁ hd₂) (by
      rw [Int.natAbs_mul]; exact (hnd₁.mul h₂₁).mul_right (h₁₂.mul hnd₂)) := by
  rw [mul_def]; dsimp; simp [mk_eq_normalize]

@[simp] theorem inv_divInt' (a b : ℤ) : (a /. b)⁻¹ = b /. a := inv_divInt ..

@[simp] theorem inv_mkRat (a : ℤ) (b : ℕ) : (mkRat a b)⁻¹ = b /. a := by
  rw [mkRat_eq_divInt, inv_divInt']

@[simp]
theorem divInt_mul_divInt' (n₁ d₁ n₂ d₂ : ℤ) : (n₁ /. d₁) * (n₂ /. d₂) = (n₁ * n₂) /. (d₁ * d₂) := by
  obtain rfl | h₁ := Int.eq_or_ne d₁ 0
  · simp
  obtain rfl | h₂ := Int.eq_or_ne d₂ 0
  · simp
  exact divInt_mul_divInt _ _ h₁ h₂

-- TODO: Rename `divInt_self` in Batteries to `num_divInt_den`
@[simp]
theorem divInt_self' {n : ℤ} (hn : n ≠ 0) : n /. n = 1 := by
  simpa using divInt_mul_right (n := 1) (d := 1) hn

protected theorem mul_inv_cancel : a ≠ 0 → a * a⁻¹ = 1 :=
  numDenCasesOn' a fun n d hd hn ↦ by
    simp only [divInt_ofNat, ne_eq, hd, not_false_eq_true, mkRat_eq_zero] at hn
    simp [-divInt_ofNat, mkRat_eq_divInt, Int.mul_comm, Int.mul_ne_zero hn (Int.ofNat_ne_zero.2 hd)]

protected theorem inv_mul_cancel (h : a ≠ 0) : a⁻¹ * a = 1 :=
  Eq.trans (Rat.mul_comm _ _) (Rat.mul_inv_cancel _ h)

--------------------------------------------------------------------------------

/-! ### The rational numbers are a group -/

instance instAddCommGroup : AddCommGroup ℚ where
  zero := 0
  add := (· + ·)
  neg := Neg.neg
  zero_add := Rat.zero_add
  add_zero := Rat.add_zero
  add_comm := Rat.add_comm
  add_assoc := Rat.add_assoc
  neg_add_cancel := Rat.neg_add_cancel
  sub_eq_add_neg := Rat.sub_eq_add_neg
  nsmul := nsmulRec
  zsmul := zsmulRec

instance instAddGroup : AddGroup ℚ := by infer_instance
instance instAddCommMonoid : AddCommMonoid ℚ := by infer_instance
instance instAddMonoid : AddMonoid ℚ := by infer_instance
instance instAddCommSemigroup : AddCommSemigroup ℚ := by infer_instance
instance instAddSemigroup : AddSemigroup ℚ := by infer_instance

instance instCommMonoid : CommMonoid ℚ where
  one := 1
  mul := (· * ·)
  mul_one := Rat.mul_one
  one_mul := Rat.one_mul
  mul_comm := Rat.mul_comm
  mul_assoc := Rat.mul_assoc
  npow n q := q ^ n
  npow_zero := by intros; apply Rat.ext <;> simp [Nat.pow_zero]
  npow_succ n q := by
    dsimp
    rw [← q.mk'_num_den, mk'_pow, mk'_mul_mk']
    · congr
    · rw [mk'_pow, Int.natAbs_pow]
      exact q.reduced.pow_left _
    · rw [mk'_pow]
      exact q.reduced.pow_right _

instance instMonoid : Monoid ℚ := by infer_instance
instance instCommSemigroup : CommSemigroup ℚ := by infer_instance
instance instSemigroup : Semigroup ℚ := by infer_instance

/-! # The rationals are a Ring -/

instance instCommRing : CommRing ℚ where
  mul_one := instCommMonoid.mul_one
  one_mul := instCommMonoid.one_mul
  mul_comm := instCommMonoid.mul_comm
  mul_assoc := instCommMonoid.mul_assoc
  neg_add_cancel := instAddCommGroup.neg_add_cancel
  sub_eq_add_neg := instAddCommGroup.sub_eq_add_neg
  zsmul := instAddCommGroup.zsmul
  zero_mul := Rat.zero_mul
  mul_zero := Rat.mul_zero
  left_distrib := Rat.mul_add
  right_distrib := Rat.add_mul
  intCast := fun n => n
  natCast n := Int.cast n
  natCast_zero := rfl
  natCast_succ n := by
    simp only [intCast_eq_divInt, divInt_add_divInt _ _ Int.one_ne_zero Int.one_ne_zero,
      ← divInt_one_one, Int.natCast_add, Int.natCast_one, instCommMonoid.mul_one]
    simp

instance instRing : Ring ℚ := by infer_instance

-- CC: We don't actually have this class, but steal its fields

/-! # Rationals also form a Field -/

instance instField : Field ℚ where
  inv := Rat.inv
  exists_pair_ne := ⟨0, 1, Rat.zero_ne_one⟩
  inv_zero := by
    change Rat.inv 0 = 0
    rw [Rat.inv_def]
    rfl
  mul_one := instCommRing.mul_one
  one_mul := instCommRing.one_mul
  mul_comm := instCommRing.mul_comm
  mul_assoc := instCommRing.mul_assoc
  neg_add_cancel := instCommRing.neg_add_cancel
  sub_eq_add_neg := instCommRing.sub_eq_add_neg
  zsmul := instCommRing.zsmul
  zsmul_zero' := _
  zsmul_succ' := _
  mul_inv_cancel := Rat.mul_inv_cancel
  zero_mul := instCommRing.zero_mul
  mul_zero := instCommRing.mul_zero
  left_distrib := instCommRing.left_distrib
  right_distrib := instCommRing.right_distrib
  natCast := instCommRing.natCast
  natCast_zero := instCommRing.natCast_zero
  natCast_succ := instCommRing.natCast_succ

end Rat

#exit

/-import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Int.Defs
import Mathlib.Data.Rat.Init
import Mathlib.Order.Basic
import Mathlib.Tactic.Common
import Batteries.Data.Rat.Lemmas -/

/-!
# Basics for the Rational Numbers

## Summary

We define the integral domain structure on `ℚ` and prove basic lemmas about it.
The definition of the field structure on `ℚ` will be done in `Mathlib.Data.Rat.Basic` once the
`Field` class has been defined.

## Main Definitions

- `Rat.divInt n d` constructs a rational number `q = n / d` from `n d : ℤ`.

## Notations

- `/.` is infix notation for `Rat.divInt`.

-/



open Function

namespace Rat
variable {q : ℚ}

theorem mk'_num_den (q : ℚ) : mk' q.num q.den q.den_nz q.reduced = q := rfl

@[simp]
theorem ofInt_eq_cast (n : ℤ) : ofInt n = Int.cast n :=
  rfl

-- TODO: Replace `Rat.ofNat_num`/`Rat.ofNat_den` in Batteries
@[simp] theorem num_ofNat (n : ℕ) : num (ofNat (n)) = ofNat(n) := rfl
@[simp] theorem den_ofNat (n : ℕ) : den ofNat(n) = 1 := rfl

@[simp, norm_cast] theorem num_natCast (n : ℕ) : num n = n := rfl

@[simp, norm_cast] theorem den_natCast (n : ℕ) : den n = 1 := rfl

-- TODO: Replace `intCast_num`/`intCast_den` the names in Batteries
@[simp, norm_cast] theorem num_intCast (n : ℤ) : (n : ℚ).num = n := rfl

@[simp, norm_cast] theorem den_intCast (n : ℤ) : (n : ℚ).den = 1 := rfl

/-theorem intCast_injective : Injective (Int.cast : ℤ → ℚ) := fun _ _ ↦ congr_arg num
theorem natCast_injective : Injective (Nat.cast : ℕ → ℚ) :=
  intCast_injective.comp fun _ _ ↦ Int.natCast_inj.1

-- We want to use these lemmas earlier than the lemmas simp can prove them with
@[simp, nolint simpNF, norm_cast] theorem natCast_inj {m n : ℕ} : (m : ℚ) = n ↔ m = n :=
  natCast_injective.eq_iff
@[simp, nolint simpNF, norm_cast] theorem intCast_eq_zero {n : ℤ} : (n : ℚ) = 0 ↔ n = 0 := intCast_inj
@[simp, nolint simpNF, norm_cast] theorem natCast_eq_zero {n : ℕ} : (n : ℚ) = 0 ↔ n = 0 := natCast_inj
@[simp, nolint simpNF, norm_cast] theorem intCast_eq_one {n : ℤ} : (n : ℚ) = 1 ↔ n = 1 := intCast_inj
@[simp, nolint simpNF, norm_cast] theorem natCast_eq_one {n : ℕ} : (n : ℚ) = 1 ↔ n = 1 := natCast_inj -/

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11215): TODO Should this be namespaced?

theorem mkRat_eq_divInt (n d) : mkRat n d = n /. d := rfl

@[simp] theorem mk'_zero (d) (h : d ≠ 0) (w) : mk' 0 d h w = 0 := by congr; simp_all

@[simp]
theorem num_eq_zero {q : ℚ} : q.num = 0 ↔ q = 0 := by
  induction q
  constructor
  · rintro rfl
    exact mk'_zero _ _ _
  · exact congrArg num

theorem num_ne_zero {q : ℚ} : q.num ≠ 0 ↔ q ≠ 0 := num_eq_zero.not

@[simp] theorem den_ne_zero (q : ℚ) : q.den ≠ 0 := q.den_pos.ne'

@[simp] theorem num_nonneg : 0 ≤ q.num ↔ 0 ≤ q := by
  simp [Int.le_iff_lt_or_eq, instLE, Rat.blt, Int.not_lt]; tauto

@[simp]
theorem divInt_eq_zero {a b : ℤ} (b0 : b ≠ 0) : a /. b = 0 ↔ a = 0 := by
  rw [← zero_divInt b, divInt_eq_iff b0 b0, Int.zero_mul, Int.mul_eq_zero, or_iff_left b0]

theorem divInt_ne_zero {a b : ℤ} (b0 : b ≠ 0) : a /. b ≠ 0 ↔ a ≠ 0 :=
  (divInt_eq_zero b0).not

-- Porting note: this can move to Batteries
theorem normalize_eq_mk' (n : Int) (d : Nat) (h : d ≠ 0) (c : Nat.gcd (Int.natAbs n) d = 1) :
    normalize n d h = mk' n d h c := (mk_eq_normalize ..).symm

-- TODO: Rename `mkRat_num_den` in Batteries
@[simp] alias mkRat_num_den' := mkRat_self

-- TODO: Rename `Rat.divInt_self` to `Rat.num_divInt_den` in Batteries
theorem num_divInt_den (q : ℚ) : q.num /. q.den = q := divInt_self _

theorem mk'_eq_divInt {n d h c} : (⟨n, d, h, c⟩ : ℚ) = n /. d := (num_divInt_den _).symm

theorem intCast_eq_divInt (z : ℤ) : (z : ℚ) = z /. 1 := mk'_eq_divInt

-- TODO: Rename `divInt_self` in Batteries to `num_divInt_den`
@[simp] theorem divInt_self' {n : ℤ} (hn : n ≠ 0) : n /. n = 1 := by
  simpa using divInt_mul_right (n := 1) (d := 1) hn

/-- Define a (dependent) function or prove `∀ r : ℚ, p r` by dealing with rational
numbers of the form `n /. d` with `0 < d` and coprime `n`, `d`. -/
@[elab_as_elim]
def numDenCasesOn.{u} {C : ℚ → Sort u} :
    ∀ (a : ℚ) (_ : ∀ n d, 0 < d → (Int.natAbs n).Coprime d → C (n /. d)), C a
  | ⟨n, d, h, c⟩, H => by rw [mk'_eq_divInt]; exact H n d (Nat.pos_of_ne_zero h) c

/-- Define a (dependent) function or prove `∀ r : ℚ, p r` by dealing with rational
numbers of the form `n /. d` with `d ≠ 0`. -/
@[elab_as_elim]
def numDenCasesOn'.{u} {C : ℚ → Sort u} (a : ℚ) (H : ∀ (n : ℤ) (d : ℕ), d ≠ 0 → C (n /. d)) :
    C a :=
  numDenCasesOn a fun n d h _ => H n d h.ne'

/-- Define a (dependent) function or prove `∀ r : ℚ, p r` by dealing with rational
numbers of the form `mk' n d` with `d ≠ 0`. -/
@[elab_as_elim]
def numDenCasesOn''.{u} {C : ℚ → Sort u} (a : ℚ)
    (H : ∀ (n : ℤ) (d : ℕ) (nz red), C (mk' n d nz red)) : C a :=
  numDenCasesOn a fun n d h h' ↦ by rw [← mk_eq_divInt _ _ h.ne' h']; exact H n d h.ne' _

-- Porting note: there's already an instance for `Add ℚ` is in Batteries.

theorem lift_binop_eq (f : ℚ → ℚ → ℚ) (f₁ : ℤ → ℤ → ℤ → ℤ → ℤ) (f₂ : ℤ → ℤ → ℤ → ℤ → ℤ)
    (fv :
      ∀ {n₁ d₁ h₁ c₁ n₂ d₂ h₂ c₂},
        f ⟨n₁, d₁, h₁, c₁⟩ ⟨n₂, d₂, h₂, c₂⟩ = f₁ n₁ d₁ n₂ d₂ /. f₂ n₁ d₁ n₂ d₂)
    (f0 : ∀ {n₁ d₁ n₂ d₂}, d₁ ≠ 0 → d₂ ≠ 0 → f₂ n₁ d₁ n₂ d₂ ≠ 0) (a b c d : ℤ)
    (b0 : b ≠ 0) (d0 : d ≠ 0)
    (H :
      ∀ {n₁ d₁ n₂ d₂}, a * d₁ = n₁ * b → c * d₂ = n₂ * d →
        f₁ n₁ d₁ n₂ d₂ * f₂ a b c d = f₁ a b c d * f₂ n₁ d₁ n₂ d₂) :
    f (a /. b) (c /. d) = f₁ a b c d /. f₂ a b c d := by
  generalize ha : a /. b = x; cases' x with n₁ d₁ h₁ c₁; rw [mk'_eq_divInt] at ha
  generalize hc : c /. d = x; cases' x with n₂ d₂ h₂ c₂; rw [mk'_eq_divInt] at hc
  rw [fv]
  have d₁0 := Int.ofNat_ne_zero.2 h₁
  have d₂0 := Int.ofNat_ne_zero.2 h₂
  exact (divInt_eq_iff (f0 d₁0 d₂0) (f0 b0 d0)).2
    (H ((divInt_eq_iff b0 d₁0).1 ha) ((divInt_eq_iff d0 d₂0).1 hc))

attribute [simp] divInt_add_divInt

attribute [simp] neg_divInt

theorem neg_def (q : ℚ) : -q = -q.num /. q.den := by rw [← neg_divInt, num_divInt_den]

@[simp] theorem divInt_neg (n d : ℤ) : n /. -d = -n /. d := divInt_neg' ..

attribute [simp] divInt_sub_divInt

@[simp]
theorem divInt_mul_divInt' (n₁ d₁ n₂ d₂ : ℤ) : (n₁ /. d₁) * (n₂ /. d₂) = (n₁ * n₂) /. (d₁ * d₂) := by
  obtain rfl | h₁ := eq_or_ne d₁ 0
  · simp
  obtain rfl | h₂ := eq_or_ne d₂ 0
  · simp
  exact divInt_mul_divInt _ _ h₁ h₂

attribute [simp] mkRat_mul_mkRat

theorem mk'_mul_mk' (n₁ n₂ : ℤ) (d₁ d₂ : ℕ) (hd₁ hd₂ hnd₁ hnd₂) (h₁₂ : n₁.natAbs.Coprime d₂)
    (h₂₁ : n₂.natAbs.Coprime d₁) :
    mk' n₁ d₁ hd₁ hnd₁ * mk' n₂ d₂ hd₂ hnd₂ = mk' (n₁ * n₂) (d₁ * d₂) (Nat.mul_ne_zero hd₁ hd₂) (by
      rw [Int.natAbs_mul]; exact (hnd₁.mul h₂₁).mul_right (h₁₂.mul hnd₂)) := by
  rw [mul_def]; dsimp; simp [mk_eq_normalize]

theorem mul_eq_mkRat (q r : ℚ) : q * r = mkRat (q.num * r.num) (q.den * r.den) := by
  rw [mul_def, normalize_eq_mkRat]

-- TODO: Rename `divInt_eq_iff` in Batteries to `divInt_eq_divInt`
alias divInt_eq_divInt := divInt_eq_iff

instance instPowNat : Pow ℚ ℕ where
  pow q n := ⟨q.num ^ n, q.den ^ n, by simp [Nat.pow_eq_zero], by
    rw [Int.natAbs_pow]; exact q.reduced.pow _ _⟩

theorem pow_def (q : ℚ) (n : ℕ) :
    q ^ n = ⟨q.num ^ n, q.den ^ n,
      by simp [Nat.pow_eq_zero],
      by rw [Int.natAbs_pow]; exact q.reduced.pow _ _⟩ := rfl

theorem pow_eq_mkRat (q : ℚ) (n : ℕ) : q ^ n = mkRat (q.num ^ n) (q.den ^ n) := by
  rw [pow_def, mk_eq_mkRat]

theorem pow_eq_divInt (q : ℚ) (n : ℕ) : q ^ n = q.num ^ n /. q.den ^ n := by
  rw [pow_def, mk_eq_divInt, Int.natCast_pow]

@[simp] theorem num_pow (q : ℚ) (n : ℕ) : (q ^ n).num = q.num ^ n := rfl
@[simp] theorem den_pow (q : ℚ) (n : ℕ) : (q ^ n).den = q.den ^ n := rfl

@[simp] theorem mk'_pow (num : ℤ) (den : ℕ) (hd hdn) (n : ℕ) :
    mk' num den hd hdn ^ n = mk' (num ^ n) (den ^ n)
      (by simp [Nat.pow_eq_zero, hd]) (by rw [Int.natAbs_pow]; exact hdn.pow _ _) := rfl

instance : Inv ℚ :=
  ⟨Rat.inv⟩

@[simp] theorem inv_divInt' (a b : ℤ) : (a /. b)⁻¹ = b /. a := inv_divInt ..

@[simp] theorem inv_mkRat (a : ℤ) (b : ℕ) : (mkRat a b)⁻¹ = b /. a := by
  rw [mkRat_eq_divInt, inv_divInt']

theorem inv_def' (q : ℚ) : q⁻¹ = q.den /. q.num := by rw [← inv_divInt', num_divInt_den]

@[simp] theorem divInt_div_divInt (n₁ d₁ n₂ d₂) :
    (n₁ /. d₁) / (n₂ /. d₂) = (n₁ * d₂) /. (d₁ * n₂) := by
  rw [div_def, inv_divInt, divInt_mul_divInt']

theorem div_def' (q r : ℚ) : q / r = (q.num * r.den) /. (q.den * r.num) := by
  rw [← divInt_div_divInt, num_divInt_den, num_divInt_den]

variable (a b c : ℚ)

protected theorem add_zero : a + 0 = a := by simp [add_def, normalize_eq_mkRat]

protected theorem zero_add : 0 + a = a := by simp [add_def, normalize_eq_mkRat]

protected theorem add_comm : a + b = b + a := by
  simp [add_def, Int.add_comm, Int.mul_comm, Nat.mul_comm]

protected theorem add_assoc : a + b + c = a + (b + c) :=
  numDenCasesOn' a fun n₁ d₁ h₁ ↦ numDenCasesOn' b fun n₂ d₂ h₂ ↦ numDenCasesOn' c fun n₃ d₃ h₃ ↦ by
    simp only [ne_eq, Int.natCast_eq_zero, h₁, not_false_eq_true, h₂, divInt_add_divInt,
      Int.mul_eq_zero, or_self, h₃]
    rw [Int.mul_assoc, Int.add_mul, Int.add_mul, Int.mul_assoc, Int.add_assoc]
    congr 2
    ac_rfl

protected theorem neg_add_cancel : -a + a = 0 := by
  simp [add_def, normalize_eq_mkRat, Int.neg_mul, Int.add_comm, ← Int.sub_eq_add_neg]

@[simp] theorem divInt_one (n : ℤ) : n /. 1 = n := by simp [divInt, mkRat, normalize]
@[simp] theorem mkRat_one (n : ℤ) : mkRat n 1 = n := by simp [mkRat_eq_divInt]

theorem divInt_one_one : 1 /. 1 = 1 := by rw [divInt_one, intCast_one]

protected theorem mul_assoc : a * b * c = a * (b * c) :=
  numDenCasesOn' a fun n₁ d₁ h₁ =>
    numDenCasesOn' b fun n₂ d₂ h₂ =>
      numDenCasesOn' c fun n₃ d₃ h₃ => by
        simp [h₁, h₂, h₃, Int.mul_comm, Nat.mul_assoc, Int.mul_left_comm]

protected theorem add_mul : (a + b) * c = a * c + b * c :=
  numDenCasesOn' a fun n₁ d₁ h₁ ↦ numDenCasesOn' b fun n₂ d₂ h₂ ↦ numDenCasesOn' c fun n₃ d₃ h₃ ↦ by
    simp only [ne_eq, Int.natCast_eq_zero, h₁, not_false_eq_true, h₂, divInt_add_divInt,
      Int.mul_eq_zero, or_self, h₃, divInt_mul_divInt]
    rw [← divInt_mul_right (Int.natCast_ne_zero.2 h₃), Int.add_mul, Int.add_mul]
    ac_rfl

protected theorem mul_add : a * (b + c) = a * b + a * c := by
  rw [Rat.mul_comm, Rat.add_mul, Rat.mul_comm, Rat.mul_comm c a]

protected theorem zero_ne_one : 0 ≠ (1 : ℚ) := by
  rw [ne_comm, ← divInt_one_one, divInt_ne_zero] <;> omega

attribute [simp] mkRat_eq_zero

protected theorem mul_inv_cancel : a ≠ 0 → a * a⁻¹ = 1 :=
  numDenCasesOn' a fun n d hd hn ↦ by
    simp only [divInt_ofNat, ne_eq, hd, not_false_eq_true, mkRat_eq_zero] at hn
    simp [-divInt_ofNat, mkRat_eq_divInt, Int.mul_comm, Int.mul_ne_zero hn (Int.ofNat_ne_zero.2 hd)]

protected theorem inv_mul_cancel (h : a ≠ 0) : a⁻¹ * a = 1 :=
  Eq.trans (Rat.mul_comm _ _) (Rat.mul_inv_cancel _ h)

-- Porting note: we already have a `DecidableEq ℚ`.

-- Extra instances to short-circuit type class resolution
-- TODO(Mario): this instance slows down Mathlib.Data.Real.Basic
instance nontrivial : Nontrivial ℚ where exists_pair_ne := ⟨1, 0, by decide⟩

/-! ### The rational numbers are a group -/

instance addCommGroup : AddCommGroup ℚ where
  zero := 0
  add := (· + ·)
  neg := Neg.neg
  zero_add := Rat.zero_add
  add_zero := Rat.add_zero
  add_comm := Rat.add_comm
  add_assoc := Rat.add_assoc
  neg_add_cancel := Rat.neg_add_cancel
  sub_eq_add_neg := Rat.sub_eq_add_neg
  nsmul := nsmulRec
  zsmul := zsmulRec

instance addGroup : AddGroup ℚ := by infer_instance

instance addCommMonoid : AddCommMonoid ℚ := by infer_instance

instance addMonoid : AddMonoid ℚ := by infer_instance

instance addLeftCancelSemigroup : AddLeftCancelSemigroup ℚ := by infer_instance

instance addRightCancelSemigroup : AddRightCancelSemigroup ℚ := by infer_instance

instance addCommSemigroup : AddCommSemigroup ℚ := by infer_instance

instance addSemigroup : AddSemigroup ℚ := by infer_instance

instance commMonoid : CommMonoid ℚ where
  one := 1
  mul := (· * ·)
  mul_one := Rat.mul_one
  one_mul := Rat.one_mul
  mul_comm := Rat.mul_comm
  mul_assoc := Rat.mul_assoc
  npow n q := q ^ n
  npow_zero := by intros; apply Rat.ext <;> simp [Int.pow_zero]
  npow_succ n q := by
    dsimp
    rw [← q.mk'_num_den, mk'_pow, mk'_mul_mk']
    · congr
    · rw [mk'_pow, Int.natAbs_pow]
      exact q.reduced.pow_left _
    · rw [mk'_pow]
      exact q.reduced.pow_right _

instance monoid : Monoid ℚ := by infer_instance

instance commSemigroup : CommSemigroup ℚ := by infer_instance

instance semigroup : Semigroup ℚ := by infer_instance

theorem eq_iff_mul_eq_mul {p q : ℚ} : p = q ↔ p.num * q.den = q.num * p.den := by
  conv =>
    lhs
    rw [← num_divInt_den p, ← num_divInt_den q]
  apply Rat.divInt_eq_iff <;>
    · rw [← Int.natCast_zero, Ne, Int.ofNat_inj]
      apply den_nz

@[simp]
theorem den_neg_eq_den (q : ℚ) : (-q).den = q.den :=
  rfl

@[simp]
theorem num_neg_eq_neg_num (q : ℚ) : (-q).num = -q.num :=
  rfl

-- Not `@[simp]` as `num_ofNat` is stronger.
theorem num_zero : Rat.num 0 = 0 :=
  rfl

-- Not `@[simp]` as `den_ofNat` is stronger.
theorem den_zero : Rat.den 0 = 1 :=
  rfl

theorem zero_of_num_zero {q : ℚ} (hq : q.num = 0) : q = 0 := by simpa [hq] using q.num_divInt_den.symm

theorem zero_iff_num_zero {q : ℚ} : q = 0 ↔ q.num = 0 :=
  ⟨fun _ => by simp [*], zero_of_num_zero⟩

-- `Not `@[simp]` as `num_ofNat` is stronger.
theorem num_one : (1 : ℚ).num = 1 :=
  rfl

@[simp]
theorem den_one : (1 : ℚ).den = 1 :=
  rfl

theorem mk_num_ne_zero_of_ne_zero {q : ℚ} {n d : ℤ} (hq : q ≠ 0) (hqnd : q = n /. d) : n ≠ 0 :=
  fun this => hq <| by simpa [this] using hqnd

theorem mk_denom_ne_zero_of_ne_zero {q : ℚ} {n d : ℤ} (hq : q ≠ 0) (hqnd : q = n /. d) : d ≠ 0 :=
  fun this => hq <| by simpa [this] using hqnd

theorem divInt_ne_zero_of_ne_zero {n d : ℤ} (h : n ≠ 0) (hd : d ≠ 0) : n /. d ≠ 0 :=
  (divInt_ne_zero hd).mpr h

protected theorem nonneg_antisymm : 0 ≤ q → 0 ≤ -q → q = 0 := by
  simp_rw [← num_eq_zero, Int.le_antisymm_iff, ← num_nonneg, num_neg_eq_neg_num, Int.neg_nonneg]
  tauto

protected theorem nonneg_total (a : ℚ) : 0 ≤ a ∨ 0 ≤ -a := by
  simp_rw [← num_nonneg, num_neg_eq_neg_num, Int.neg_nonneg]; exact Int.le_total _ _

section Casts

protected theorem add_divInt (a b c : ℤ) : (a + b) /. c = a /. c + b /. c :=
  if h : c = 0 then by simp [h]
  else by
    rw [divInt_add_divInt _ _ h h, divInt_eq_iff h (Int.mul_ne_zero h h)]
    simp [Int.add_mul, Int.mul_assoc]

theorem divInt_eq_div (n d : ℤ) : n /. d = (n : ℚ) / d := by simp [div_def']

theorem intCast_div_eq_divInt (n d : ℤ) : (n : ℚ) / (d) = n /. d := by rw [divInt_eq_div]

theorem natCast_div_eq_divInt (n d : ℕ) : (n : ℚ) / d = n /. d := Rat.intCast_div_eq_divInt n d

theorem divInt_mul_divInt_cancel {x : ℤ} (hx : x ≠ 0) (n d : ℤ) : n /. x * (x /. d) = n /. d := by
  by_cases hd : d = 0
  · rw [hd]
    simp
  rw [divInt_mul_divInt _ _ hx hd, x.mul_comm, divInt_mul_right hx]

theorem coe_int_num_of_den_eq_one {q : ℚ} (hq : q.den = 1) : (q.num : ℚ) = q := by
  conv_rhs => rw [← num_divInt_den q, hq]
  rw [intCast_eq_divInt]
  rfl

theorem eq_num_of_isInt {q : ℚ} (h : q.isInt) : q = q.num := by
  rw [Rat.isInt, Nat.beq_eq_true_eq] at h
  exact (Rat.coe_int_num_of_den_eq_one h).symm

theorem den_eq_one_iff (r : ℚ) : r.den = 1 ↔ ↑r.num = r :=
  ⟨Rat.coe_int_num_of_den_eq_one, fun h => h ▸ Rat.den_intCast r.num⟩

instance canLift : CanLift ℚ ℤ (↑) fun q => q.den = 1 :=
  ⟨fun q hq => ⟨q.num, coe_int_num_of_den_eq_one hq⟩⟩

-- Will be subsumed by `Int.coe_inj` after we have defined
-- `LinearOrderedField ℚ` (which implies characteristic zero).
theorem coe_int_inj (m n : ℤ) : (m : ℚ) = n ↔ m = n :=
  ⟨congr_arg num, congr_arg _⟩

end Casts
end Rat


namespace Rat

protected theorem add_comm (a b : Rat) : a + b = b + a := by
  simp only [add_def, Int.add_comm, Nat.mul_comm]

@[simp] protected theorem add_zero (r : Rat) : r + 0 = r := by
  simp [add_def]; exact normalize_self r

@[simp] protected theorem zero_add (r : Rat) : 0 + r = r := by
  rw [Rat.add_comm]; exact Rat.add_zero r

@[local simp] protected theorem add_left_neg (a : Rat) : -a + a = 0 := by
  simp only [add_def, neg_num, Int.neg_mul, neg_den, normalize_eq_zero]
  exact Int.add_left_neg _

@[local simp] protected theorem add_right_neg (a : Rat) : a + (-a) = 0 := by
  rw [Rat.add_comm]; exact Rat.add_left_neg a

@[simp] protected theorem sub_self (a : Rat) : a - a = 0 := by
  rw [Rat.sub_eq_add_neg, Rat.add_right_neg]
  done

theorem sub_eq_zero_of_eq (a b : Rat) (h : a = b) : a - b = 0 := by
  rw [h]; exact Rat.sub_self b

protected theorem add_assoc (a b c : Rat) : a + b + c = a + (b + c) := by


  done

protected theorem add_neg_cancel_right (a b : Rat) : a + b + -b = a := by


@[simp] protected theorem add_sub_cancel (a b : Rat) : a + b - b = a := by
  simp [sub_eq_add_neg]
  done

@[simp] protected theorem sub_add_cancel (a b : Rat) : a - b + b = a := by
  simp [sub_eq_add_neg]

#check Int.add_sub_cancel
#check Int.add_neg_cancel_right



end Rat
