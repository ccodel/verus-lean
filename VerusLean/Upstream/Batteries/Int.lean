import Init.Data.Int.DivModLemmas
import VerusLean.Upstream.Batteries.Classes

namespace Int

theorem dvd_of_mul_dvd_left {a b c : Int} : (a * b) ∣ c → a ∣ c := by
  rw [Int.dvd_def]
  rintro ⟨d, rfl⟩
  rw [Int.mul_assoc]
  exact Int.dvd_mul_right _ _

theorem dvd_of_mul_dvd_right {a b c : Int} : (a * b) ∣ c → b ∣ c :=
  Int.mul_comm .. ▸ dvd_of_mul_dvd_left

@[simp]
theorem natCast_eq_zero {n : ℕ} : (n : ℤ) = 0 ↔ n = 0 := by omega

@[simp]
theorem natCast_ne_zero {n : ℕ} : (n : ℤ) ≠ 0 ↔ n ≠ 0 := by omega

-- This lemma competes with `Int.ofNat_eq_natCast` to come later
@[simp high, norm_cast]
theorem cast_natCast {R : Type u} [AddGroupWithOne R] (n : ℕ) : ((n : ℤ) : R) = n :=
  AddGroupWithOne.intCast_ofNat _
-- expected `n` to be implicit, and `HasLiftT`

theorem natAbs_pow (n : ℤ) (k : ℕ) : Int.natAbs (n ^ k) = Int.natAbs n ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Int.pow_succ, natAbs_mul, Nat.pow_succ, ih, Nat.mul_comm]

@[simp] theorem one_ne_zero : (1 : ℤ) ≠ 0 := by trivial

-- CC: To get around neeting Mathlib's `Logic.eq_or_ne` and `Classical`
protected theorem eq_or_ne (a b : ℤ) : a = b ∨ a ≠ b := by
  by_cases h : a = b
  · exact Or.inl h
  · exact Or.inr h

--------------------------------------------------------------------------------

instance instCommMonoid : CommMonoid ℤ where
  mul_comm := Int.mul_comm
  mul_one := Int.mul_one
  one_mul := Int.one_mul
  npow n x := x ^ n
  npow_zero _ := rfl
  npow_succ _ _ := rfl
  mul_assoc := Int.mul_assoc

open Nat in
instance instAddCommGroup : AddCommGroup ℤ where
  add_comm := Int.add_comm
  add_assoc := Int.add_assoc
  add_zero := Int.add_zero
  zero_add := Int.zero_add
  neg_add_cancel := Int.add_left_neg
  nsmul := (·*·)
  nsmul_zero := Int.zero_mul
  nsmul_succ n x :=
    show (n + 1 : ℤ) * x = n * x + x
    by rw [Int.add_mul, Int.one_mul]
  zsmul := (·*·)
  zsmul_zero' := Int.zero_mul
  zsmul_succ' m n := by
    simp only [ofNat_succ, Int.add_mul, Int.add_comm, Int.one_mul]
  zsmul_neg' m n := by simp only [negSucc_coe, ofNat_succ, Int.neg_mul]
  sub_eq_add_neg _ _ := Int.sub_eq_add_neg

instance instCommRing : CommRing ℤ where
  -- Ugh... we manually include the other instances
  -- Mathlib solved this with "spreads" (see `Mathlib.Tactic.Spread`).

  -- `AddCommGroup ℤ`
  add_comm := instAddCommGroup.add_comm
  add_assoc := instAddCommGroup.add_assoc
  add_zero := instAddCommGroup.add_zero
  zero_add := instAddCommGroup.zero_add
  neg_add_cancel := instAddCommGroup.neg_add_cancel
  nsmul := instAddCommGroup.nsmul
  nsmul_zero := instAddCommGroup.nsmul_zero
  nsmul_succ := instAddCommGroup.nsmul_succ
  zsmul := instAddCommGroup.zsmul
  zsmul_zero' := instAddCommGroup.zsmul_zero'
  zsmul_succ' := instAddCommGroup.zsmul_succ'
  zsmul_neg' := instAddCommGroup.zsmul_neg'
  sub_eq_add_neg := instAddCommGroup.sub_eq_add_neg

  -- `CommMonoid ℤ`
  mul_comm := instCommMonoid.mul_comm
  mul_one := instCommMonoid.mul_one
  one_mul := instCommMonoid.one_mul
  mul_assoc := instCommMonoid.mul_assoc

  zero_mul := Int.zero_mul
  mul_zero := Int.mul_zero
  left_distrib := Int.mul_add
  right_distrib := Int.add_mul
  npow n x := x ^ n
  npow_zero _ := rfl
  npow_succ _ _ := rfl
  natCast := (·)
  natCast_zero := rfl
  natCast_succ _ := rfl
  intCast := (·)
  intCast_ofNat _ := rfl
  intCast_negSucc _ := rfl

instance instCommSemiring : CommSemiring ℤ := inferInstance
instance instSemiring     : Semiring ℤ     := inferInstance
instance instRing         : Ring ℤ         := inferInstance
instance instDistrib      : Distrib ℤ      := inferInstance

end Int
