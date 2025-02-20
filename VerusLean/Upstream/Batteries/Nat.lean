import Batteries.Data.Nat.Lemmas
import VerusLean.Upstream.Batteries.Notation

namespace Nat

-- We want to use this lemma earlier than the lemma simp can prove it with
@[simp] protected theorem pow_eq_zero {a : ℕ} : ∀ {n : ℕ}, a ^ n = 0 ↔ a = 0 ∧ n ≠ 0
  | 0 => by simp
  | n + 1 => by rw [Nat.pow_succ, mul_eq_zero, Nat.pow_eq_zero]; omega

end Nat
