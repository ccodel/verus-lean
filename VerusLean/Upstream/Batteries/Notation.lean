import Batteries.Data.Rat

@[inherit_doc] notation "ℕ" => Nat
@[inherit_doc] notation "ℤ" => Int
@[inherit_doc] notation "ℚ" => Rat

/-- Nonnegative rational numbers. -/
def NNRat := {q : ℚ // 0 ≤ q}

@[inherit_doc] notation "ℚ≥0" => NNRat
