import VerusLean.Tactic.Modular.Poly.Poly
import VerusLean.Upstream.Batteries.Array

namespace VerusLean.Tactic.Modular

open Lean

-- Move these somewhere else later

namespace List

-- CC: TODO these classes can be made more general
theorem foldl_mul {R : Type u} [CommSemiring R] (f : β → R) (l : List β) (init : R)
    : l.foldl (· * f ·) init = init * l.foldl (· * f ·) 1 := by
  induction l generalizing init with
  | nil => simp
  | cons r rs ih =>
    simp [ih (init * f r), ih (f r)]
    rw [mul_assoc]

theorem foldl_add {R : Type u} [CommSemiring R] (f : β → R) (l : List β) (init : R)
    : l.foldl (· + f ·) init = init + l.foldl (· + f ·) 0 := by
  induction l generalizing init with
  | nil => simp
  | cons r rs ih =>
    simp [ih (init + f r), ih (f r)]
    rw [add_assoc]

end List

namespace Monomial

-- TODO: Move these to `Monomial.lean` later

@[simp] theorem eᵢ_one : eᵢ 1 = #[0, 1] := rfl

@[simp] theorem eᵢ_succ (i : Nat) : eᵢ (i + 1) = #[0] ++ eᵢ i := by
  induction i with
  | zero => simp
  | succ i ih =>
    sorry
    done
  done

@[simp]
theorem toList_eᵢ_succ (i : Nat) : (Monomial.eᵢ (i + 1)).toList = 0 :: (Monomial.eᵢ i).toList := by
  induction i with
  | zero => simp
  | succ i ih => simp [ih]

-----------------------

variable {R : Type u} [CommRing R]

protected def eval (m : Monomial) (atoms : Array R) : R :=
  Array.zipWith (· ^ ·) atoms m
    |>.foldl (· * ·) 1

-- `eval_asList`
def eval' (m : List Nat) (atoms : List R) :=
  List.zipWith (· ^ ·) atoms m
    |>.foldl (· * ·) 1

@[simp]
protected theorem eval_eq_eval' (m : Monomial) (atoms : Array R)
    : m.eval atoms = eval' m.toList atoms.toList := by
  have ⟨atoms⟩ := atoms
  have ⟨m⟩ := m
  simp [Monomial.eval, eval']

@[simp]
theorem eval_zero (atoms : Array R) : Monomial.eval 0 atoms = 1 := by
  have ⟨atoms⟩ := atoms
  simp [eval']

@[simp]
theorem eval'_nil_left (atoms : List R) : eval' [] atoms = 1 := by
  simp [eval']

@[simp]
theorem eval'_nil_right (m : List Nat) : eval' m ([] : List R) = 1 := by
  simp [eval']

@[simp]
theorem eval'_cons_cons (a : R) (as : List R) (e : Nat) (m : List Nat)
    : eval' (e :: m) (a :: as) = a ^ e * eval' m as := by
  simp [eval']
  rw [List.foldl_mul]

@[simp]
theorem eval_eᵢ_succ_zero (a : R) (atoms : List R)
    : Monomial.eval (Monomial.eᵢ 0) { toList := (a :: atoms) } = a := by
  simp [eval']

@[simp]
theorem eval_eᵢ_succ_cons (a : R) (atoms : List R) (i : Nat)
    : Monomial.eval (Monomial.eᵢ (i + 1)) { toList := (a :: atoms) }
        = Monomial.eval (Monomial.eᵢ i) { toList := atoms } := by
  simp [eval']

@[simp]
theorem eval_eᵢ (atoms : Array R) (i : Nat)
    : Monomial.eval (Monomial.eᵢ i) atoms = atoms[i]?.getD 1 := by
  simp
  have ⟨atoms⟩ := atoms
  induction atoms generalizing i with
  | nil => simp [eval']
  | cons a as ih =>
    match i with
    | 0 => simp [eval']
    | i + 1 => simp [ih]

@[simp]
theorem eval_mul (m₁ m₂ : Monomial) (atoms : Array R)
    : Monomial.eval (m₁ * m₂) atoms = m₁.eval atoms * m₂.eval atoms := by
  have ⟨atoms⟩ := atoms
  have ⟨m₁⟩ := m₁
  have ⟨m₂⟩ := m₂
  simp only [Monomial.eval_eq_eval']
  induction atoms generalizing m₁ m₂ with
  | nil => simp only [eval'_nil_right, mul_one]
  | cons a as ih =>
    match m₁ with
    | .nil => simp only [nil_eq_zero, Monomial.zero_mul, eval'_nil_left, one_mul]
    | .cons e₁ es₁ =>
      match m₂ with
      | .nil => simp
      | .cons e₂ es₂ =>
        simp [ih]
        simp only [← mul_assoc]
        rw [mul_assoc (a ^ e₁), mul_comm _ (a ^ e₂), ← mul_assoc, pow_add]

end Monomial

namespace MTerm

variable {F : Type u} [Field F] [DecidableEq F]

theorem add_of_eq {t₁ t₂ : M[F]} (h : t₁.monomial = t₂.monomial)
    : t₁ + t₂ = { coeff := t₁.coeff + t₂.coeff, monomial := t₁.monomial } := by
  simp only [HAdd.hAdd, Add.add, MTerm.add, h, ↓reduceIte]

theorem sub_of_eq {t₁ t₂ : M[F]} (h : t₁.monomial = t₂.monomial)
    : t₁ - t₂ = { coeff := t₁.coeff - t₂.coeff, monomial := t₁.monomial } := by
  simp only [HSub.hSub, Sub.sub, MTerm.sub, h, ↓reduceIte]

--------------------------------------------------------------------------------

protected def eval (t : M[F]) (atoms : Array F) : F :=
  t.coeff * t.monomial.eval atoms

def eval' (c : F) (m : List Nat) (atoms : List F) : F :=
  c * Monomial.eval' m atoms

@[simp]
protected theorem eval_eq_eval' (t : M[F]) (atoms : Array F)
    : t.eval atoms = eval' t.coeff t.monomial.toList atoms.toList := by
  simp [MTerm.eval, eval']

@[simp]
protected theorem eval'_nil_left (c : F) (atoms : List F) : eval' c [] atoms = c := by
  simp [eval']

@[simp]
protected theorem eval'_nil_right (c : F) (m : List Nat) : eval' c m [] = c := by
  simp [eval']

end MTerm

namespace Poly

variable {F : Type v} [Field F] [DecidableEq F]

-- TODO: Move these to Poly

@[simp] theorem toList_zero : Array.toList (0 : P[F]) = [] := rfl

theorem zero_eq_nil : (0 : P[F]) = #[] := rfl
@[simp] theorem nil_eq_zero : #[] = (0 : P[F]) := rfl

@[simp] theorem size_zero : size (0 : P[F]) = 0 := rfl
@[simp] theorem size_zero' : size ({ toList := [] } : P[F]) = 0 := rfl

@[simp] theorem size_cons (t : M[F]) (ts : List M[F])
    : size ({ toList := t :: ts } : P[F]) = size ({ toList := ts }) + 1 := rfl

@[simp]
protected theorem add_zero (p : P[F]) : p + 0 = p := by
  have ⟨p⟩ := p
  simp only [HAdd.hAdd, Add.add, Poly.add]
  rw [add.loop]
  simp
  induction p with
  | nil => simp
  | cons t ts ih =>
    simp
    sorry
    done

@[simp]
protected theorem zero_add (p : P[F]) : 0 + p = p := by
  have ⟨p⟩ := p
  simp only [HAdd.hAdd, Add.add, Poly.add]
  rw [add.loop]
  simp
  induction p with
  | nil => simp
  | cons t ts ih =>
    simp
    sorry
    done

--instance instCommSemiring : CommSemiring P[F] := by sorry

protected def eval (p : P[F]) (atoms : Array F) : F :=
  p.foldl (init := (0 : F)) (fun acc t => acc + (t.eval atoms))

protected def eval' (p : List (F × List Nat)) (atoms : List F) : F :=
  p.foldl (init := (0 : F)) (fun acc ⟨c, m⟩ => acc + (MTerm.eval' c m atoms))

@[simp]
protected theorem eval_eq_eval' (p : P[F]) (atoms : Array F)
    : p.eval atoms
        = Poly.eval' ((p.toList).map (fun t => (t.coeff, t.monomial.toList))) atoms.toList := by
  have ⟨p⟩ := p
  have ⟨atoms⟩ := atoms
  simp [Poly.eval, Poly.eval']
  induction p with
  | nil => simp
  | cons t ts ih =>
    simp only [List.foldl_cons, zero_add, List.map_cons]
    rw [List.foldl_add, ih]
    conv => rhs; rw [List.foldl_add]

@[simp] theorem eval'_nil_left (atoms : List F) : Poly.eval' [] atoms = 0 := rfl

@[simp]
theorem eval_eᵢ (i : Nat) (atoms : Array F)
    : Poly.eval #[Monomial.eᵢ i] atoms = atoms.getD i 1 := by
  simp [Poly.eval', MTerm.eval']
  rw [← Monomial.eval_eq_eval']
  exact Monomial.eval_eᵢ atoms i

@[simp]
theorem eval_add (p₁ p₂ : P[F]) (atoms : Array F)
    : (p₁ + p₂).eval atoms = p₁.eval atoms + p₂.eval atoms := by
  have ⟨p₁⟩ := p₁
  have ⟨p₂⟩ := p₂
  have ⟨atoms⟩ := atoms
  simp [Poly.eval']
  induction p₁ generalizing p₂ with
  | nil => simp
  | cons t ts ih =>
    simp
    conv => rhs; rw [List.foldl_add]
    stop
    done
  done

@[simp]
theorem eval_sub (p₁ p₂ : P[F]) (atoms : Array F)
    : (p₁ - p₂).eval atoms = p₁.eval atoms - p₂.eval atoms := by
  stop
  done

@[simp]
theorem eval_neg (p : P[F]) (atoms : Array F)
    : (-p).eval atoms = -(p.eval atoms) := by
  sorry
  done

@[simp]
theorem eval_tmul (t : M[F]) (p : P[F]) (atoms : Array F)
    : (t * p).eval atoms = t.eval atoms * p.eval atoms := by
  stop
  done

@[simp]
theorem eval_mul (p₁ p₂ : P[F]) (atoms : Array F)
    : (p₁ * p₂).eval atoms = p₁.eval atoms * p₂.eval atoms := by
  stop
  done

end Poly

#exit


namespace Poly

variable {R : Type u} [CommRing R]

/-

BIG TODO: For now, we assume the coefficients of the polynomial are
elements of a `CommRing`. However, Buchberger's algorithm assumes
that the underlying coefficients lie in a field. We can get around this
by not normalizing, or by computing on the rationals and then re-normalizing
afterwards(?).

NOTE: We must have at least a `CommRing` to ensure that multiplication during
evaluation is commutative(?) and that we have additive inverses.

-/

def toExpr (p : Poly) : Expr :=
  let p := p.map (fun ⟨c, m⟩ => m)
  ToExpr.toExpr (p : Array Monomial)

-- TODO: Refactor to include `R` later
def toTypeExpr : Expr :=
  .const ``Poly []

instance instToExpr : ToExpr Poly := ⟨toExpr, toTypeExpr⟩


def eval (p : Poly) (atoms : Array R) : R :=
  p.foldl (init := 0) (fun acc ⟨c, m⟩ => acc + Monomial.eval m atoms)

@[simp]
theorem eval_monomial (m : Monomial) (atoms : Array R)
    : eval (↑m) atoms = Monomial.eval m atoms := by
  simp [Poly.eval]
  exact AddMonoid.zero_add (m.eval atoms) -- TODO: Mark the exports? in classes

@[simp]
theorem eval_eᵢ (i : Nat) (atoms : Array R)
    : eval (Monomial.eᵢ i) atoms = atoms.get! i := by
  simp

@[simp]
theorem eval_add (p₁ p₂ : Poly) (atoms : Array R)
    : eval (p₁ + p₂) atoms = eval p₁ atoms + eval p₂ atoms := by
  sorry
  done

@[simp]
theorem eval_sub (p₁ p₂ : Poly) (atoms : Array R)
    : eval (p₁ - p₂) atoms = (eval p₁ atoms) - (eval p₂ atoms) := by
  sorry
  done



@[simp]
theorem eval_mul (p₁ p₂ : Poly) (atoms : Array R)
    : eval (p₁ * p₂) atoms = (eval p₁ atoms) * (eval p₂ atoms) := by
  sorry
  done

/-@[simp]
theorem eval_scmul (sc : R) (p : Poly) (atoms : Array R)
    : eval (sc * p) atoms = sc * (eval p atoms) := by
  sorry
  done -/

end Poly

namespace VerusLean.Tactic.Modular

-- Evaluate dot products of (variable) atoms with monomials, polynomials, etc.

namespace Monomial

variable {R : Type u} [CommSemiring R]

def eval (m : Monomial) (atoms : Array R) : R :=
  if m.size > atoms.size then
    panic! "Monomial.eval: not enough atoms"
  else
    Array.zipWith (fun exp atom =>
      match exp with
      | 0 => (1 : R)
      | 1 => atom
      | e => Monoid.npow e atom
    ) m atoms
  |>.foldl (· * ·) 1
  /-let rec loop (i : Nat) (acc : R) : R :=
    if hi₁ : i < m.size then
      if hi₂ : i < atoms.size then
        let exp := m[i]
        match exp with
        | 0 => loop (i + 1) acc
        | 1 => loop (i + 1) (acc * atoms[i])
        | e => loop (i + 1) (acc * (Monoid.npow m[i] atoms[i]))
      else
        acc
    else
      acc
  loop 0 1 -/

@[simp]
theorem eval_zero (atoms : Array R) : eval 0 atoms = 1 := by
  simp [eval]
  have ⟨atoms⟩ := atoms
  stop
  rw [Array.zipWith_eq]
  induction atoms with
  | nil =>
    simp
    done
  done

@[simp]
theorem eval_zero_mul (m : Monomial) (atoms : Array R) : eval (0 * m) atoms = eval m atoms := by
  simp only [zero_mul]
  done

@[simp]
theorem eval_mul_zero (m : Monomial) (atoms : Array R) : eval (m * 0) atoms = eval m atoms := by
  simp only [mul_zero]
  done

@[simp]
theorem eval_eᵢ (atoms : Array R) (i : Nat) : eval (Monomial.eᵢ i) atoms = atoms.get! i := by
  stop
  rw [eval, eval.loop]
  simp
  done

end Monomial

end VerusLean.Tactic.Modular
