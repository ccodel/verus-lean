/-

  LICENSE goes here.

  Verus-Lean contributors.

-/

import VerusLean.Tactic.Modular.Poly.Monomial
import VerusLean.Upstream.Batteries.Classes

/-!

  Monomial-coefficient terms. The coefficients are in a `Field`.

-/


namespace VerusLean.Tactic.Modular

/--
  A monomial term is a coefficient `coeff` multiplied by a monomial.
-/
structure MTerm (F : Type u) [Field F] where
  coeff : F := 1
  --h_coeff : coeff ≠ 0
  monomial : Monomial := #[]
deriving Inhabited

structure MTermRef (F : Type u) [Field F] where
  coeff : F := 1
  monomial : Nat := 0
deriving Inhabited, DecidableEq

-- TODO: Replace coefficients with a general field `F`.

/-structure MTerm (F : Type u) [Field F] where
  coeff : F := 1
  monomial : Monomial := #[]
deriving Inhabited, DecidableEq

structure MTermRef (F : Type u) [Field F] where
  coeff : F := 1
  monomial : Nat := 0
deriving Inhabited, DecidableEq -/

namespace MTerm

variable {F : Type u} [Field F] [DecidableEq F]

def lexOrder (t₁ t₂ : MTerm F) : Ordering := Monomial.lexOrder t₁.monomial t₂.monomial
def revLexOrder (t₁ t₂ : MTerm F) : Ordering := Monomial.revlexOrder t₁.monomial t₂.monomial
def grlexOrder (t₁ t₂ : MTerm F) : Ordering := Monomial.grlexOrder t₁.monomial t₂.monomial
def grevlexOrder (t₁ t₂ : MTerm F) : Ordering := Monomial.grevlexOrder t₁.monomial t₂.monomial

-- protected def zero (F : outParam (Type u)) [Field F] : MTerm F := mk 0 0
-- instance instZero (F : outParam (Type u)) [Field F] : Zero (MTerm F) := ⟨MTerm.zero F⟩
-- instance instInhabited (F : outParam (Type u)) [Field F] : Inhabited (MTerm F) := ⟨0⟩

protected def zero : MTerm F := mk 0 0
instance instZero : Zero (MTerm F) := ⟨MTerm.zero⟩
instance instInhabited : Inhabited (MTerm F) := ⟨0⟩

instance instDecidableEq : DecidableEq (MTerm F) := by
  rintro ⟨c₁, m₁⟩ ⟨c₂, m₂⟩
  by_cases hc : c₁ = c₂
  · by_cases hm : m₁ = m₂
    · simp [hc, hm]; exact isTrue trivial
    · simp [hc, hm]; exact isFalse id
  · simp [hc]; exact isFalse id

protected def one : MTerm F := mk 1 0

def toString [ToString F] : MTerm F → String
  | ⟨c, m⟩ =>
  let mStr := m.toString
  if mStr = "0" then
    s!"{c}"
  else
    if c = 1 then
      s!"{m}"
    else
      s!"{c} {m}"

instance instToString (F : Type u) [Field F] [DecidableEq F] [ToString F] : ToString (MTerm F) :=
  ⟨toString⟩

instance instCoeOfNat : Coe Nat (MTerm F) := ⟨λ n => mk n 0⟩
instance instCoeOfInt : Coe Int (MTerm F) := ⟨λ i => mk i 0⟩
--instance instCoeOfCoeff : Coe Rat (MTerm F) := ⟨λ c => mk c 0⟩
instance instCoeOfMonomial : Coe Monomial (MTerm F) := ⟨λ m => mk 1 m⟩
--instance instCoeToCoeff : Coe MTerm Rat := ⟨coeff⟩
--instance instCoeToMonomial (F : Type u) [Field F] : Coe (MTerm F) Monomial := ⟨monomial⟩
--instance instCoeProd : Coe (Rat × Monomial) MTerm := ⟨λ ⟨c, m⟩ => mk c m⟩

def neg (t : MTerm F) : MTerm F :=
  mk (-t.coeff) t.monomial

protected def add (t₁ t₂ : MTerm F) : MTerm F :=
  if t₁.monomial = t₂.monomial then
    mk (t₁.coeff + t₂.coeff) t₁.monomial
  else
    panic! "monomials must be equal"

protected def sub (t₁ t₂ : MTerm F) : MTerm F :=
  if t₁.monomial = t₂.monomial then
    mk (t₁.coeff - t₂.coeff) t₁.monomial
  else
    panic! "monomials must be equal"

protected def mul (t₁ t₂ : MTerm F) : MTerm F :=
  mk (t₁.coeff * t₂.coeff) (t₁.monomial * t₂.monomial)

instance instNeg : Neg (MTerm F) := ⟨neg⟩
instance instAdd : Add (MTerm F) := ⟨MTerm.add⟩
instance instSub : Sub (MTerm F) := ⟨MTerm.sub⟩
instance instMul : Mul (MTerm F) := ⟨MTerm.mul⟩

-- It is up to the field to implement division by 0
def div? (t₁ t₂ : MTerm F) : Option (MTerm F) :=
  let ⟨c₁, m₁⟩ := t₁
  let ⟨c₂, m₂⟩ := t₂
  if c₂ = 0 then
    none
  else
    match m₁.div? m₂ with
    | none   => none
    | some m => mk (c₁ / c₂) m

/-- Division when you're confident it will work. -/
def div! (t₁ t₂ : MTerm F) : MTerm F :=
  let ⟨c₁, m₁⟩ := t₁
  let ⟨c₂, m₂⟩ := t₂
  mk (c₁ / c₂) (m₁.div! m₂)

end MTerm

--------------------------------------------------------------------------------

namespace MTermRef

variable {F : Type u} [Field F] [DecidableEq F]

protected def zero : (MTermRef F) := mk 0 0
instance instZero : Zero (MTermRef F) := ⟨MTermRef.zero⟩
instance instInhabited : Inhabited (MTermRef F) := ⟨0⟩

def toString [ToString F] : (MTermRef F) → String
  | ⟨c, m⟩ =>
  if c = 1 then
    s!"x{m}"
  else if c = -1 then
    s!"-x{m}"
  else
    s!"{c} x{m}"

instance instToString [ToString F] : ToString (MTermRef F) := ⟨toString⟩

def neg (t : MTermRef F) : MTermRef F :=
  mk (-t.coeff) t.monomial

-- Adds two monomials. Checks if their references are the same.
protected def add (t₁ t₂ : MTermRef F) : MTermRef F :=
  if t₁.monomial = t₂.monomial then
    mk (t₁.coeff + t₂.coeff) t₁.monomial
  else
    panic! "monomials must be equal"

-- Subtracts two monomials. Checks if their references are the same.
protected def sub (t₁ t₂ : MTermRef F) : MTermRef F :=
  if t₁.monomial = t₂.monomial then
    mk (t₁.coeff - t₂.coeff) t₁.monomial
  else
    panic! "monomials must be equal"

instance instNeg : Neg (MTermRef F) := ⟨neg⟩
instance instAdd : Add (MTermRef F) := ⟨MTermRef.add⟩
instance instSub : Sub (MTermRef F) := ⟨MTermRef.sub⟩

end MTermRef

end VerusLean.Tactic.Modular
