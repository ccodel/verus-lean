import VerusLean.Tactic.Modular.Poly.Monomial
import VerusLean.Tactic.Modular.Poly.Classes


namespace VerusLean.Tactic.Modular

/--
  A monomial term is a coefficient `coeff` multiplied by a monomial.
-/
structure MTerm where
  coeff : Rat := 1
  monomial : Monomial := #[]
deriving Inhabited, DecidableEq

structure MTermRef where
  coeff : Rat := 1
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

def lexOrder (t₁ t₂ : MTerm) : Ordering := Monomial.lexOrder t₁.monomial t₂.monomial
def revLexOrder (t₁ t₂ : MTerm) : Ordering := Monomial.revlexOrder t₁.monomial t₂.monomial
def grlexOrder (t₁ t₂ : MTerm) : Ordering := Monomial.grlexOrder t₁.monomial t₂.monomial
def grevlexOrder (t₁ t₂ : MTerm) : Ordering := Monomial.grevlexOrder t₁.monomial t₂.monomial

-- protected def zero (F : outParam (Type u)) [Field F] : MTerm F := mk 0 0
-- instance instZero (F : outParam (Type u)) [Field F] : Zero (MTerm F) := ⟨MTerm.zero F⟩
-- instance instInhabited (F : outParam (Type u)) [Field F] : Inhabited (MTerm F) := ⟨0⟩

protected def zero : MTerm := mk 0 0
instance instZero : Zero MTerm := ⟨MTerm.zero⟩
instance instInhabited : Inhabited MTerm := ⟨0⟩

protected def one : MTerm := mk 1 0

def toString : MTerm → String
  | ⟨c, m⟩ =>
  let mStr := m.toString
  if mStr = "0" then
    s!"{c}"
  else
    if c = 1 then
      s!"{m}"
    else if c = -1 then
      s!"-{m}"
    else
      s!"{c} {m}"

instance instToString : ToString MTerm := ⟨toString⟩

instance instCoeOfNat : Coe Nat MTerm := ⟨λ n => mk n 0⟩
instance instCoeOfInt : Coe Int MTerm := ⟨λ i => mk i 0⟩
instance instCoeOfCoeff : Coe Rat MTerm := ⟨λ c => mk c 0⟩
instance instCoeOfMonomial : Coe Monomial MTerm := ⟨λ m => mk 1 m⟩
instance instCoeToCoeff : Coe MTerm Rat := ⟨coeff⟩
instance instCoeToMonomial : Coe MTerm Monomial := ⟨monomial⟩
instance instCoeProd : Coe (Rat × Monomial) MTerm := ⟨λ ⟨c, m⟩ => mk c m⟩

def neg (t : MTerm) : MTerm :=
  mk (-t.coeff) t.monomial

protected def add (t₁ t₂ : MTerm) : MTerm :=
  if t₁.monomial == t₂.monomial then
    mk (t₁.coeff + t₂.coeff) t₁.monomial
  else
    panic! "monomials must be equal"

protected def sub (t₁ t₂ : MTerm) : MTerm :=
  if t₁.monomial == t₂.monomial then
    mk (t₁.coeff - t₂.coeff) t₁.monomial
  else
    panic! "monomials must be equal"

protected def mul (t₁ t₂ : MTerm) : MTerm :=
  mk (t₁.coeff * t₂.coeff) (t₁.monomial * t₂.monomial)

instance instNeg : Neg MTerm := ⟨neg⟩
instance instAdd : Add MTerm := ⟨MTerm.add⟩
instance instSub : Sub MTerm := ⟨MTerm.sub⟩
instance instMul : Mul MTerm := ⟨MTerm.mul⟩

def div? (t₁ t₂ : MTerm) : Option MTerm :=
  let ⟨c₁, m₁⟩ := t₁
  let ⟨c₂, m₂⟩ := t₂
  if c₂ = 0 then
    none
  else do
    let m ← m₁.div? m₂
    mk (c₁ / c₂) m

/-- Division when you're confident it will work. -/
def div! (t₁ t₂ : MTerm) : MTerm :=
  let ⟨c₁, m₁⟩ := t₁
  let ⟨c₂, m₂⟩ := t₂
  mk (c₁ / c₂) (m₁.div! m₂)

end MTerm

--------------------------------------------------------------------------------

namespace MTermRef

protected def zero : MTermRef := mk 0 0
instance instZero : Zero MTermRef := ⟨MTermRef.zero⟩
instance instInhabited : Inhabited MTermRef := ⟨0⟩

def toString : MTermRef → String
  | ⟨c, m⟩ =>
  if c = 1 then
    s!"x{m}"
  else if c = -1 then
    s!"-x{m}"
  else
    s!"{c} x{m}"

instance instToString : ToString MTermRef := ⟨toString⟩

def neg (t : MTermRef) : MTermRef :=
  mk (-t.coeff) t.monomial

-- Adds two monomials. Checks if their references are the same.
protected def add (t₁ t₂ : MTermRef) : MTermRef :=
  if t₁.monomial = t₂.monomial then
    mk (t₁.coeff + t₂.coeff) t₁.monomial
  else
    panic! "monomials must be equal"

-- Subtracts two monomials. Checks if their references are the same.
protected def sub (t₁ t₂ : MTermRef) : MTermRef :=
  if t₁.monomial = t₂.monomial then
    mk (t₁.coeff - t₂.coeff) t₁.monomial
  else
    panic! "monomials must be equal"

instance instNeg : Neg MTermRef := ⟨neg⟩
instance instAdd : Add MTermRef := ⟨MTermRef.add⟩
instance instSub : Sub MTermRef := ⟨MTermRef.sub⟩

end MTermRef

end VerusLean.Tactic.Modular
