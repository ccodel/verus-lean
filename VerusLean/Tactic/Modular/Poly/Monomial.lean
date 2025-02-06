namespace VerusLean.Tactic.Modular

-- Represent a monomial as an array of exponents
-- For example, `x₁² * x₂` is represented as `[2, 1]`
abbrev Monomial := Array Nat

-- An ordering function on monomials. Useful for Groebner basis computations.
abbrev MOrder := Monomial → Monomial → Ordering

namespace Monomial

protected def zero : Monomial := Array.empty
instance instZero : Zero Monomial := ⟨Monomial.zero⟩

instance instInhabited : Inhabited Monomial := ⟨0⟩
instance instDecidableEq : DecidableEq Monomial :=
  inferInstanceAs (DecidableEq (Array Nat))

def toString (m : Monomial) : String :=
  let n := m.size
  let rec loop (i : Nat) (str : String) : String :=
    if h : i < n then
      let c := m[i]
      match c with
      | 0 => loop (i + 1) str
      | 1 =>
        if str.length > 0 then  loop (i + 1) (str ++ s!" * x{i + 1}")
        else                    loop (i + 1) (str ++ s!"x{i + 1}")
      | c =>
        if str.length > 0 then  loop (i + 1) (str ++ s!" * x{i + 1}^{c}")
        else                    loop (i + 1) (str ++ s!"x{i + 1}^{c}")
    else str
  termination_by m.size - i
  let str := loop 0 ""
  if str.length = 0 then "0" else str

instance instToString : ToString Monomial := ⟨toString⟩

-- Take a 0-indexed index and return the "standard basis" monomial from it
def eᵢ (n : Nat) : Monomial :=
  let m := Array.mkArray (n + 1) 0
  m.set! n 1

def degreeSum (m : Monomial) : Nat := m.foldl (init := 0) (· + ·)

/--
  A lexicographic ordering on monomials.

  Returns `.lt` if `m₁` is lexicographically less than `m₂`, meaning that
  scanning from left to right, some `i` has `m₁[i] < m₂[i]`.
-/
def lexOrder (m₁ m₂ : Monomial) : Ordering :=
  let rec loop (i : Nat) : Ordering :=
    if h₁ : i < m₁.size then
      let mi := m₁[i]
      if h₂ : i < m₂.size then
        let mj := m₂[i]
        if mi < mj then
          Ordering.lt
        else if mi > mj then
          Ordering.gt
        else
          loop (i + 1)
      else
        if mi > 0 then
          Ordering.gt
        else
          loop (i + 1)
    else
      if h₂ : i < m₂.size then
        if m₂[i] > 0 then
          Ordering.lt
        else
          loop (i + 1)
      else
        Ordering.eq
  termination_by (m₁.size + m₂.size) - i
  loop 0

def revlexOrder (m₁ m₂ : Monomial) : Ordering :=
  lexOrder m₂ m₁

def grlexOrder (m₁ m₂ : Monomial) : Ordering :=
  let ds₁ := degreeSum m₁
  let ds₂ := degreeSum m₂
  if ds₁ < ds₂ then
    Ordering.lt
  else if ds₁ > ds₂ then
    Ordering.gt
  else
    lexOrder m₁ m₂

def grevlexOrder (m₁ m₂ : Monomial) : Ordering :=
  let ds₁ := degreeSum m₁
  let ds₂ := degreeSum m₂
  if ds₁ < ds₂ then
    Ordering.lt
  else if ds₁ > ds₂ then
    Ordering.gt
  else
    revlexOrder m₁ m₂

/--
  Returns `true` if the two monomials are coprime.

  Two monomials are coprime if they have no common factors other than 1.
  This means that for any variable index `i`, not both of `m₁` and `m₂`
  have a positive exponent for `xᵢ`.
-/
def areCoprime (m₁ m₂ : Monomial) : Bool :=
  let rec loop (i : Nat) : Bool :=
    if hi₁ : i < m₁.size then
      if hi₂ : i < m₂.size then
        if m₁[i] > 0 && m₂[i] > 0 then
          false
        else
          loop (i + 1)
      else true
    else true
  loop 0

/--
  Returns the least common multiple of two monomials.

  The least common multiple of two monomials `m₁` and `m₂` is the monomial
  formed by taking the maximum exponent for each variable index.
-/
protected def lcm (m₁ m₂ : Monomial) : Monomial :=
  let rec loop (i : Nat) (m : Monomial) : Monomial :=
    if h₁ : i < m₁.size then
      if h₂ : i < m₂.size then
        loop (i + 1) (m.push (max m₁[i] m₂[i]))
      else
        loop (i + 1) (m.push m₁[i])
    else
      if h₂ : i < m₂.size then
        loop (i + 1) (m.push m₂[i])
      else
        m
  termination_by (m₁.size + m₂.size) - i
  loop 0 Array.empty

/--
  If the two monomials are coprime, returns `none`. Otherwise, returns
  `some m`, where `m` is the least common multiple of `m₁` and `m₂`.

  CC: Perhaps it's better to return the empty (zero) monomial instead?
-/
def lcmIfNotCoprime (m₁ m₂ : Monomial) : Option Monomial :=
  /-
    We only know if the two monomials are coprime after we check all indexes.
    So we must build the LCM as we go
    However, if one of the monomials is shorter than the other and we are
    coprime, then we can return early without looping.
  -/
  let rec loop (i : Nat) (areNotCoprime : Bool) (m : Monomial) :=
    if h₁ : i < m₁.size then
      if h₂ : i < m₂.size then
        let a₁ := m₁[i]
        let a₂ := m₂[i]
        let areNotCoprime := areNotCoprime || (a₁ > 0 && a₂ > 0)
        loop (i + 1) areNotCoprime (m.push (max a₁ a₂))
      else
        if areNotCoprime then loop (i + 1) areNotCoprime (m.push m₁[i])
        else none
    else
      if h₂ : i < m₂.size then
        if areNotCoprime then loop (i + 1) areNotCoprime (m.push m₂[i])
        else none
      else
        if areNotCoprime then some m
        else none
  termination_by (m₁.size + m₂.size) - i
  loop 0 false Array.empty

protected def beq (m₁ m₂ : Monomial) : Bool :=
  let rec loop (i : Nat) : Bool :=
    if h₁ : i < m₁.size then
      if h₂ : i < m₂.size then
        if m₁[i] = m₂[i] then loop (i + 1)
        else                  false
      else
        if m₁[i] = 0 then     loop (i + 1)
        else                  false
    else
      if h₂ : i < m₂.size then
        if m₂[i] = 0 then     loop (i + 1)
        else                  false
      else                    true
  termination_by (m₁.size + m₂.size) - i
  loop 0

instance instBEq : BEq Monomial := ⟨Monomial.beq⟩

/-- Multiplies two monomials together by adding their exponents.  -/
protected def mul (m₁ m₂ : Monomial) : Monomial :=
  let rec loop (i : Nat) (m : Monomial) : Monomial :=
    if h₁ : i < m₁.size then
      if h₂ : i < m₂.size then
        loop (i + 1) (m.push (m₁[i] + m₂[i]))
      else
        loop (i + 1) (m.push m₁[i])
    else
      if h₂ : i < m₂.size then
        loop (i + 1) (m.push m₂[i])
      else
        m
  termination_by (m₁.size + m₂.size) - i
  loop 0 Array.empty

instance instMul : Mul Monomial := ⟨Monomial.mul⟩

-- Divides `m₁` by `m₂`, assuming `m₂` has smaller multidegree.
def div? (m₁ m₂ : Monomial) : Option Monomial :=
  let rec loop (i : Nat) (m : Monomial) : Option Monomial :=
    if h₁ : i < m₁.size then
      let mi := m₁[i]
      if h₂ : i < m₂.size then
        let mj := m₂[i]
        if mi ≥ mj then
          loop (i + 1) (m.push (mi - mj))
        else
          none
      else
        loop (i + 1) (m.push mi)
    else
      if h₂ : i < m₂.size then
        if m₂[i] = 0 then
          loop (i + 1) (m.push 0)
        else
          none
      else
        some m
  termination_by (m₁.size + m₂.size) - i
  loop 0 0

def div! (m₁ m₂ : Monomial) : Monomial :=
  let rec loop (i : Nat) (m : Monomial) : Monomial :=
    if h₁ : i < m₁.size then
      if h₂ : i < m₂.size then
        loop (i + 1) (m.push (m₁[i] - m₂[i]))
      else
        loop (i + 1) (m.push m₁[i])
    else
      m
  loop 0 0

instance instDiv : Div Monomial := ⟨Monomial.div!⟩

def scPow (m : Monomial) (n : Nat) : Monomial :=
  m.map (· * n)

instance instHPow : HPow Monomial Nat Monomial := ⟨Monomial.scPow⟩

end Monomial

end VerusLean.Tactic.Modular
