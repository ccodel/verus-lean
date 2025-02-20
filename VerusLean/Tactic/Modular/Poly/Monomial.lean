
import Init.Data.Nat.MinMax

namespace VerusLean.Tactic.Modular

/-
CC: TODO: Right now there are an infinite number of ways to represent the
zero monomial. Annotate the type that its size is positive if its degree
sum is positive?
-/

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

def size (m : Monomial) : Nat := Array.size m
def get (m : Monomial) (i : Nat) : Nat := m.getD i 0
def get' (m : Monomial) (i : Nat) (hi : i < m.size) : Nat := m[i]

@[ext]
theorem ext (m₁ m₂ : Monomial)
    (h₁ : m₁.size = m₂.size)
    (h₂ : (i : Nat) → (hi₁ : i < m₁.size) → (hi₂ : i < m₂.size) → m₁[i] = m₂[i])
    : m₁ = m₂ := by
  exact Array.ext m₁ m₂ h₁ h₂

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
  m.set n 1 (by simp only [Array.size_mkArray, Nat.lt_add_one, m])

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
  loop 0 0

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
  loop 0 false 0

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
  let maxSize := max m₁.size m₂.size
  let rec loop (i : Nat) (m : Monomial) : Monomial :=
    if i < maxSize then
      let a₁ := m₁.get i
      let a₂ := m₂.get i
      loop (i + 1) (m.push (a₁ + a₂))
    else
      m
  loop 0 0

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

----------------------------------------

/- # theorems -/

@[simp] theorem toList_zero : Array.toList (0 : Monomial) = [] := rfl

theorem zero_eq_nil : (0 : Monomial) = #[] := rfl
@[simp] theorem nil_eq_zero : #[] = (0 : Monomial) := rfl

@[simp]
theorem push_ne_zero (m : Monomial) (n : Nat) : m.push n ≠ 0 := by
  simp [zero_eq_nil, -nil_eq_zero]

@[simp]
theorem toList_cons_ne_zero (x : Nat) (xs : List Nat)
    : ({ toList := x :: xs } : Monomial) ≠ 0 := by
  simp [zero_eq_nil, -nil_eq_zero]

@[simp] theorem size_zero : size 0 = 0 := by simp [size]
@[simp] theorem size_nil : size (#[] : Monomial) = 0 := size_zero

@[simp]
theorem zipWith_zero_left (f : Nat → β → γ) (as : Array β)
    : Array.zipWith f (0 : Monomial) as = #[] := rfl

@[simp]
theorem zipWith_zero_right (f : α → Nat → γ) (as : Array α)
    : Array.zipWith f as (0 : Monomial) = #[] := by
  simp only [Array.zipWith_eq_empty_iff, nil_eq_zero, or_true]

@[simp]
theorem size_push (m : Monomial) (n : Nat) : (m.push n).size = m.size + 1 := by
  simp [Monomial.size]


@[simp]
theorem size_zero' : Array.size (0 : Monomial) = 0 := size_zero

@[simp]
theorem size_zero_iff_eq_zero {m : Monomial} : m.size = 0 ↔ m = 0 := by
  simp [size]

@[simp]
theorem size_gt_zero_iff_ne_zero {m : Monomial} : m.size > 0 ↔ m ≠ 0 := by
  constructor
  · intro h h_con
    rw [size_zero_iff_eq_zero.mpr h_con] at h
    contradiction
  · intro h
    false_or_by_contra
    rename_i h_con
    simp at h_con
    exact absurd h_con h

@[simp]
theorem size_mul (m₁ m₂ : Monomial) : size (m₁ * m₂) = max m₁.size m₂.size := by
  simp [HMul.hMul, Mul.mul, Monomial.mul]
  have ⟨m₁⟩ := m₁
  have ⟨m₂⟩ := m₂
  stop
  induction m₁ generalizing m₂ with
  | nil =>
    rw [mul.loop]
    induction m₂ with
    | nil => simp
    | cons y ys ih =>
      simp
      done
    done
  done

@[simp]
protected theorem zero_mul (m : Monomial) : 0 * m = m := by
  have := size_zero
  stop
  by_cases hm : m = 0
  ·
    done
  simp [HMul.hMul, Mul.mul, Monomial.mul]
  rw [mul.loop]
  simp
  split
  <;> rename_i h
  · rw [h]; rfl
  ·
    done
  done

@[simp]
protected theorem mul_zero (m : Monomial) : m * 0 = m := by
  stop
  simp
  done

@[simp]
theorem mul_cons_cons (a : Nat) (as : List Nat) (b : Nat) (bs : List Nat)
    : ({ toList := a :: as } : Monomial) * { toList := b :: bs } = #[a + b] ++ ({ toList := as } * { toList := bs }) := by
  sorry
  done

protected theorem mul_comm (m₁ m₂ : Monomial) : m₁ * m₂ = m₂ * m₁ := by
  sorry
  done

protected theorem mul_assoc (m₁ m₂ m₃ : Monomial) : m₁ * m₂ * m₃ = m₁ * (m₂ * m₃) := by
  sorry
  done

@[simp] theorem eᵢ_zero : eᵢ 0 = #[1] := rfl

@[simp]
theorem size_eᵢ (i : Nat) : size (eᵢ i) = (i + 1) := by
  simp [eᵢ, Array.setIfInBounds, Monomial.size]

@[simp]
theorem get_eᵢ_eq (i j : Nat) : (eᵢ i).get j = (if i = j then 1 else 0) := by
  have := size_eᵢ i
  simp [eᵢ, get] at this ⊢
  rcases Nat.lt_trichotomy i j with (h_lt | rfl | h_gt)
  · have h_le := Nat.succ_le_of_lt h_lt
    rw [Nat.succ_eq_add_one, ← this] at h_le
    rw [Array.getElem?_eq_none h_le]
    simp [Nat.ne_of_lt h_lt]
  · simp
  · have h_gt' := Nat.lt_succ_of_lt h_gt
    rw [Nat.succ_eq_add_one, ← this] at h_gt'
    rw [Array.getElem?_eq_getElem h_gt']
    rw [Array.get_set]
    · simp [(Nat.ne_of_lt h_gt).symm]
      rw [Array.getElem_mkArray]
      simp
      exact Nat.lt_succ_of_lt h_gt

end Monomial

end VerusLean.Tactic.Modular
