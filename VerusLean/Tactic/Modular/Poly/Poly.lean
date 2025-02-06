import VerusLean.Tactic.Modular.Poly.MTerm

namespace VerusLean.Tactic.Modular

/-structure Poly where
  -- const : Rat := 0
  terms : Array MTerm
deriving Inhabited, DecidableEq

structure PolyRef where
  -- const : Rat := 0
  terms : Array MTermRef
deriving Inhabited, DecidableEq-/

/-- Concrete representation of polynomials. (Array of `MTerm`s.) -/
abbrev Poly := Array MTerm

inductive PolyHistory where
  | zero
  | basis (idx : Nat)
  | scalarMul (c : Rat) (p : PolyHistory)
  | termMul (t : MTerm) (p : PolyHistory)
  | addHist (p₁ p₂ : PolyHistory)
  | subHist (p₁ p₂ : PolyHistory)
deriving Inhabited

structure HPoly where
  poly : Poly
  history : PolyHistory
deriving Inhabited

structure PolyRef where
  index : Nat
  history : PolyHistory
deriving Inhabited


namespace Poly

def size (p : Poly) : Nat := Array.size p

protected def zero : Poly := #[]
protected def one : Poly := #[MTerm.one]

instance instZero : Zero Poly := ⟨Poly.zero⟩
instance instInhabited : Inhabited Poly := ⟨0⟩

instance instCoeOfMTerm : Coe MTerm Poly := ⟨λ t => #[t]⟩
instance instCoeOfMonomial : Coe Monomial Poly := ⟨λ m => #[m]⟩

def toString (p : Poly) : String :=
  let rec loop (i : Nat) (str : String) : String :=
    if h : i < p.size then
      let t := p[i]
      let c := t.coeff
      let m := t.monomial
      if c < 0 then
        if str.length > 0 then
          loop (i + 1) (str ++ s!" - {MTerm.mk (-c) m}")
        else
          loop (i + 1) s!"-{MTerm.mk (-c) m}"
      else
        if str.length > 0 then
          loop (i + 1) (str ++ s!" + {t}")
        else
          loop (i + 1) s!"{t}"
    else str
  loop 0 ""

instance instToString : ToString Poly := ⟨toString⟩

def leadingTerm (p : Poly) : MTerm :=
  if h : p.size > 0 then
    p[0]
  else
    ⟨0, 0⟩

def normalize (p : Poly) : Poly :=
  if p.size = 0 then p else
  let leadingCoeff := p.leadingTerm.coeff
  p.map (λ t => ⟨t.coeff / leadingCoeff, t.monomial⟩)

protected def neg (p : Poly) : Poly :=
  p.map (λ t => -t)

instance instNeg : Neg Poly := ⟨Poly.neg⟩

/--
  Adds two polynomials by combining like terms.

  Assumes that the polynomial is sorted in decreasing order under `cmp`.
-/
protected def add (p₁ p₂ : Poly) (cmp : MOrder := Monomial.grevlexOrder) : Poly :=
  let numTerms₁ := p₁.size
  let numTerms₂ := p₂.size
  let totalNumTerms := numTerms₁ + numTerms₂
  let rec loop (i j : Nat) (p : Poly) : Poly :=
    if i + j < totalNumTerms then
      if hi : i < numTerms₁ then
        if hj : j < numTerms₂ then
          let t₁ := p₁[i]
          let t₂ := p₂[j]
          let c₁ := t₁.coeff
          let c₂ := t₂.coeff
          let m₁ := t₁.monomial
          let m₂ := t₂.monomial
          match cmp m₁ m₂ with
          | .lt => loop i (j + 1) (p.push t₂)    -- Push the larger one
          | .gt => loop (i + 1) j (p.push t₁)    -- Push the smaller one
          | .eq =>
            -- Check if the coefficients cancel
            let c := c₁ + c₂
            if c ≠ 0 then
              loop (i + 1) (j + 1) (p.push (MTerm.mk c m₁))
            else
              loop (i + 1) (j + 1) p
        else
          -- p₂ is done, so push the rest of p₁
          loop (i + 1) j (p.push p₁[i])
      else if hj : j < numTerms₂ then
        -- p₁ is done, so push the rest of p₂
        loop i (j + 1) (p.push p₂[j])
      else
        p
    else
      p
  termination_by totalNumTerms - i - j
  loop 0 0 0

-- NB: This will use the `grevLexOrder` ordering.
--     To supply a different ordering, call `add` directly.
instance instAdd : Add Poly := ⟨Poly.add⟩

protected def sub (p₁ p₂ : Poly) (cmp : MOrder := Monomial.grevlexOrder) : Poly :=
  let numTerms₁ := p₁.size
  let numTerms₂ := p₂.size
  let totalNumTerms := numTerms₁ + numTerms₂
  let rec loop (i j : Nat) (p : Poly) : Poly :=
    if i + j < totalNumTerms then
      if hi : i < numTerms₁ then
        if hj : j < numTerms₂ then
          let t₁ := p₁[i]
          let t₂ := p₂[j]
          let c₁ := t₁.coeff
          let c₂ := t₂.coeff
          let m₁ := t₁.monomial
          let m₂ := t₂.monomial
          match cmp m₁ m₂ with
          | .lt => loop i (j + 1) (p.push (-t₂)) -- Push the larger one
          | .gt => loop (i + 1) j (p.push t₁)    -- Push the smaller one
          | .eq =>
            -- Check if the coefficients cancel
            let c := c₁ - c₂
            if c ≠ 0 then
              loop (i + 1) (j + 1) (p.push (MTerm.mk c m₁))
            else
              loop (i + 1) (j + 1) p
        else
          -- p₂ is done, so push the rest of p₁
          loop (i + 1) j (p.push p₁[i])
      else if hj : j < numTerms₂ then
        -- p₁ is done, so push the rest of p₂
        loop i (j + 1) (p.push p₂[j])
      else
        p
    else
      p
  termination_by totalNumTerms - i - j
  loop 0 0 0

-- NB: This will use the `grevLexOrder` ordering.
--     To supply a different ordering, call `add` directly.
instance instSub : Sub Poly := ⟨Poly.sub⟩

def mul_term_poly (t : MTerm) (p : Poly) : Poly :=
  p.map (λ t' => t * t')

def mul_poly_term (p : Poly) (t : MTerm) : Poly :=
  p.map (λ t' => t' * t)

instance instHMulTermPoly : HMul MTerm Poly Poly := ⟨mul_term_poly⟩
instance instHMulPolyTerm : HMul Poly MTerm Poly := ⟨mul_poly_term⟩

protected def mul (p₁ p₂ : Poly) (cmp : MOrder := Monomial.grevlexOrder) : Poly :=
  let prods := p₂.map (λ t₂ => p₁ * t₂)
  prods.foldl (init := 0) (Poly.add · · cmp)

instance instMul : Mul Poly := ⟨Poly.mul⟩

-- Divides `p₁` by `p₂`. Returns a pair `(q, r)`.
-- If `p₂` is zero, returns `(0, 0)`.
protected partial def div (p₁ p₂ : Poly) (cmp : MOrder := Monomial.grevlexOrder) : Poly × Poly :=
  let lt₂ := p₂.leadingTerm
  if lt₂ = 0 then (0, 0) else

  /-
    Repeatedly loop on the remainder `r` until the leading term of `p₂` (`lt₂`)
    cannot divide the leading term of `r`. Subtract the new term from `r`
    and add the appropriate quotient to `q`.
  -/
  let rec loop (q r : Poly) : Poly × Poly :=
    if r = 0 then (q, 0) else
    let ltr := r.leadingTerm
    match ltr.div? lt₂ with
    | none => (q, r)
    | some qt =>
      let q' := Poly.add q qt cmp
      -- CC: This can probably be optimized(?)
      let r' := Poly.sub r (qt * p₂) cmp
      loop q' r'
  loop 0 p₁

/--
  Divides a polynomial `p` by an array of polynomials `ps`.

  Returns a pair `(qs, r)`, where `qs` is an array of quotients of the same
  size as `ps`, and where `r` is the remainder polynomial, such that

    `p = ps ⬝ qs + r`

  where `·` denotes the dot product under polynomial multiplication.

  The caller must ensure that `ps` does not contain the zero polynomial.

  The division is unique up to the ordering of the polynomials in `ps`.
-/
partial def divPolys (p : Poly) (ps : Array Poly)
    (cmp : MOrder := Monomial.grevlexOrder) : (Array Poly × Poly) :=
  let n := ps.size
  let rec loop (p r : Poly) (qs : Array Poly)
      (hqs : qs.size = ps.size) : (Array Poly × Poly) :=
    if p = 0 then (qs, r) else
    let ltp := p.leadingTerm

    let rec innerLoop (i : Nat) :=
      if hi : i < n then
        -- TODO: ASSUMES NOT ZERO POLY HERE
        let lti := ps[i].leadingTerm
        match ltp.div? lti with
        | none => innerLoop (i + 1)
        | some qt =>
          let qt_mul_pi := qt * ps[i]
          let qs' := qs.set i (Poly.add qs[i] qt cmp)
          let p' := Poly.sub p qt_mul_pi cmp
          loop p' r qs' (by simp [qs', hqs])
      else
        -- No division was found, subtract and return
        let r' := Poly.add r ltp cmp
        let p' := Poly.sub p ltp cmp
        loop p' r' qs hqs

    innerLoop 0

  let qs : Array Poly := Array.mkArray ps.size 0
  have hqs : qs.size = ps.size := by
    simp only [Array.size_mkArray, qs]
  loop p 0 qs hqs

end Poly

/-
  Constructs the "S-polynomial"
-/
/-def sPoly (basis : Array HPoly) (i j : Nat)
    (hi : i < basis.size) (hj : j < basis.size) (cmp : MOrder) : (Unit ⊕ HPoly) :=

  let ⟨f, fHist⟩ := basis[i]
  let ⟨g, gHist⟩ := basis[j]
  if hf : f.size = 0 then panic! "sPoly: f is zero" else
  if hg : g.size = 0 then panic! "sPoly: g is zero" else

  let ltf := leadingTerm' (by exact Nat.zero_lt_of_ne_zero hf)
  let ltg := leadingTerm' (by exact Nat.zero_lt_of_ne_zero hg)
  match Monomial.lcmIfNotCoprime ltf.monomial ltg.monomial with
  | .inl _ => Sum.inl ()
  | .inr lcm =>
    if secondCriterion basis i j lcm hj then
      match MTerm.div? lcm ltf, MTerm.div? lcm ltg with
      | none, _
      | _, none => panic! "bad lcm division"
      | some qf, some qg =>
        let left := qf * f
        let leftHist := History.termMul qf fHist
        let right := qg * g
        let rightHist := History.termMul qg gHist
        let sp := Polynomial.sub (qf * f) (qg * g) cmp
        let hist := leftHist - rightHist
        Sum.inr <| HPoly.mk sp (leftHist - rightHist)
    else
      Sum.inl ()

end Poly -/

namespace PolyHistory

instance instZero : Zero PolyHistory := ⟨.zero⟩

/-def toString : History → String
  | .Zero => ""
  | .Basis idx => s!"basis[{idx}]"
  | .ScalarMul c p =>
    let pStr := toString p
    if pStr.length = 0 then ""
    else
      if c = 1 then
        pStr
      else if c = -1 then
        s!"- {pStr}"
      else
        s!"({c} * {toString p})"
  | .TermMul t p =>
      s!"({t} * {toString p})"
  | .Add p₁ p₂ =>
    let pStr₁ := toString p₁
    let pStr₂ := toString p₂
    if pStr₁.length = 0 then pStr₂
    else if pStr₂.length = 0 then pStr₁
    else s!"({pStr₁} + {pStr₂})"
  | .Sub p₁ p₂ =>
    let pStr₁ := toString p₁
    let pStr₂ := toString p₂
    if pStr₁.length = 0 then pStr₂
    else if pStr₂.length = 0 then pStr₁
    else s!"({pStr₁} - {pStr₂})"-/

def toString : PolyHistory → String
  | .zero => "0"
  | .basis idx => s!"[{idx}]"
  | .scalarMul c p => s!"({c} * {toString p})"
  | .termMul t p => s!"({t} * {toString p})"
  | .addHist p₁ p₂ => s!"({toString p₁} + {toString p₂})"
  | .subHist p₁ p₂ => s!"({toString p₁} - {toString p₂})"

instance instToString : ToString PolyHistory := ⟨toString⟩

def pushNeg : PolyHistory → PolyHistory
  | .zero => .zero
  | .basis idx => .scalarMul (-1) (.basis idx)
  | .scalarMul c h =>
    if c = -1 then h
    else .scalarMul (-c) h
  | .termMul t h => .termMul (-t) h
  | .addHist h₁ h₂ => .subHist (pushNeg h₁) h₂
  | .subHist h₁ h₂ => .addHist (pushNeg h₁) h₂

protected def add : PolyHistory → PolyHistory → PolyHistory
  | .zero, h₂ => h₂
  | h₁, .zero => h₁
  | h₁, h₂ => .addHist h₁ h₂

instance instAdd : Add PolyHistory := ⟨.add⟩

protected def sub : PolyHistory → PolyHistory → PolyHistory
  | .zero, h₂ => .scalarMul (-1) h₂
  | h₁, .zero => h₁
  | h₁, h₂ => .subHist h₁ h₂

instance instSub : Sub PolyHistory := ⟨.sub⟩

def scmul : Rat → PolyHistory → PolyHistory
  | _, .zero => .zero
  | c, h =>
    if c = 1 then h
    else if c = -1 then pushNeg h
    else .scalarMul c h

instance instScMul : HMul Rat PolyHistory PolyHistory := ⟨scmul⟩

end PolyHistory

--------------------------------------------------------------------------------

namespace HPoly

open Poly

def toString (p : HPoly) : String :=
  let ⟨p, h⟩ := p
  s!"⟪{p}, {h}⟫"
instance instToString : ToString HPoly := ⟨toString⟩

-- Returns `true` if the criterion means that we should check the `(i, j)` pair
-- In other words, if for all `l`, the leading term doesn't divide the `lcm`
def secondCriterion (basis : Array HPoly) (i j : Nat) (lcm : Monomial)
    (hj : j < basis.size) : Bool :=
  /- Buchberger's second criterion is to run over all pairs (i, l) and (j, l)
     that we have already visited in buchberger's algorithm and check that
     LT(l) does NOT divide LCM(LT(i), LT(j)). -/
  let rec loop (l : Nat) : Bool :=
    if hl : l < j then
      if l = i then
        loop (l + 1)
      else
        let ⟨p, _⟩ := basis[l]
        let ltl := p.leadingTerm.monomial
        match lcm.div? ltl with
        | none => loop (l + 1)
        | some _ => false
    else
      true
  loop 0

-- Divides by the leading coefficient across the whole polynomial.
-- This makes the leading coefficient 1.
def normalize (p : HPoly) : HPoly :=
  let ⟨p, pHist⟩ := p
  if p = 0 then ⟨p, pHist⟩ else
  let leadingCoeff := p.leadingTerm.coeff
  let pDivC := p.map (λ ⟨c, m⟩ =>
    MTerm.mk (c / leadingCoeff) m
  )
  HPoly.mk pDivC ((1 / leadingCoeff) * pHist)

/--
  Returns the S-polynomial, if the second criterion is met.
  Otherwise, returns `none`.

  The caller must ensure that neither `basis[i]` nor `basis[j]` is 0.
-/
def sPoly (basis : Array HPoly) (i j : Nat)
    (hi : i < basis.size) (hj : j < basis.size) (cmp : MOrder) : Option HPoly :=

  let ⟨f, fHist⟩ := basis[i]
  let ⟨g, gHist⟩ := basis[j]

  let ltf := f.leadingTerm
  let ltg := g.leadingTerm

  match Monomial.lcmIfNotCoprime ltf.monomial ltg.monomial with
  | none => none
  | some lcm =>
    if secondCriterion basis i j lcm hj then
      dbg_trace s!"lcm is {lcm} for {ltf.monomial} and {ltg.monomial}"
      -- The LCM is always divisible by the leading terms
      let qf := MTerm.div! lcm ltf
      let qg := MTerm.div! lcm ltg

      dbg_trace s!"sPoly f hist has {qf} ({qf.monomial} {qf.monomial.size} {qf.coeff}) and {f}"
      dbg_trace s!"sPoly g hist has {qg} and {g}"

      let left := qf * f
      let leftHist := .termMul qf fHist

      let right := qg * g
      let rightHist := .termMul qg gHist

      let sp := Poly.sub (qf * f) (qg * g) cmp
      let hist := leftHist - rightHist

      dbg_trace s!"Combined history is {hist}"

      some <| HPoly.mk sp hist
    else
      none

partial def divPolysUpTo (p : HPoly) (ps : Array HPoly) (n : Nat) (hn : n ≤ ps.size)
    (cmp : MOrder := Monomial.grevlexOrder) : (Array HPoly × HPoly) :=
  let ⟨pp, pHist⟩ := p
  let rec loop (p : Poly) (r : Poly) (qs : Array HPoly)
      (hqs : qs.size = ps.size) : (Array HPoly × HPoly) :=
    if p = 0 then
      -- Construct the history for the remainder
      --    p = q * (basis) + rem  <===>  rem = p - q * (basis)
      let folded := qs.foldl (init := 0) (fun hist ⟨_, qHist⟩ => hist + qHist)
      let subHist := pHist - folded
      (qs, HPoly.mk r subHist)
    else
    let ltp := p.leadingTerm

    let rec innerLoop (i : Nat) :=
      if hi : i < n then
        -- Assume that none of the `ps` are the zero polynomial
        let ⟨pi, piHist⟩ := ps[i]
        let lti := pi.leadingTerm
        match ltp.div? lti with
        | none => innerLoop (i + 1)
        | some qt =>
          dbg_trace s!"Got a leading term division for {pi} and {p}"
          -- Calculate the "quotient part" we subtract from `p`
          let qt_mul_pi := qt * pi
          let qt_mul_pi_hist := .termMul qt piHist

          -- Add the "multiple" part of the quotient to `qs[i]`
          let ⟨qi, qiHist⟩ := qs[i]
          let qi_add_qt := Poly.add qi qt cmp
          let qi_add_qt_hist := qiHist + qt_mul_pi_hist
          let qs' := qs.set i (HPoly.mk qi_add_qt qi_add_qt_hist)
          let p' := Poly.sub p qt_mul_pi
          loop p' r qs' (by simp [qs', hqs])
      else
        -- No division was found, subtract and return
        let r' := Poly.add r ltp cmp
        let p' := Poly.sub p ltp cmp
        loop p' r' qs hqs

    innerLoop 0

  let qs := Array.mkArray ps.size (HPoly.mk 0 0)
  have hqs : qs.size = ps.size := by
    simp only [Array.size_mkArray, qs]
  loop pp 0 qs hqs

/--
  Divides polynomial `p` by the list `ps`.

  During division, we construct an array of `HPoly`s, but instead of
  pairing the quotients with their histories, the histories instead
  represent `qi * ps[i]`, and is built as the division continues.

  At the end, the remainder's history is constructed by subtracting
  `p`'s history from the sum of quotient histories. This eliminates
  the need of doing polynomial multiplication.
-/
partial def divPolys (p : HPoly) (ps : Array HPoly)
    (cmp : MOrder := Monomial.grevlexOrder) : (Array HPoly × HPoly) :=
  divPolysUpTo p ps ps.size (Nat.le_refl _) cmp

-- Minimize the basis, but keep the history of new derived polynomials
def minimizeBasis (ps : Array HPoly) : Array HPoly :=
  let rec loop (i : Nat) (minBasis : Array HPoly) : Array HPoly :=
    if hi : i < ps.size then
      let ⟨pi, piHist⟩ := ps[i]
      let lti := pi.leadingTerm

      -- Returns if we should include pi in the basis
      let rec innerLoop (j : Nat) : Bool :=
        if hj : j < ps.size then
          if i = j then innerLoop (i + 1) else
          let ⟨pj, pjHist⟩ := ps[j]
          let ltj := pj.leadingTerm
          -- If pi is divisible by pj, then we can safely drop it
          match lti.div? ltj with
          | none => innerLoop (j + 1)
          | some q => false
        else true

      if innerLoop i then loop (i + 1) (minBasis.push ⟨pi, piHist⟩)
      else                loop (i + 1) minBasis
    else
      minBasis

  loop 0 #[]

partial def buchbergers (ps : Array Poly) (cmp : MOrder := Monomial.grevlexOrder) : Array HPoly :=
  -- Transform polynomials into history annotated ones
  let hPolys : Array HPoly := ps.mapIdx (λ i p => HPoly.mk p (.basis i)) |>.map normalize

  let rec loop (i j checked len : Nat) (hij : i < j) (basis : Array HPoly) (h_len : len ≤ basis.size) :=
    if hi : i < len then
      if hj : j < len then
        match sPoly basis i j (by omega) (by omega) cmp with
        | none => loop i (j + 1) checked len (by omega) basis h_len
        | some ⟨s, sHist⟩ =>
          dbg_trace s!"div-ing (hpoly) {s} {sHist}"
          match divPolysUpTo ⟨s, sHist⟩ basis len h_len cmp with
          | (qs, ⟨rem, remHist⟩) =>
            if rem ≠ 0 then
              let remNormalized := normalize ⟨rem, remHist⟩
              loop i (j + 1) checked len (by omega) (basis.push remNormalized)
                (by simp [Array.size_push]; exact Nat.le_succ_of_le h_len)
            else
              loop i (j + 1) checked len (by omega) basis h_len
      else
        let i' := i + 1
        let j' := max (i' + 1) checked
        loop i' j' checked len (by omega) basis h_len
    else
      if h_len' : len ≥ basis.size then
        basis
      else
        let checked' := len
        let i' := 0
        let j' := max (i' + 1) checked'
        let len' := basis.size
        loop i' j' checked' len' (by omega) basis (Nat.le_refl _)

  let basisRes := loop 0 1 0 0 (by omega) hPolys (Nat.zero_le _)
  minimizeBasis basisRes

def constructWitness (n : Nat) (h : PolyHistory) (cmp : MOrder) : Array Poly :=
  let zeros : Array Poly := Array.mkArray n 0
  have h_zeros : zeros.size = n := by
    simp only [Array.size_mkArray, zeros]
  let one : Poly := #[MTerm.mk 1 0]

  let rec loop : PolyHistory → ({ arr : Array Poly // arr.size = n })
    | .zero => ⟨zeros, h_zeros⟩

    | .basis i =>
      if hi : i < n then
        let w := zeros.set i one
        ⟨w, by simp [w, h_zeros]⟩
      else
        dbg_trace s!"panic! {n} {i}"
        ⟨zeros, h_zeros⟩

    | .scalarMul c h =>
      match loop h with
      | ⟨w, hw⟩ =>
        let t : MTerm := MTerm.mk c 0
        let w' : Array Poly := w.map (λ p => t * p)
        ⟨w', by simp [w']; exact hw⟩

    | .termMul t h =>
      match loop h with
      | ⟨w, hw⟩ =>
        let w' : Array Poly := w.map (λ p => t * p)
        ⟨w', by simp [w']; exact hw⟩

    | .addHist h₁ h₂ =>
      let ⟨w₁, hw₁⟩ := loop h₁
      let ⟨w₂, hw₂⟩ := loop h₂
      let w := w₁.zipWith (Poly.add · · cmp) w₂
      ⟨w, by simp [w, hw₁, hw₂]⟩

    | .subHist h₁ h₂ =>
      let ⟨w₁, hw₁⟩ := loop h₁
      let ⟨w₂, hw₂⟩ := loop h₂
      let w := w₁.zipWith (Poly.sub · · cmp) w₂
      ⟨w, by simp [w, hw₁, hw₂]⟩

  loop h


/--
  Returns `some qs`, where `qs` are a "linear" combination of the starting
  basis polynomials `ps` that, when added together, equal `p`.

  Computes the ideal from Buchberger's algorithm.
-/
partial def idealMembership (p : Poly) (ps : Array Poly)
    (cmp : MOrder := Monomial.grevlexOrder) : Option (Array Poly) :=
  dbg_trace s!"Received poly {p} and basis {ps}"
  let n := ps.size
  let basis := buchbergers ps
  let printStr := basis.foldl (init := "[\n") (λ str hp => str ++ s!" {hp},\n")
  dbg_trace s!"returned basis: {printStr}]"
  let (_, ⟨rem, remHist⟩) := divPolys (HPoly.mk p (.basis n)) basis cmp
  if rem.size = 0 then
    match remHist with
    | .subHist h₁ h₂ =>
      match h₁ with
      | .basis n =>
        -- Calculate the Array witness in terms of the basis,
        -- which are themselves historied in terms of the original basis polynomials
        dbg_trace s!"Rem is zero, history is {h₂}"
        some <| constructWitness n h₂ cmp
      | _ => panic! "LHS of sub isn't right"
    | _ => panic! "Shape of history is wrong for rem of 0"
  else
    none

end HPoly

--Received poly x4 and basis #[-x2 * x3 + x1, -x1 * x5 + x4, x2]

def p₁ : Poly := #[MTerm.mk (-1) #[0, 1, 1], MTerm.mk 1 #[1]]
def p₂ : Poly := #[MTerm.mk (-1) #[1, 0, 0, 0, 1], MTerm.mk 1 #[0, 0, 0, 1]]
def p₃ : Poly := #[MTerm.mk 1 #[0, 1]]

def p : Poly := #[MTerm.mk 1 #[0, 0, 0, 1]]

--#eval HPoly.idealMembership p #[p₁, p₂, p₃]

end VerusLean.Tactic.Modular
