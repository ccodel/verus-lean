/-

`modular`: A tactic to discharge goals about modular arithmetic.

Authors: Cayden Codel

-/

import Init.Data.Int.Basic
import Std.Data.HashMap

import Qq

import Lean.Expr
import Lean.Meta.Canonicalizer
import Lean.Elab.Tactic
import Lean.Meta.Tactic.Rewrite

import Init.Omega.Logic
import VerusLean.Tactic.Modular.Core

import VerusLean.Tactic.Modular.Poly
import VerusLean.Tactic.Modular.Poly.Eval
import VerusLean.Upstream.Batteries.Rat

-- See the following import statement for the `omega` tactic's implementation
--import Lean.Elab.Tactic.Omega

namespace VerusLean.Tactic.Modular

open Lean Meta Tactic Std Lean.Omega
open Qq

namespace Rat

/-
instance : ToExpr (Fin n) where
  toTypeExpr := .app (mkConst ``Fin) (toExpr n)
  toExpr a :=
    let r := mkRawNatLit a.val
    mkApp3 (.const ``OfNat.ofNat [0]) (.app (mkConst ``Fin) (toExpr n)) r
      (mkApp3 (.const ``Fin.instOfNat []) (toExpr n)
        (.app (.const ``Nat.instNeZeroSucc []) (mkNatLit (n-1))) r)

instance : ToExpr Int where
  toTypeExpr := .const ``Int []
  toExpr i := if 0 ≤ i then
    mkNat i.toNat
  else
    mkApp3 (.const ``Neg.neg [0]) (.const ``Int []) (.const ``Int.instNegInt [])
      (mkNat (-i).toNat)
where
  mkNat (n : Nat) : Expr :=
    let r := mkRawNatLit n
    mkApp3 (.const ``OfNat.ofNat [0]) (.const ``Int []) r
        (.app (.const ``instOfNat []) r) -/

def toExpr (r : ℚ) : Q(ℚ) :=
  match r with
  | ⟨n, d, _, _⟩ =>
    let n : Q(ℤ) := q($n)
    let d : Q(ℕ) := q($d)
    mkApp2 (.const ``mkRat []) n d

def toTypeExpr : Q(Type) :=
  q(Rat)

instance instToExpr : ToExpr Rat := ⟨toExpr, toTypeExpr⟩

end Rat

-- Some necessary theorems

theorem Int.exists_of_dvd {a b : Int} : a ∣ b → ∃ c, b = a * c := id
theorem Int.dvd_of_exists {a b : Int} : (∃ c, b = a * c) → (a ∣ b) := id

private theorem neg_congr {R : Type u} [CommRing R] {a b : R} (h : a = b) : -a = -b := by
  rw [h]

private theorem binop_congr {R : Type u} [CommRing R] {a b c d : R} (h₁ : a = b) (h₂ : c = d) (op : R → R → R)
    : op a c = op b d := by
  rw [h₁, h₂]

private theorem add_congr {R : Type u} [CommRing R] {a b c d : R} (h₁ : a = b) (h₂ : c = d)
    : a + c = b + d :=
  binop_congr h₁ h₂ (· + ·)

private theorem sub_congr {R : Type u} [CommRing R] {a b c d : R} (h₁ : a = b) (h₂ : c = d)
    : a - c = b - d :=
  binop_congr h₁ h₂ (· - ·)

private theorem mul_congr {R : Type u} [CommRing R] {a b c d : R} (h₁ : a = b) (h₂ : c = d)
    : a * c = b * d :=
  binop_congr h₁ h₂ (· * ·)


namespace Monomial

/--
  Casts a monomial into a single `Expr`.
-/
def toExpr (m : Monomial) : Q(Monomial) :=
  q($m)

def toTypeExpr : Q(Type) :=
  q(Monomial)

instance instToExpr : ToExpr Monomial := ⟨toExpr, toTypeExpr⟩

end Monomial

namespace MTerm

variable {F : Type u} [Field F] [DecidableEq F]

def toExprM [instToExpr : ToExpr F] (t : M[F]) : MetaM Expr :=
  let ⟨c, m⟩ := t
  mkAppM ``MTerm.mk #[instToExpr.toExpr c, m.toExpr]

--def toTypeExpr : Expr :=
--  .const ``MTerm []

end MTerm

namespace Poly

variable {F : Type u} [Field F] [DecidableEq F]

def toExprM [instToExpr : ToExpr F] (p : P[F]) : MetaM Expr := do
  let exprs ← p.mapM MTerm.toExprM
  mkArrayLit (instToExpr.toTypeExpr) exprs.toList

-- TODO: Refactor to include `R` later
--def toTypeExpr : Expr :=
--  .const ``Poly []

end Poly

--------------------------------------------------------------------------------


open Lean Meta

structure GBConfig where
  splitDisjunctions : Bool := true

structure GBState (F : Type) [Field F] [DecidableEq F] [ToExpr F] where
  -- Field coefficient type (as an `Expr`)
  -- v : Level := 0
  -- F : Q(Type v) := q(ℚ)   -- But this fails
  -- F : Q(Type) := q(ℚ)

  -- Expressions to variable numbers
  -- Really of type `Std.HashMap Q($F) Nat`, but I can't get the hashing to work right
  atoms : Std.HashMap Expr Nat := {}
  atomsInOrder : Array Expr := #[]

  -- CC: Ideally we would say `Array Q(Poly $F)`, but this requires
  --     a field to be inferred. Perhaps require a field only for ops?

  polys : Array P[F] := #[]
  polyProofs : Array Expr := #[]

  -- These are the expressions associated with the polynomial representations
  -- in `polys`. They are added in a one-to-one correspondence.
  -- In other `polyExprs` holds the hypotheses that are represented as polys
  polyExprs : Array Expr := #[]

abbrev GBM' (F : Type) [Field F] [DecidableEq F] [ToExpr F] :=
  StateRefT (GBState F) (ReaderT GBConfig CanonM)

-- Maps to a pair `(p, prf)` where `p` is an `Expr` of type `Poly F` for
-- the field `F` in the state
def Cache (F : outParam Type) [Field F] [DecidableEq F] [ToExpr F] : Type :=
  Std.HashMap Expr (P[F] × GBM' F Expr)

abbrev GBM (F : outParam Type) [Field F] [DecidableEq F] [ToExpr F] :=
  StateRefT (Cache F) (GBM' F)

def GBM.run {F : Type} [Field F] [DecidableEq F] [ToExpr F]
    (m : GBM F α) (st : GBState F := {}) (cfg : GBConfig) : MetaM α :=
  m.run' Std.HashMap.empty |>.run' st cfg |>.run'

--abbrev GBProof (F : outParam Type) [Field F] [DecidableEq F] [ToExpr F] : Type :=
--  GBM F Expr

structure Problem where
  --assumptions : Array GBProof := ∅
  --numVars : Nat := 0
  equalities : Std.HashSet Nat := ∅

structure MetaProblem where
  problem : Problem := {}
  /-- Pending facts to process -/
  facts : List Expr := []
  /-- Pending disjunctions. We case split these later. -/
  disjunctions : List Expr := []
  /-- Processed facts. We keep these to avoid duplicates. -/
  processedFacts : Std.HashSet Expr := ∅

def MetaProblem.trivial : MetaProblem :=
  { problem := {} }

instance : Inhabited MetaProblem := ⟨MetaProblem.trivial⟩

variable {F : outParam Type} [Field F] [DecidableEq F] [ToExpr F]

def cfg : GBM F GBConfig :=
  read

def fieldTypeExpr : GBM F Q(Type) := do
  return toTypeExpr F

def atoms : GBM F (Array Expr) := do
  return (← getThe (GBState F)).atomsInOrder

def getNumAtoms : GBM F Nat := do
  return (← getThe (GBState F)).atomsInOrder.size

def getPolys : GBM F (Array P[F]) := do
  return (← getThe (GBState F)).polys

def getPolyExprs : GBM F (Array Expr) := do
  return (← getThe (GBState F)).polyExprs

def getNumPolys : GBM F Nat := do
  return (← getPolys).size

def addPoly (p : P[F]) (proof e : Expr) : GBM F Unit := do
  modifyThe (GBState F) (fun s => { s with
    polys := s.polys.push p
    polyProofs := s.polyProofs.push proof
    polyExprs := s.polyExprs.push e
  })

def atomsAsArrayLitExpr : GBM F Expr := do
  mkArrayLit (← fieldTypeExpr) (← atoms).toList

-- CC: Defined in `OmegaM.lean`. What is the point of this?
/-- Construct the term with type hint `(Eq.refl a : a = b)`-/
def mkEqReflWithExpectedType (a b : Expr) : MetaM Expr := do
  mkExpectedTypeHint (← mkEqRefl a) (← mkEq a b)

def reconstructProof (proof : GBM F Expr) (e : Expr) : GBM F Expr := do
  mkEqTrans (← mkEqSymm (← proof)) e

/--
  For a given expression `e`, consults the atoms in the `GBState` to see if
  we have already encountered `e`. If so, return its index.
-/
def lookup (e : Expr) : GBM F Nat := do
  let c ← getThe (GBState F)
  let e ← canon e
  --let F : Q(Type) ← fieldType
  --have e : Q($F) := e
  match c.atoms[e]? with
  | some i => return i
  | none =>
    trace[gb] s!"New atom: {e}"
    let i ← modifyGetThe (GBState F) fun c =>
      let cs := c.atoms.size
      (cs, { c with
        atoms := c.atoms.insert e cs
        atomsInOrder := c.atomsInOrder.push e
      })
    return i

/-def nameInField (constName : Name) (exprs : Array Expr) : GBM F Expr := do
  mkAppM constName exprs -/

def oneAsExpr : GBM F Expr := do
  let F : Q(Type) ← fieldTypeExpr
  let _ ← synthInstanceQ q(One $F)
  return q((1 : $F))

def mtermExpr (m : Q(Monomial)) : GBM F Expr := do
  let one ← oneAsExpr
  mkAppM ``MTerm.mk #[one, m]

def asGet!Expr (atoms i : Expr) : GBM F Expr := do
  mkAppM ``Array.get! #[atoms, i]

def asGetDExpr (atoms i v : Expr) : GBM F Expr := do
  mkAppM ``Array.getD #[atoms, i, v]

def mkEvalAtomEq (e : Expr) (i : Nat) : GBM F Expr := do
  let atoms ← atomsAsArrayLitExpr
  let i := toExpr i
  -- CC: Why do we need a refl proof to start, and then a trans eq proof?
  --     Can't we construct the proof directly?
  -- TODO: The types of `get` and `get!` don't agree

  -- A proof that `e = atoms.getD i 1`,
  -- tagged with the LHS/RHS type under `e` (which should belong to the ring)
  let eq₁ ← mkEqReflWithExpectedType e (← asGetDExpr atoms i (← oneAsExpr))

  -- A proof that `atoms.getD i 1 = Poly.eval ↑(eᵢ i) atoms`
  let eq₂ ← mkEqSymm <| ← mkAppM ``Poly.eval_eᵢ #[i, atoms]

  -- Returns a proof that `e = Poly.eval ↑(eᵢ i) atoms`
  mkEqTrans eq₁ eq₂

-- Returns a pair `(p, prf)` where `p` is an expression containing a `Poly F`
-- in some field, and `prf` is a proof that `e = p.eval atoms`
def mkVarAtom (e : Expr) : GBM F (P[F] × GBM F Expr) := do
  -- Index of atom
  let i : ℕ ← lookup e
  let m := Monomial.eᵢ i
  return (Poly.ofMonomial m, mkEvalAtomEq e i)

def ord {α : Type u} (cmp : α → α → Ordering) : α → α → Bool := fun a b =>
  match cmp a b with
  | .gt => true
  | _ => false

@[inline, always_inline]
def constructEqTransProof (e : Expr) (name : Name) (proof : GBM F Expr) : GBM F Expr := do
   mkEqTrans
    (← mkAppM name #[← proof])
    (← mkEqSymm e)

@[inline, always_inline]
def constructEqTransProof₂ (e : Expr) (name : Name) (proof₁ proof₂ : GBM F Expr) : GBM F Expr := do
  mkEqTrans
    (← mkAppM name #[← proof₁, ← proof₂])
    (← mkEqSymm e)

@[inline]
def binop_proof (opStr : String) (p₁ p₂ : P[F]) (proof₁ proof₂ : GBM F Expr) : GBM F (GBM F Expr) := do
  -- let op_name : Name := .str ``Poly opStr
  let eval_name : Name := .str ``Poly s!"eval_{opStr}"
  let congr_name : Name := .str .anonymous s!"{opStr}_congr"
  let eval_expr ← mkAppM eval_name #[← p₁.toExprM, ← p₂.toExprM, ← atomsAsArrayLitExpr]
  return constructEqTransProof₂ eval_expr congr_name proof₁ proof₂

mutual

/-

Transform a base expression, from the LHS of `(lhs : Int) = 0`,
into a polynomial.

-/

-- Returns the expression as a polynomial, tagged with its proof
partial def asPoly (e : Expr) : GBM F (P[F] × GBM F Expr) := do
  let cache ← get
  match cache.get? e with
  | some ⟨poly, proof⟩ =>
    trace[gb] s!"Found in cache: {e}"
    return (poly, proof)
  | none =>
    let ⟨poly, proof⟩ ← asPolyImpl e
    modifyThe (Cache F) fun cache => ( cache.insert e (poly, proof.run' cache) )
    return (poly, proof)

partial def asPolyImpl (e : Expr) : GBM F (P[F] × GBM F Expr) := do
  --trace[gb] s!"processing {e}"
  -- `omega` uses `groundInt?` here to shuffle casts and ops around
  if e.isFVar then
    if let some v ← e.fvarId!.getValue? then
      asPoly v
    else
      mkVarAtom e
  else
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, e₁, e₂]) =>
    let (p₁, proof₁) ← asPoly e₁
    let (p₂, proof₂) ← asPoly e₂
    let proof ← binop_proof "add" p₁ p₂ proof₁ proof₂
    return (p₁ + p₂, proof)
  | (``HSub.hSub, #[_, _, _, _, e₁, e₂]) =>
    let (p₁, proof₁) ← asPoly e₁
    let (p₂, proof₂) ← asPoly e₂
    let proof ← binop_proof "sub" p₁ p₂ proof₁ proof₂
    return (p₁ - p₂, proof)
  | (``Neg.neg, #[_, _, e']) =>
    let (p, proof) ← asPoly e'
    let proof : GBM F Expr := do
      let eval_neg ←
        mkAppM ``Poly.eval_neg #[← p.toExprM, ← atomsAsArrayLitExpr]
      constructEqTransProof eval_neg ``neg_congr proof
    return (-p, proof)
  | (``HMul.hMul, #[_, _, _, _, e₁, e₂]) =>
    let (p₁, proof₁) ← asPoly e₁
    let (p₂, proof₂) ← asPoly e₂
    let proof ← binop_proof "mul" p₁ p₂ proof₁ proof₂
    return (p₁ * p₂, proof)
  -- Ignore division for now
  -- | (``HDiv.hDiv, #[_, _, _, _, x, y]) => do
  -- Ignore mod fow now
  /-| (``HPow.hPow, #[_, _, _, _, b, exp]) =>
    -- We expect the power to be a `Nat`
    match exp.getAppFnArgs with
    | (``Nat.zero, #[]) => return Poly.one
    | (``Nat.succ, #[n]) =>
      match n.nat? with
      | none => mkVarAtom e
      | some n =>
        -- We won't expand the power, so whatever is inside better be an atom
        let (p, proof) ← mkVarAtom b
        return Monomial.scPow monomial (n + 1)
    | _ => mkVarAtom e -/
  | _ => mkVarAtom e


end /- mutual for `{asPoly, asPolyImpl}` -/

/-def rewrite (lhs rw : Expr) : MetaM (Option Expr) := do
  trace[gb] "rewriting {lhs} via {rw} : {← inferType rw}"
  match (← inferType rw).eq? with
  | some (_, lhs, rhs) => -/

--def processEquality () : MetaM Unit := do

-- Perhaps have a set of constraints based on the types of things?
-- e.g. `Nat` can't have negative values?

def addEquality (e lhs : Expr) : GBM F Unit := do
  let (poly, proof) ← asPoly lhs

  -- Reconstruct proof that `e` can be represented as a `Poly`
  let proof ← reconstructProof proof e

  trace[gb] "Adding poly for {e}"
  addPoly poly proof e

/-- Given a fact `e` with type `¬P`, return a more useful fact by pushing the negation. -/
def pushNot (e P : Expr) : MetaM (Option Expr) := do
  let P ← whnfR P
  trace[gb] s!"pushing negation: {P}"
  match P with
  | .forallE _ t b _ => return none
  | .app _ _ =>
    match_expr P with
    | Not P =>
      return some (mkApp3 (.const ``Decidable.of_not_not []) P
        (.app (.const ``Classical.propDecidable []) P) e)
    | And P Q =>
      return some (mkApp5 (.const ``Decidable.or_not_not_of_not_and []) P Q
        (.app (.const ``Classical.propDecidable []) P)
        (.app (.const ``Classical.propDecidable []) Q) e)
    | Or P Q =>
      return some (mkApp3 (.const ``and_not_not_of_not_or []) P Q e)
    | Iff P Q =>
      return some (mkApp5 (.const ``Decidable.and_not_or_not_and_of_not_iff []) P Q
        (.app (.const ``Classical.propDecidable []) P)
        (.app (.const ``Classical.propDecidable []) Q) e)
    | _ => return none
  | _ => return none

mutual

partial def processFact (p : MetaProblem) (e : Expr) : GBM F MetaProblem := do
  let t ← instantiateMVars (← whnfR (← inferType e))
  trace[gb] "adding fact: {t}"
  match t with
  | .app _ _ =>
    match_expr t with
    | Eq α x y =>
      match_expr α with
      | Int =>
        match y.int? with
        | some 0 => addEquality e x; return p
        | _ => processFact p (mkApp3 (.const ``Int.sub_eq_zero_of_eq []) x y e)
      | _ => return p
    /-  Replace `(a | b)` with `∃ c, b = a * c`  -/
    | Dvd.dvd α _ a b =>
      match_expr α with
      --| Int => processFact p (mkApp2 (.const ``Int.dvd_def []) s t)
      | Int => processFact p (mkApp3 (.const ``Int.exists_of_dvd []) a b e)
      | _ => return p
    /-  Split products into pieces and recurse on each  -/
    | And t₁ t₂ => do
      let p₁ ← processFact p (mkApp3 (.const ``And.left []) t₁ t₂ e)
      processFact p₁ (mkApp3 (.const ``And.right []) t₁ t₂ e)
    /-  Split existentials and recurse on their property  -/
    | Exists α P =>
      processFact p (mkApp3 (.const ``Exists.choose_spec [← getLevel α]) α P e)
    /-  Split subtypes and recurse on their property  -/
    | Subtype α P =>
      processFact p (mkApp3 (.const ``Subtype.property [← getLevel α]) α P e)
    | Or _ _ =>
      if (← cfg).splitDisjunctions then
        return { p with disjunctions := p.disjunctions.insert e}
      else
        return p
    | _ =>
      trace[gb] "Application has no matching rule: {t}"
      return p
  | _ =>
    trace[gb] "Expression has no matching rule: {t}"
    return p


end /- mutual for `{processFact}` -/

partial def processFacts (p : MetaProblem) : GBM F (GBState F) := do
  match p.facts with
  | [] =>
    trace[gb] "processed {(← getThe (GBState F)).polys.size} polys"
    getThe (GBState F)
  | e :: es =>
    if p.processedFacts.contains e then
      processFacts { p with facts := es }
    else
      let p ← processFact (e := e) { p with
        facts := es
        processedFacts := p.processedFacts.insert e }
      processFacts p

partial def processGoalFact (e : Expr) : GBM F (Option (P[F] × Array P[F] × Array Expr)) := do
  let t ← instantiateMVars (← whnfR (← inferType e))
  trace[gb] "adding goal fact: {t}"
  match t with
  | .forallE _ x fx _ =>
    trace[gb] "FORALLE {x}, {fx}"
    return none
    --processGoalFact fx
  | .lam _ x fx _ =>
    trace[gb] "LAM {x}, {fx}"
    processGoalFact fx
  | .app _ _ =>
    match_expr t with
    | Eq α x y =>
      match_expr α with
      | Int =>
        -- Assume the existential variable is on the RHS
        match y.getAppFnArgs with
        | (``HMul.hMul, #[_, _, _, _, e₁, e₂]) =>
          -- Assume that `e₂` has the existential variable
          let (xpoly, xproof) ← asPoly x
          let (ypoly, yproof) ← asPoly e₁
          addPoly ypoly (← yproof) e
          return some (xpoly, ← getPolys, ← getPolyExprs)
        | _ => return none
      | _ => return none
    /-  Replace `(a | b)` with `∃ c, b = a * c`  -/
    | Dvd.dvd α _ a b =>
      match_expr α with
      --| Int => processFact p (mkApp2 (.const ``Int.dvd_def []) s t)
      | Int => processGoalFact (mkApp3 (.const ``Int.exists_of_dvd []) a b e)
      | _ => return none
    | Exists α P =>
      -- We extract the multiplier on the existentially quantified variable
      -- TODO: Rearrange LHS and RHS so the ∃ var is on the RHS and is a multiple(?)
      -- Fow now, assume correct sides
      trace[gb] "{P}"
      processGoalFact (mkApp3 (.const ``Exists.choose_spec [← getLevel α]) α P e)
      --return none
    | _ => return none
  | _ => return none

partial def processGoal (g : MVarId) : MetaM MVarId := do
  let e ← whnfR (.mvar g)
  let t ← instantiateMVars (← whnfR (← inferType e))
  trace[gb] "processing goal mvarid {t}"
  match t with
  | .app _ _ =>
    match_expr t with
    | Dvd.dvd α _ s t =>
      match_expr α with
      | Int =>
        -- Apply `Int.exists_of_dvd`
        match ← g.apply (mkApp2 (.const ``Int.dvd_of_exists []) s t) with
        | [g] => processGoal g
        | _ =>
          trace[gb] "Apply failed!"
          return g
      | _ => return g
    | Exists α P => return g
      -- We extract the multiplier on the existentially quantified variable
      -- TODO: Rearrange LHS and RHS so the ∃ var is on the RHS and is a multiple(?)
      -- Fow now, assume correct sides
      --trace[gb] "{P}"
      --processGoalFact (mkApp3 (.const ``Exists.choose_spec [← getLevel α]) α P e)
    | _ => return g
  | _ => return g


theorem Int.mul_left_eq_zero_of_eq_zero {a : Int} : a = 0 → ∀ (b : Int), b * a = 0 := by
  rintro rfl b
  rw [Int.mul_zero]

def inferFieldFromProcessedGoal (g : MVarId) : MetaM Q(Type) := do
  let e ← whnfR (.mvar g)
  let t ← instantiateMVars (← whnfR (← inferType e))
  match t with
  | .app _ _ =>
    match_expr t with
    | Exists α P =>
      match_expr α with
      | Nat => return q(ℚ)
      | Int => return q(ℚ)
      | _ =>
        -- Try to infer a field instance
        let inst ← synthInstance q(Field $α)
    | _ => return Int
  | _ => return Int



-- Assume `exprs` is an array of expressions of the form `a = 0`.
/-def constructProof (exprs : Array Expr) : PolyHistory → MetaM Expr
  | .zero => mkEqRefl (mkApp (.const ``Int.ofNat []) (.const ``Nat.zero []))
  | .basis i => return exprs.get! i
  | .scalarMul c h => do
    let proof ← constructProof exprs h
    match_expr proof with
    | Eq _ x _ =>
      return mkApp4 (.const ``Int.mul_left_eq_zero_of_eq_zero []) proof x proof (RattoExpr c)
    | _ => return exprs.get! 0
  | .termMul t h => do
    let proof ← constructProof exprs h
    return proof
    --mkEqRefl (mkApp3 (.const ``Int.mul []) (mkApp (.const ``Int.ofNat []) c) prf)
  | _ => return exprs.get! 0
-/
--def prfOf (h : PolyHistory F) (exprs : Array Expr) : Expr := exprs.get! 0

open Elab Tactic

syntax (name := gbSyn) "gb" : tactic


def gbImpl (facts : List Expr) (g : MVarId) : MetaM Unit := do
  trace[gb] "facts: {facts}"
  let st ← GBM.run (processFacts { facts }) (cfg := {})
  trace[gb] "---------------"
  let g ← processGoal g
  let goalExpr ← whnfR (.mvar g)
  match ← GBM.run (@processGoalFact goalExpr) st {} with
  | none => throwError "Goal is not a valid modular arithmetic goal."
    --trace[gb] "Goal is not a valid modular arithmetic goal."
    --return ()
  | some (poly, polys, exprs) => do
    trace[gb] "derived polys: {polys}"
    trace[gb] "derived goal poly: {poly}"
    trace[gb] "derived exprs: {exprs}"
    match HPoly.idealMembership poly polys with
    | none => throwError "Groebner basis membership test failed."
      --trace[gb] "Groebner basis membership test failed."
    | some w =>
      trace[gb] "{w}"
      return ()

def gbTactic : TacticM Unit := do
  --liftMetaTactic fun g => do
  liftMetaFinishingTactic fun g => do
    g.withContext do
      let hyps := (← getLocalHyps).toList
      trace[gb] "analyzing {hyps.length} hypotheses:\n{← hyps.mapM inferType}"
      let _ ← gbImpl hyps g
      return ()

@[builtin_tactic VerusLean.Tactic.Modular.gbSyn]
def evalGB : Tactic := fun
  | `(tactic| gb) => do
    gbTactic
  | _ => throwUnsupportedSyntax

elab "gb" : tactic => gbTactic
-- CC: Place in different file?

set_option trace.omega true
set_option trace.gb true

theorem omegaTest : ∀ (a b c : ℤ), a < b → b < c → a < c := by
  omega
  done

theorem test : ∀ (a b c : ℤ), a ∣ b → b ∣ c → a ∣ c := by
  intro a b c ha hb
  gb
  done
