/-

`modular`: A tactic to discharge goals about modular arithmetic.

Authors: Cayden Codel

-/

import Init.Data.Int.Basic
import Std.Internal.Rat
import Std.Data.HashMap

import Lean.Expr
import Lean.Meta.Canonicalizer
import Lean.Elab.Tactic
import Lean.Meta.Tactic.Rewrite

import Init.Omega.Logic
import VerusLean.Tactic.Modular.Core

import VerusLean.Tactic.Modular.Poly

-- See the following import statement for the `omega` tactic's implementation
--import Lean.Elab.Tactic.Omega

namespace VerusLean.Tactic.Modular

open Lean Tactic Std Internal Lean.Omega

-- Some necessary theorems

theorem Int.exists_of_dvd {a b : Int} : a ∣ b → ∃ c, b = a * c := id
theorem Int.dvd_of_exists {a b : Int} : (∃ c, b = a * c) → (a ∣ b) := id


open Lean Meta

structure GBConfig where
  splitDisjunctions : Bool := true

structure GBState where
  -- Expressions to indexes into `polys`
  atoms : Std.HashMap Expr Nat := {}
  -- Expressions to variable numbers.
  vars : Std.HashMap Expr Nat := {}
  varsInOrder : Array Expr := #[]
  polys : Array Poly := #[]
  polyExprs : Array Expr := #[]

abbrev GBM' := StateRefT GBState (ReaderT GBConfig CanonM)

def Cache : Type := Std.HashMap Expr Poly

abbrev GBM := StateRefT Cache GBM'

def GBM.run (m : GBM α) (st : GBState := {}) (cfg : GBConfig) : MetaM α :=
  m.run' Std.HashMap.empty |>.run' st cfg |>.run'

abbrev GBProof : Type := GBM Expr

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

def cfg : GBM GBConfig := do pure (← read)

def atoms : GBM (Array Expr) := do
  return (← getThe GBState).atoms.toArray.qsort (·.2 < ·.2) |>.map (·.1)

def getPolys : GBM (Array Poly) := do
  return (← getThe GBState).polys

def getPolyExprs : GBM (Array Expr) := do
  return (← getThe GBState).polyExprs

def getNumPolys : GBM Nat := do
  return (← getPolys).size

def getNumVars : GBM Nat := do
  return (← getThe GBState).vars.size

def addPoly (p : Poly) (e : Expr) : GBM Unit := do
  modifyThe GBState (fun s => { s with
    polys := s.polys.push p
    polyExprs := s.polyExprs.push e
  })

/--
  For a given expression `e`, consults the atoms in the `GBState` to see if
  we have already encountered `e`. If so, return its index.
-/
def lookup (e : Expr) : GBM Nat := do
  let c ← getThe GBState
  let e ← canon e
  match c.atoms[e]? with
  | some i => return i
  | none =>
    trace[gb] s!"New atom: {e}"
    let i ← modifyGetThe GBState fun c =>
      let cs := c.atoms.size
      let m := Monomial.eᵢ cs
      (cs, { c with
        atoms := c.atoms.insert e cs
        polys := c.polys.push ↑m })
    return i

--def mkAtomPoly (e : Expr) : GBM (Poly × GBM Expr) := do
--  let n ← lookup e

def mkVarAtom (e : Expr) : GBM Monomial := do
  let c ← getThe GBState
  let e ← canon e
  match c.vars[e]? with
  | some i => return Monomial.eᵢ i
  | none =>
    trace[gb] s!"New var atom: {e}"
    let i ← modifyGetThe GBState fun c =>
      let cs := c.vars.size
      (cs, { c with
        vars := c.vars.insert e cs
        varsInOrder := c.varsInOrder.push e })
    return Monomial.eᵢ i

-- CC: Defined in `OmegaM.lean`. What is the point of this?
/-- Construct the term with type hint `(Eq.refl a : a = b)`-/
def mkEqReflWithExpectedType (a b : Expr) : MetaM Expr := do
  mkExpectedTypeHint (← mkEqRefl a) (← mkEq a b)

def ord {α : Type u} (cmp : α → α → Ordering) : α → α → Bool := fun a b =>
  match cmp a b with
  | .gt => true
  | _ => false

mutual

/-

Transform a base expression, from the LHS of `(lhs : Int) = 0`,
into a polynomial.

-/

-- Returns a `Nat` index into `polys`.
partial def asPoly (e : Expr) : GBM Poly := do
  let cache ← get
  match cache.get? e with
  | some poly =>
    trace[gb] s!"Found in cache: {e}"
    return poly
  | none =>
    let poly ← asPolyImpl e
    modifyThe Cache fun cache => ( cache.insert e poly )
    return poly

partial def asPolyImpl (e : Expr) : GBM Poly := do
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
    let p₁ ← asPoly e₁
    let p₂ ← asPoly e₂
    return p₁ + p₂
  | (``HSub.hSub, #[_, _, _, _, e₁, e₂]) =>
    let p₁ ← asPoly e₁
    let p₂ ← asPoly e₂
    return p₁ - p₂
  | (``Neg.neg, #[_, _, e']) =>
    let p ← asPoly e'
    return -p
  | (``HMul.hMul, #[_, _, _, _, e₁, e₂]) =>
    let p₁ ← asPoly e₁
    let p₂ ← asPoly e₂
    return p₁ * p₂
  -- Ignore division for now
  -- | (``HDiv.hDiv, #[_, _, _, _, x, y]) => do
  -- Ignore mod fow now
  | (``HPow.hPow, #[_, _, _, _, b, exp]) =>
    -- We expect the power to be a `Nat`
    match exp.getAppFnArgs with
    | (``Nat.zero, #[]) => return Poly.one
    | (``Nat.succ, #[n]) =>
      match n.nat? with
      | none => mkVarAtom e
      | some n =>
        -- We won't expand the power, so whatever is inside better be an atom
        let monomial ← mkVarAtom b
        return Monomial.scPow monomial (n + 1)
    | _ => mkVarAtom e
  | _ => mkVarAtom e


end /- mutual -/

/-def rewrite (lhs rw : Expr) : MetaM (Option Expr) := do
  trace[gb] "rewriting {lhs} via {rw} : {← inferType rw}"
  match (← inferType rw).eq? with
  | some (_, lhs, rhs) => -/

--def processEquality () : MetaM Unit := do

-- Perhaps have a set of constraints based on the types of things?
-- e.g. `Nat` can't have negative values?

def addEquality (e lhs : Expr) : GBM Unit := do
  -- TODO: Prevent adding the poly twice?
  let poly ← asPoly lhs
  trace[gb] "Adding poly {poly} for {e}"
  addPoly poly e

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

partial def processFact (p : MetaProblem) (e : Expr) : GBM MetaProblem := do
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


end /- mutual -/

partial def processFacts (p : MetaProblem) : GBM GBState := do
  match p.facts with
  | [] =>
    trace[gb] "processed polys: {(← getThe GBState).polys}"
    return (← getThe GBState)
  | e :: es =>
    if p.processedFacts.contains e then
      processFacts { p with facts := es }
    else
      let p ← processFact (e := e) { p with
        facts := es
        processedFacts := p.processedFacts.insert e }
      processFacts p

partial def processGoalFact (e : Expr) : GBM (Option (Poly × Array Poly × Array Expr)) := do
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
          let xP ← asPoly x
          let yP ← asPoly e₁
          addPoly yP e
          return some (xP, ← getPolys, ← getPolyExprs)
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

/-
  Constructs a new `Expr` from a LHS of an equation `P = 0`.

  `exprs` are all of the equation form.

-/
--def constructLinearCombination (p : Poly) (exprs : Array Expr) (vars : Array Expr) : MetaM Expr := do


open Elab Tactic

syntax (name := gbSyn) "gb" : tactic

set_option trace.gb true

def gbImpl (facts : List Expr) (g : MVarId) : MetaM Unit := do
  trace[gb] "facts: {facts}"
  let st ← GBM.run (processFacts { facts }) (cfg := {})
  trace[gb] "---------------"
  let g ← processGoal g
  let goalExpr ← whnfR (.mvar g)
  match ← GBM.run (processGoalFact goalExpr) st {} with
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

theorem omegaTest : ∀ (a b c : Int), a < b → b < c → a < c := by
  omega
  done

theorem test : ∀ (a b c : Int), a ∣ b → b ∣ c → a ∣ c := by
  intro a b c ha hb
  gb
  done
