import VerusLean.VLIR.Defs
import Lean.Elab

namespace VerusLean

open Lean Elab Command

def Ident.toSyntax (i : Ident) : TermElabM Lean.Ident :=
  return mkIdent (.mkSimple i)

def Idents.toSyntax (i : Idents) : TermElabM (Array Lean.Ident) :=
  i.mapM Ident.toSyntax

def Typ.toSyntax (ty : Typ) : TermElabM Term := do
  match ty with
  | .Bool => return mkIdent ``_root_.Bool
  | .Int => return mkIdent ``_root_.Int
  | .Nat => return mkIdent ``_root_.Nat
  | .UInt _ => return mkIdent ``_root_.UInt32
  | .SInt _ => `(BitVec 32)
  | .Char => return mkIdent ``_root_.Char
  | .StrSlice => throwError "StrSlice not supported"
  -- | .ConstInt _ => return mkIdent ``_root_.Int
  | .Array t => do
    let t ← t.toSyntax
    `(Array $t)

def Const.toSyntax (c : Const) : TermElabM Term := do
  match c with
  | Const.Bool b =>
    -- See Lean.Init.Meta, for Quote Bool and mkCIdent
    -- No way to take the boolean directly?
    match b with
    | true => return mkIdent ``true
    | false => return mkIdent ``false
  | Const.Int i => return Syntax.mkNumLit s!"{i}"
  | Const.StrSlice _ => return mkIdent ``StrSlice
  | Const.Char _ => return mkIdent ``Char

-- CC: TODO figure out how to return just the op?
def BitwiseOp.toSyntax (b : BitwiseOp) (lhs rhs : Term) : TermElabM Term := do
  match b with
  | .BitXor  => `($lhs ^^^ $rhs)
  | .BitAnd  => `($lhs &&& $rhs)
  | .BitOr   => `($lhs ||| $rhs)
  | .Shr _   => `($lhs >>> $rhs)
  | .Shl _ _ => `($lhs <<< $rhs)

def ArithOp.toSyntax (a : ArithOp) (lhs rhs : Term) : TermElabM Term := do
  match a with
  | .Add => `($lhs + $rhs)
  | .Sub => `($lhs - $rhs)
  | .Mul => `($lhs * $rhs)
  | .EuclideanDiv => `($lhs / $rhs)
  | .EuclideanMod => `($lhs % $rhs)

def InequalityOp.toSyntax (i : InequalityOp) (lhs rhs : Term) : TermElabM Term := do
  match i with
  | .Lt => `($lhs < $rhs)
  | .Le => `($lhs ≤ $rhs)
  | .Gt => `($lhs > $rhs)
  | .Ge => `($lhs ≥ $rhs)

def UnaryOp.toSyntax (u : UnaryOp) (e : Term) : TermElabM Term := do
  match u with
  | .Not => `(¬ ($e))
  | .BitNot _ => `(~~~ $e)
  | _ => throwError "unsupported unary op {repr u}"

def BinaryOp.toSyntax (b : BinaryOp) (lhs rhs : Term) : TermElabM Term := do
  match b with
  | .And => `($lhs ∧ $rhs)
  | .Or => `($lhs ∨ $rhs)
  | .Xor => `($lhs ^^ $rhs)
  | .Implies => `($lhs → $rhs)
  | .Eq _ => `($lhs = $rhs)
  | .Ne => `($lhs ≠ $rhs)
  | .Inequality ineq => ineq.toSyntax lhs rhs
  | .Arith arith _ => arith.toSyntax lhs rhs
  | .Bitwise bitwise _ => bitwise.toSyntax lhs rhs

mutual

partial def Bind.toSyntax (b : Bind) (t : Term) : TermElabM Term := do
  match b with
  | .Let ⟨v, e⟩ =>
    let v ← v.toSyntax
    let e ← e.toSyntax
    -- See `letMVar` in `Lean.Parser.Term.lean`
    `(let $v := $e; $t)
  | .Quant q vars =>
    match q with
    | .Forall =>
      let varsForall : TSyntaxArray `Lean.Parser.Term.bracketedBinder ←
        (vars.toArray.mapM (fun ⟨i, ty⟩ => do
          let i ← i.toSyntax
          let ty ← ty.toSyntax
          `(Lean.Parser.Term.bracketedBinderF| ($i : $ty))
        ))
      `(∀ $(varsForall):bracketedBinder*, $t)
    | .Exists =>
      match vars with
      | [] => throwError "empty exists"
      | ⟨vi, vty⟩ :: vs =>
        throwError "not yet implemented"
        /- let i ← vi.toSyntax
        let ty ← vty.toSyntax
        --let v : TSyntax `Lean.explicitBinder ← `(Lean.Parser.Term.bracketedBinderF| ($i : $ty))
        let varsExists : TSyntax `Lean.explicitBinders ←
          (
            vars.toArray.foldlM (init := v) (fun ⟨i, ty⟩ => do
              let i ← i.toSyntax
              let ty ← ty.toSyntax
              `(Lean.Parser.Term.bracketedBinderF| ($i : $ty))
            )
          )
        `(∃ $(varsExists), l = [1, 2, 3]) -/
  | .Lambda vars => throwError "unsupported bind {repr b}"
    /-let varsLambda : TSyntaxArray `Lean.Parser.Term.funBinder ←
      (vars.toArray.mapM (fun ⟨i, ty⟩ => do
        let i ← i.toSyntax
        let ty ← ty.toSyntax
        `(Lean.Parser.Term.bracketedBinderF| ($i : $ty))
      ))
    --  binders : TSyntaxArray `Lean.Parser.Term.funBinder
    `(λ $(varsLambda):bracketedBinder*, $t) -/

partial def Exp.toSyntax (e : Exp) : TermElabM Term := do
  match e with
  | .Const c => c.toSyntax
  | .Var ident => ident.toSyntax
  | .Unary op e =>
    let e ← e.toSyntax
    op.toSyntax e
  | .Binary op lhs rhs =>
    let lhs ← lhs.toSyntax
    let rhs ← rhs.toSyntax
    op.toSyntax lhs rhs
  | .If cond b₁ b₂ =>
    let cond ← cond.toSyntax
    let b₁ ← b₁.toSyntax
    let b₂ ← b₂.toSyntax
    `(if $cond then $b₁ else $b₂)
  | .Bind bind exp =>
    let exp ← exp.toSyntax
    bind.toSyntax exp
  | .Call fn _ exps =>
    let fn := ← match fn with
      | CallFun.Fun fn => fn.toSyntax
    -- let typs ← typs.mapM Typ.toSyntax
    let exps ← exps.mapM Exp.toSyntax
    let exps_TSepArray := exps.foldl Syntax.TSepArray.push (Syntax.TSepArray.mk #[] (sep := ","))
    dbg_trace s!"elab get here!! {fn}, {exps}"
    -- let termSyntaxList := exps.map (·.raw)
    `($fn ([$exps_TSepArray,*]))

  -- | .ArrayLiteral es =>
  --   let es ← es.mapM Exp.toSyntax
  --   `(#[ $es,* ])

end /- mutual -/

def Exps.toSyntax (e : Exps) : TermElabM (Array Term) := do
  e.mapM Exp.toSyntax

-- CC: Just use TSyntax `command?
def Decl.toSyntax (d : Decl) : CommandElabM (TSyntaxArray `command) := do
  match d with
  | .assertion a =>
    let ident ← liftTermElabM a.name.toSyntax
    let args : TSyntaxArray ``Lean.Parser.Term.bracketedBinder ←
      liftTermElabM (
        a.decls.toArray.mapM (fun (i, ty) => do
          let i ← i.toSyntax
          let ty ← ty.toSyntax
          `(Lean.Parser.Term.bracketedBinderF| ($i : $ty))
        )
      )
    let eTerm : Term ← liftTermElabM a.body.toSyntax
    let c ← `(command|
      theorem $ident $(args):bracketedBinder*
        : $eTerm
        := by sorry
    )
    return #[c]
  | .specFn f =>
  -- syntax: def add_one (x : Int) : Int := x + 1
    let ident ← liftTermElabM f.name.toSyntax
    let args : TSyntaxArray ``Lean.Parser.Term.bracketedBinder ←
      liftTermElabM (
        f.inputs.toArray.mapM (fun (i, ty) => do
          let i ← i.toSyntax
          let ty ← ty.toSyntax
          `(Lean.Parser.Term.bracketedBinderF| ($i : $ty))
        )
      )
    let returnType : Term ← liftTermElabM f.returnType.toSyntax
    let body : Term ← liftTermElabM f.body.toSyntax
    dbg_trace s!"Commanding a spec function {ident} {body}"
    let c ← `(command|
      def $ident $(args):bracketedBinder*
        : $returnType
        := $body
    )
    -- dbg_trace s!"get to toSyntax {c}"
    return #[c]

end VerusLean
