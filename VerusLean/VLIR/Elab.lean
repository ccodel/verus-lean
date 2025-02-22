import VerusLean.VLIR.Defs
import Lean.Elab

namespace VerusLean

open Lean Elab Command Parser Term

def Ident.toIdent (i : Ident) : MetaM Lean.Ident :=
  return mkIdent (.mkSimple i)

def Idents.toIdent (i : Idents) : MetaM (Array Lean.Ident) :=
  i.mapM Ident.toIdent

def Typ.toTerm (ty : Typ) : MetaM Term := do
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
    let t ← t.toTerm
    `(Array $t)

def Const.toTerm (c : Const) : MetaM Term := do
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
def BitwiseOp.toTerm (b : BitwiseOp) (lhs rhs : Term) : MetaM Term := do
  match b with
  | .BitXor  => `($lhs ^^^ $rhs)
  | .BitAnd  => `($lhs &&& $rhs)
  | .BitOr   => `($lhs ||| $rhs)
  | .Shr _   => `($lhs >>> $rhs)
  | .Shl _ _ => `($lhs <<< $rhs)

def ArithOp.toTerm (a : ArithOp) (lhs rhs : Term) : MetaM Term := do
  match a with
  | .Add => `($lhs + $rhs)
  | .Sub => `($lhs - $rhs)
  | .Mul => `($lhs * $rhs)
  | .EuclideanDiv => `($lhs / $rhs)
  | .EuclideanMod => `($lhs % $rhs)

def InequalityOp.toTerm (i : InequalityOp) (lhs rhs : Term) : MetaM Term := do
  match i with
  | .Lt => `($lhs < $rhs)
  | .Le => `($lhs ≤ $rhs)
  | .Gt => `($lhs > $rhs)
  | .Ge => `($lhs ≥ $rhs)

def UnaryOp.toTerm (u : UnaryOp) (e : Term) : MetaM Term := do
  match u with
  | .Not => `(¬ ($e))
  | .BitNot _ => `(~~~ $e)
  | .Trigger => `($e)
  | _ => throwError "unsupported unary op {repr u}"

def BinaryOp.toTerm (b : BinaryOp) (lhs rhs : Term) : MetaM Term := do
  match b with
  | .And => `($lhs ∧ $rhs)
  | .Or => `($lhs ∨ $rhs)
  | .Xor => `($lhs ^^ $rhs)
  | .Implies => `($lhs → $rhs)
  | .Eq _ => `($lhs = $rhs)
  | .Ne => `($lhs ≠ $rhs)
  | .Inequality ineq => ineq.toTerm lhs rhs
  | .Arith arith _ => arith.toTerm lhs rhs
  | .Bitwise bitwise _ => bitwise.toTerm lhs rhs

def CallFun.toIdent : CallFun → MetaM (Lean.Ident)
  | CallFun.Fun i => i.toIdent

mutual

partial def Bind.toTerm (b : Bind) (t : Term) : MetaM Term := do
  match b with
  | .Let ⟨v, e⟩ =>
    let v ← v.toIdent
    let e ← e.toTerm
    -- See `letMVar` in `Lean.Parser.Term.lean`
    `(let $v := $e; $t)
  | .Quant q vars =>
    match q with
    | .Forall =>
      let varsForall : TSyntaxArray ``bracketedBinder ←
        vars.toArray.mapM (fun ⟨i, ty⟩ => do
          let i ← i.toIdent
          let ty ← ty.toTerm
          `(bracketedBinderF| ($i : $ty))
        )
      `(∀ $(varsForall):bracketedBinder*, $t)
    | .Exists => do
      if [] == vars then
        throwError "empty exists"
      let varsExists : TSyntaxArray ``bracketedExplicitBinders ←
        vars.toArray.mapM (fun ⟨i, ty⟩ => do
          let i ← i.toIdent
          let ty ← ty.toTerm
          `(bracketedExplicitBinders| ($i:ident : $ty))
        )
      `(∃ $(varsExists):bracketedExplicitBinders*, $t)
  | .Lambda vars =>
    let varsLambda : TSyntaxArray ``funBinder ←
      vars.toArray.mapM (fun ⟨i, ty⟩ => do
        let i ← i.toIdent
        let ty ← ty.toTerm
        `(funBinder| ($i : $ty))
      )
    `(fun $(varsLambda):funBinder* => $t)

partial def Exp.toTerm (e : Exp) : MetaM Term := do
  match e with
  | .Const c => c.toTerm
  | .Var i => i.toIdent
  | .Unary op e =>
    let e ← e.toTerm
    op.toTerm e
  | .Binary op lhs rhs =>
    let lhs ← lhs.toTerm
    let rhs ← rhs.toTerm
    op.toTerm lhs rhs
  | .If cond b₁ b₂ =>
    let cond ← cond.toTerm
    let b₁ ← b₁.toTerm
    let b₂ ← b₂.toTerm
    `(if $cond then $b₁ else $b₂)
  | .Bind bind exp =>
    let exp ← exp.toTerm
    bind.toTerm exp
  | .Call fn _ exps =>
    let fnIdent ← fn.toIdent
    let fn ← `(term| $fnIdent)
    exps.foldlM (init := fn) (fun acc e => do
      let t ← e.toTerm
      `($acc:term ($t:term))
    )
    -- let exps ← exps.mapM Exp.toTerm
    -- exps.foldlM (init := fnTerm)
    -- let exps_TSepArray : TSyntax `term := exps.foldl Syntax.TSepArray.push (Syntax.TSepArray.mk #[] (sep := ","))
    -- `(app| $fn $exps_TSepArray)

  -- | .ArrayLiteral es =>
  --   let es ← es.mapM Exp.toTerm
  --   `(#[ $es,* ])

end /- mutual -/

def Exps.toTerm (e : Exps) : MetaM (Array Term) := do
  e.mapM Exp.toTerm

def Decl.toTerm (d : Decl) : MetaM (TSyntax `command) := do
  match d with
  | .assertion a =>
    let ident ← a.name.toIdent
    let args : TSyntaxArray ``Lean.Parser.Term.bracketedBinder ←
      (
        a.decls.toArray.mapM (fun (i, ty) => do
          let i ← i.toIdent
          let ty ← ty.toTerm
          `(Lean.Parser.Term.bracketedBinderF| ($i : $ty))
        )
      )
    let eTerm : Term ← a.body.toTerm
    let c ← `(command|
      theorem $ident $(args):bracketedBinder*
        : $eTerm
        := by sorry
    )
    return c
  | .specFn f =>
    let ident ← f.name.toIdent
    let args : TSyntaxArray ``Lean.Parser.Term.bracketedBinder ←
      (
        f.inputs.toArray.mapM (fun (i, ty) => do
          let i ← i.toIdent
          let ty ← ty.toTerm
          `(Lean.Parser.Term.bracketedBinderF| ($i : $ty))
        )
      )
    let returnType : Term ← f.returnType.toTerm
    let body : Term ← f.body.toTerm
    -- dbg_trace s!"Commanding a spec function {ident} {body}"
    let c ← `(command|
      def $ident $(args):bracketedBinder*
        : $returnType
        := $body
    )
    return c

end VerusLean
