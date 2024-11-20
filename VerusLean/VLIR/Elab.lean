import VerusLean.VLIR.Defs
import Lean.Elab

namespace VerusLean

open Lean Elab Command

def Ident.toSyntax (i : Ident) : Lean.Ident :=
  mkIdent (.mkSimple i)

def Idents.toSyntax (i : Idents) : Array Lean.Ident :=
  i.map Ident.toSyntax

def Typ.toSyntax (ty : Typ) : TermElabM Term := do
  match ty with
  | .Bool => return mkIdent ``_root_.Bool
  | .Int => return mkIdent ``_root_.Int
  | .Nat => return mkIdent ``_root_.Nat
  | .UInt _ => return mkIdent ``_root_.UInt32
  | .SInt _ => `(BitVec 32)
  | .Char => return mkIdent ``_root_.Char
  | .StrSlice => throwError "StrSlice not supported"

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
  | .Not => `(! $e)
  | .BitNot _ => `(~~~ $e)
  | _ => throwError "unsupported unary op {repr u}"

#check Eq

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

def ExpX.toSyntax (e : ExpX) : TermElabM Term := do
  match e with
  | .Const c => c.toSyntax
  | .Var ident => return ident.toSyntax
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

def Exps.toSyntax (e : Exps) : TermElabM (Array Term) := do
  e.mapM ExpX.toSyntax

-- CC: Just use TSyntax `command?
def Decl.toSyntax (d : Decl) : CommandElabM (TSyntaxArray `command) := do
  match d with
  | .assertion thmName decls e =>
    let ident := thmName.toSyntax
    let args : TSyntaxArray ``Lean.Parser.Term.bracketedBinder ←
      liftTermElabM (
        decls.toArray.mapM (fun (i, ty) => do
          let i := i.toSyntax
          let ty ← ty.toSyntax
          `(Lean.Parser.Term.bracketedBinderF| ($i : $ty))
        )
      )
    let eTerm : Term ← liftTermElabM e.toSyntax
    let c ← `(command|
      theorem $ident $(args):bracketedBinder*
        : $eTerm
        := by sorry
    )
    return #[c]

end VerusLean
