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
  | .Trigger => `($e)
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

partial def ExpX.toSyntax (e : ExpX) : TermElabM Term := do
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
  -- | .ArrayLiteral es =>
  --   let es ← es.mapM ExpX.toSyntax
  --   `(#[ $es,* ])

  -- Call (fn : CallFun) (typs : List Typ) (exps : List ExpX)
  | .Call fn typs exps =>
    let fn := match fn with
      | CallFun.Fun fn => fn.toSyntax
    -- let typs ← typs.mapM Typ.toSyntax
    let exps ← exps.mapM ExpX.toSyntax
    let exps_TSepArray := exps.foldl Syntax.TSepArray.push (Syntax.TSepArray.mk #[] (sep := ","))
    dbg_trace s!"elab get here!! {fn}, {exps}"
    -- let termSyntaxList := exps.map (·.raw)
    `($fn ( [$exps_TSepArray,*]) )
    -- #check Syntax.TSepArray
    -- let tupleSyntax := Syntax.node `Lean.Parser.Term.paren (#[mkAtom "(", mkSep "," termSyntaxList, mkAtom ")"])
    -- mkParen (mkSep "," (terms.map exps))
  | .Bind (Bind.Quant q vars) e => do
    -- let xs := vars
    -- vars.toArray.map (fun (i, ty) =>
    --   let i := i.toSyntax
    --   let ty ← ty.toSyntax
    --   return (i, ty)
    -- )
    -- let vs := xs.map Prod.fst
    -- let vs_syntax := Idents.toSyntax vs.toArray
    -- let vs_tsyntax := vs_syntax.map TSyntax.mk
    -- let ts := xs.map Prod.snd
    -- let ts_syntax := (← ts.mapM Typ.toSyntax).toArray
    -- let varsExists := Prod.mk vs_tsyntax ts_syntax
    -- let varsExists := varsExists.mapM (fun (i, ty) =>
    --   return (i, ty)
    -- )

    let varsForall : TSyntaxArray `Lean.Parser.Term.bracketedBinder ←
      (
        vars.toArray.mapM (fun (i, ty) => do
          let i := i.toSyntax
          let ty ← ty.toSyntax
          `(Lean.Parser.Term.bracketedBinderF| ($i : $ty))
        )
      )
    let e ← e.toSyntax
    match q with
    | Quant.Forall => `(∀ $(varsForall):bracketedBinder*, $e)
    | Quant.Exists => `(∀ $(varsForall):bracketedBinder*, $e)
    -- | Quant.Exists =>  `(∃ $[($vs_tsyntax : $ts_syntax)]*, $e)
    -- | Quant.Exists =>  `(∃ $vs_syntax:ident $ts_syntax:binderIdent*, $e)
    -- | Quant.Exists => `(∃ $[$varsExists]*, $e)

#check Exists
#check Lean.Parser.Term.bracketedBinder
-- #check Forall
-- #check forall


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
  | .specfn fnName inputs returnType body =>
  -- syntax: def add_one (x : Int) : Int := x + 1
    let ident := fnName.toSyntax
    let args : TSyntaxArray ``Lean.Parser.Term.bracketedBinder ←
      liftTermElabM (
        inputs.toArray.mapM (fun (i, ty) => do
          let i := i.toSyntax
          let ty ← ty.toSyntax
          `(Lean.Parser.Term.bracketedBinderF| ($i : $ty))
        )
      )
    let returnType : Term ← liftTermElabM returnType.toSyntax
    let body : Term ← liftTermElabM body.toSyntax
    let c ← `(command|
      def $ident $(args):bracketedBinder*
        : $returnType
        := $body
    )
    -- dbg_trace s!"get to toSyntax {c}"
    return #[c]

end VerusLean
