import VerusLean.VLIR.Defs
import VerusLean.VLIR.Pp
import Lean.Elab

namespace VerusLean

open Lean Syntax Elab Command Parser Term Parser.Command

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
  | .Array t => do
    let t ← t.toTerm
    `(Array $t)
  | .Struct name params =>
    let nameAsIdent ← name.toIdent
    let params := params.attach
    params.foldlM (init := nameAsIdent) (fun s ⟨ty, _⟩ => do
      let tyTerm ← ty.toTerm
      `($s:term $tyTerm:term)
    )

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
  | .Mul => `(($lhs) * ($rhs)) -- CZ: temp fix for operator precedence, when to add parentheses?
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
  | .Trigger => `($e) -- Ignore trigger information when constructing terms
  | .Proj dt field =>
    let dtName := Name.mkSimple dt
    let fieldName := mkIdent <| Name.str dtName field
    `(($fieldName:ident $e))
  | .IsVariant _ _ =>
    `(true && true)
  | .Box _ => `($e)
  | .Unbox _ => `($e)
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

/--
  Constructs a Lean meta-`Term` associated with a `Bind`.

  In Verus, `Bind`s only store the names and types of the fresh variables
  (and the binding expression for `let`s). However, Lean expects binding
  terms to have their body expressions as well. Thus, this function
  expects the term `t` asosciated with the body expression after the bind.
  For example, `∀ (x : Int), x ≠ x + 1` would have a `Bind`
  representing `∀ (x : Int)`, and `t` would represent `x ≠ x + 1`.

  Because `Let` has an `Exp`, `Bind.toTerm` is mutually recursive
  with `Exp.toTerm`.
-/
partial def Bind.toTerm (b : Bind) (t : Term) : MetaM Term := do
  match b with
  | .Let v e =>
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
  | .StructCtor _ fields =>
    -- For each field, make it a `structInstField`
    let fields ← fields.toArray.mapM (fun ⟨field, exp⟩ => do
      let fieldIdent ← field.toIdent
      let expTerm ← Exp.toTerm exp
      `(structInstField| $fieldIdent:ident := $expTerm )
    )
    `( { $fields:structInstField* } )
  | .EnumCtor dt variant data =>
    let dtName := Name.mkStr .anonymous dt
    let i := mkIdent <| Name.mkStr dtName variant
    let data ← data.toArray.mapM (fun ⟨_, e⟩ => do
      --let di ← di.toIdent
      let e ← e.toTerm
      `($e)
    )
    `( $i:ident $data:term* )
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
      -- Only include parentheses if the term is nontrivial
      -- (i.e., not a variable or a constant)
      if e.height = 1 then
        `($acc:term $t:term)
      else
        `($acc:term ($t:term))
    )

end /- mutual -/

/--
  Makes a single explicit binder from an array of identifiers and a type.

  For example, if `as := #[a, b]` and `ty : Int`,
  then the result is `(a b : Int)`.
-/
private def makeExplicitBinder (as : Array Ident) (ty : Typ) : MetaM (TSyntax ``bracketedBinderF) := do
  let ty ← ty.toTerm
  let binders : TSyntaxArray `ident ← as.mapM Ident.toIdent
  `(bracketedBinderF| ($binders:ident* : $ty:term))

/--
  Makes a `TSyntaxArray ``brackedBinder` with like types collected under
  a single bracketed binder.

  For example, if `as := #[a, b, c]` with `a b : Int` and `c : Nat`,
  then the result is `(a b : Int) (c : Nat)`.
-/
private def makeExplicitBinders (as : Array (Ident × Typ)) : MetaM (TSyntaxArray ``bracketedBinder) := do
  let ⟨arr, ltis, ty?⟩ ← as.foldlM (init := (#[], #[], none)) (fun ⟨arr, likeTypIdents, ty?⟩ ⟨i, ty⟩ => do
    match ty? with
    | none =>
      return (arr, likeTypIdents.push i, some ty)
    | some ty' =>
      if ty = ty' then
        -- Defer mapping them into bracketed binder until diff detected
        return (arr, likeTypIdents.push i, some ty)
      else
        let binder ← makeExplicitBinder likeTypIdents ty
        return (arr.push binder, #[], some ty)
  )

  match ty? with
  | some ty => return arr.push (← makeExplicitBinder ltis ty)
  | none =>
    if as.size = 0 then return #[]
    else throwError "empty array"

def Decl.toTerm (d : Decl) : MetaM (TSyntax `command) := do
  match d with
  | .assertion ⟨name, decls, body⟩ =>
    let ident ← name.toIdent
    let args ← makeExplicitBinders decls.toArray
    let eTerm : Term ← body.toTerm
    `(command| theorem $ident $args:bracketedBinder* : $eTerm := by sorry )

  | .specFn ⟨name, inputs, returnTy, body⟩ =>
    let ident ← name.toIdent
    let args ← makeExplicitBinders inputs.toArray
    let returnType : Term ← returnTy.toTerm
    let body : Term ← body.toTerm
    `(command| def $ident $args:bracketedBinder* : $returnType := $body )

  | .struct ⟨name, params, fields⟩ =>
    let nameAsIdent ← name.toIdent
    -- TODO: Skipping parameters for now
    let fields ← fields.toArray.mapM
      (fun ⟨fieldName, fieldTy⟩ => do
        let field ← fieldName.toIdent
        let ty ← fieldTy.toTerm
        `(structSimpleBinder| $field:ident : $ty))
    `(command| structure $nameAsIdent:ident where $fields:structSimpleBinder* )

  | .enum ⟨name, fields⟩ =>
    let nameAsIdent ← name.toIdent
    let fields ← fields.toArray.mapM
      (fun ⟨variantName, data⟩ => do
        let variant ← variantName.toIdent
        let data ← data.toArray.mapM (fun ⟨_, ty⟩ => do
          let ty ← ty.toTerm
          `($ty)
        )
        `(ctor| | $variant:ident ))

    `(command| inductive $nameAsIdent:ident where $fields:ctor* )

  | .func ⟨name, reqs, ens, decls⟩ =>
    let ident ← name.toIdent
    let reqs : Array Term ← reqs.toArray.mapM (·.toTerm)
    let ens : Term ← ens.toTerm
    let init : Term := mkIdent ``_root_.Bool.true
    let body : Term ← reqs.foldlM (init := init) (fun acc e => `($acc && ($e)))
    let body ← `( $body → $ens )
    let args ← makeExplicitBinders decls.toArray
    `(command| theorem $ident $args:bracketedBinder* : $body := by sorry )

end VerusLean
