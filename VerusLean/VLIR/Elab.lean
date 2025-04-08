import VerusLean.VLIR.Defs
import VerusLean.VLIR.Pp
import VerusLean.Tactic.ByVerus
import Lean.Elab

namespace VerusLean

/-
  TODOs:

  - Develop a method of parenthesizing expressions/terms as they are built
    (especially the binary ones) that takes into account the underlying
    precedences of the sub-expressions. For example, (a + b) * (c + d)
    currently gets elaborated as a + (b * c) + d, since multiplication
    has higher precedence than addition.
    - One solution is to return a pair of `(Term × Precedence)`, or to operate
      in a wrapper monad for `MetaM` that has a precendence.
-/

open Lean Syntax Elab Command Parser Term Parser.Command Parser.Term

private def trueIdent : Lean.Ident := mkIdent ``true
private def falseIdent : Lean.Ident := mkIdent ``false
private def TrueIdent : Lean.Ident := mkIdent ``True
private def FalseIdent : Lean.Ident := mkIdent ``False
private def ArrayIdent : Lean.Ident := mkIdent ``Array

def Ident.toIdent (i : Ident) : MetaM Lean.Ident :=
  return mkIdent (.mkSimple i)

def Typ.toTerm (ty : Typ) : MetaM Term := do
  match ty with
  | .Unit => return mkIdent ``_root_.Unit
  | .Tuple ty₁ ty₂ => do
    let ty₁ ← ty₁.toTerm
    let ty₂ ← ty₂.toTerm
    -- CC: TODO Dependent typing?
    `($ty₁ × $ty₂)
  | .Bool => return mkIdent ``_root_.Bool
  | .Int => return mkIdent ``_root_.Int
  | .Nat => return mkIdent ``_root_.Nat
  | .UInt _ => return mkIdent ``_root_.UInt32
  | .SInt _ => `(BitVec 32)
  | .Char => return mkIdent ``_root_.Char
  | .StrSlice => throwError "StrSlice not supported"
  | .Array t => do
    let t ← t.toTerm
    `($ArrayIdent $t)
  | .TypParam name =>
    let nameAsIdent ← name.toIdent
    return nameAsIdent
  | .Struct name params
  | .Enum name params =>
    let nameAsIdent ← name.toIdent
    let params := params.attach
    params.foldlM (init := nameAsIdent) (fun s ⟨ty, _⟩ => do
      let tyTerm ← ty.toTerm
      `($s:term $tyTerm:term))


def Const.toTerm (c : Const) : MetaM Term := do
  match c with
  | Const.Bool b =>
    -- See Lean.Init.Meta, for Quote Bool and mkCIdent
    -- No way to take the boolean directly?
    match b with
    | true => return trueIdent
    | false => return falseIdent
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
  | .Proj _ field =>
    let field ← field.toIdent
    `($e.$field)
  | .IsVariant dt variant =>
    let dt ← dt.toIdent
    let variant ← variant.toIdent
    `(match $e:term with
      | $dt.$variant .. => $trueIdent
      | _ => $falseIdent)
  | .Box _ => `($e)   -- Ignore boxed-type information when constructing terms
  | .Unbox _ => `($e) -- Ignore boxed-type information when constructing terms
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
  | .Let v ty e =>
    let v ← v.toIdent
    let ty ← ty.toTerm
    let e ← e.toTerm
    -- See `letMVar` in `Lean.Parser.Term.lean`
    `(let $v : $ty := $e; $t)
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
        `($acc:term ($t:term)))

  | .StructCtor _ fields =>
    -- For each field, make it a `structInstField`
    let fields ← fields.toArray.mapM (fun ⟨field, exp⟩ => do
      let fieldIdent ← field.toIdent
      let expTerm ← Exp.toTerm exp
      `(structInstField| $fieldIdent:ident := $expTerm ))
    `( { $fields:structInstField* } )

  | .EnumCtor dt variant data =>
    let dtName := Name.mkStr .anonymous dt
    let i := mkIdent <| Name.mkStr dtName variant
    let data := data.toArray
    let numDataVals := data.size
    let identAsTerm ← `($i:ident)

    -- Build up the application of the data elements to the constructor
    data.foldlM (init := identAsTerm) (fun acc ⟨i, e⟩ => do
      let i ← i.toIdent
      let e ← e.toTerm
      -- Verus tells us not to expect the data elements to be
      -- serialized in order, so we need to name them if there's more than one
      if numDataVals = 1 then
        `($acc $e)
      else
        `($acc ($i:ident := $e:term)))

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

  | .ArrayLiteral es =>
    let es ← es.toArray.mapM (fun e => do
      let e ← e.toTerm
      `(term| $e:term))
    `(#[ $es:term,* ])

end /- mutual -/

def addToTacticOption (acc : Option (TSyntax `tactic)) (tac : TSyntax `tactic) : MetaM (TSyntax `tactic) := do
  match acc with
  | none => return tac
  | some acc => `(tactic| ($acc:tactic; $tac:tactic))

partial def Stm.toTerm (stm : Stm) : MetaM (TSyntax `tactic) := do
  match stm with
  | .Assert e
  | .Assume e =>
    let e ← e.toTerm
    `(tactic| have : $e := by verus)

  | .AssertBitVector _ ens =>
    -- TODO: Skipping requires
    match ens with
    | [] => `(tactic| skip) -- CC: Really, this should be an error
    | [e] =>
      let e ← e.toTerm
      `(tactic| have : $e := by verus)
    | (e :: es) =>
      let e ← e.toTerm
      let ens ← es.foldlM (init := e) (fun acc e => do
        let e ← e.toTerm
        `($acc:term ∧ $e:term))
      `(tactic| have : $ens := by verus)

  | .AssertLean e =>
    let e ← e.toTerm
    `(tactic| have : $e := by auto? )

  | .Assign lhs lhsTy rhs _ =>
    let lhs ← lhs.toIdent
    let lhsTy ← lhsTy.toTerm
    let rhs ← rhs.toTerm
    `(tactic| let $lhs : $lhsTy := $rhs)

  | .DeadEnd stm => stm.toTerm

  | .Block stms =>
    let stms ← stms.toArray.mapM (fun s => do
      let s ← s.toTerm
      `(tactic| $s:tactic))

    -- Filter our those tactics that are trivial (`skip`)
    -- This is mainly due to us not implementing other branches here
    -- We explicitly type this new array to keep the syntax category
    let stms : Array (TSyntax `tactic) := stms.filter (fun tac =>
      match tac with
      | `(tactic| skip) => false
      | _ => true)

    `(tactic| ($stms:tactic*))

    -- CC: Alternate method with slightly less well-formatted parentheses
    /-
    match ← stms.foldlM (init := none) (fun acc stm => do
      let tac ← stm.toTerm
      return some <| ← addToTacticOption acc tac
    ) with
    | none => `(tactic| skip)
    | some tac => return tac -/

  | _ => `(tactic| skip)

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


def Assertion.toCommand (a : Assertion) : MetaM (TSyntax `command) := do
  let ⟨name, decls, body⟩ := a
  let ident ← name.toIdent
  let args ← makeExplicitBinders decls.toArray
  let eTerm ← body.toTerm
  `(command| theorem $ident $args:bracketedBinder* : $eTerm := by auto? )


def SpecFn.toCommand (f : SpecFn) : MetaM (TSyntax `command) := do
  let ⟨name, inputs, returnType, body⟩ := f
  let ident ← name.toIdent
  let args ← makeExplicitBinders inputs.toArray
  let returnType ← returnType.toTerm
  let body ← body.toTerm
  `(command| def $ident $args:bracketedBinder* : $returnType := $body )

def ProofFn.toCommand (f : ProofFn) : MetaM (TSyntax `command) := do
  let ⟨name, inputs, requires, ensures, body⟩ := f
  let ident ← name.toIdent
  let args ← makeExplicitBinders inputs.toArray
  -- CC: TODO requires and ensures (currently disallowed by Verus)
  let body ← body.toTerm
  if ensures.length = 0 then
    `(command| theorem $ident $args:bracketedBinder* : TrivialProofFn := by
      $body
      trivial)
  else
    `(command| theorem $ident $args:bracketedBinder* : 5 = 5 := by
      $body
      auto? )

def Struct.toCommand (s : Struct) : MetaM (TSyntax `command) := do
  let ⟨name, params, fields⟩ := s
  let nameAsIdent ← name.toIdent
  -- TODO: Skipping parameters for now
  let fields ← fields.toArray.mapM
    (fun ⟨fieldName, fieldTy⟩ => do
      let field ← fieldName.toIdent
      let ty ← fieldTy.toTerm
      `(structSimpleBinder| $field:ident : $ty))
  `(command| structure $nameAsIdent:ident where $fields:structSimpleBinder* )


def Enum.toCommand (e : Enum) : MetaM (TSyntax `command) := do
  let ⟨name, _, fields⟩ := e
  -- TODO: Type parameters
  let nameAsIdent ← name.toIdent
  let fields ← fields.toArray.mapM
    (fun ⟨variantName, data⟩ => do
      let variant ← variantName.toIdent
      let binders ← makeExplicitBinders data.toArray
      `(ctor| | $variant:ident $binders:bracketedBinder* ))
  `(command| inductive $nameAsIdent:ident where $fields:ctor* )


def FuncCheckSst.toCommand (f : FuncCheckSst) : MetaM (TSyntax `command) := do
  let ⟨name, reqs, enss, decls⟩ := f
  let ident ← name.toIdent
  let reqs : Array Term ← reqs.toArray.mapM (·.toTerm)
  let enss : Array Term ← enss.toArray.mapM (·.toTerm)
  let init : Term := trueIdent
  let req : Term ← reqs.foldlM (init := init) (fun acc e => `($acc && ($e)))
  let ens : Term ← enss.foldlM (init := init) (fun acc e => `($acc && ($e)))
  let body ← `( $req → $ens )
  let args ← makeExplicitBinders decls.toArray
  `(command| theorem $ident $args:bracketedBinder* : $body := by auto? )


def Decl.toTerm (d : Decl) : MetaM (TSyntax `command) := do
  match d with
  | .assertion a => a.toCommand
  | .specFn f => f.toCommand
  | .proofFn f => f.toCommand
  | .struct s => s.toCommand
  | .enum e => e.toCommand
  | .func f => f.toCommand

end VerusLean
