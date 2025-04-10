import VerusLean.Json
import VerusLean.VLIR.Defs
import VerusLean.VLIR.Pp
import VerusLean.Basic.Monad
import Lean

namespace VerusLean

open Lean
open VName

/-- A map for variables. Alias for `Std.HashMap Ident Typ`. -/
abbrev VarMap := Std.HashMap Ident Typ

/-- A map for functions. Alias for `Std.HashMap Ident SpecFn`. -/
abbrev FnMap := Std.HashMap Ident SpecFn
abbrev DtMap := Std.HashMap Ident Struct
abbrev DeclMap := Std.HashMap Ident Decl

/--
  The parsing monad for Verus JSONs,
  which includes a state with a map from variable names to types.

  All exceptions are strings.

  The state is a mapping from variable names to their (primitive) types.
  For example, an unsigned integer of width 32 (in Rust, a `u32`) would be `UInt 32`.

  TODO: handle shadowing
-/
structure ParserState where
  expectedType : Typ := .Bool
  freeVars : VarMap := {}
  locVars : VarMap := {}
  -- Acts like a stack?
  boundVars : List (Ident × Typ) := []
  decls : DeclMap := {}
deriving Inhabited, Repr

abbrev VParser := EStateM String ParserState

/-- Alias for `Except String`. The argument following `ExStr` is the return type. -/
abbrev ExStr := Except String

namespace VParser

open EStateM

def getTyp : VParser Typ :=
  do let st ← get; return st.expectedType

def setTyp (t : Typ) : VParser Unit :=
  modify fun st => { st with expectedType := t }

def getFreeVars : VParser VarMap :=
  do let st ← get; return st.freeVars

def getLocVars : VParser VarMap :=
  do let st ← get; return st.locVars

def getBoundVars : VParser (List (Ident × Typ)) :=
  do let st ← get; return st.boundVars

-- Adds a free variable with the explicitly given name `var` and type `typ`.
def addFreeVarWithTyp (var : Ident) (typ : Typ) : VParser Unit := do
  modify fun st => { st with
    freeVars := st.freeVars.insert var typ
  }

def addLocVarWithTyp (var : Ident) (typ : Typ) : VParser Unit := do
  modify fun st => { st with
    locVars := st.locVars.insert var typ
  }

-- Adds a free variable, using the type stored in the state.
def addFreeVar (var : Ident) : VParser Unit := do
  addFreeVarWithTyp var (← getTyp)

def addLocVar (var : Ident) : VParser Unit := do
  addLocVarWithTyp var (← getTyp)

def pushBoundVar (var : Ident) (typ : Typ) : VParser Unit :=
  modify fun st => { st with boundVars := (var, typ) :: st.boundVars }

-- Pushes a list of bound vars.
-- Note that lower indexes in `vars` means they get popped off sooner.
-- This is opposite from what one might expect, but is typical stack behavior.
def pushBoundVars (vars : List (Ident × Typ)) : VParser Unit :=
  modify fun st => { st with boundVars := vars ++ st.boundVars }

-- Pops the newest bound variable off the stack.
-- If the stack is empty, nothing happens.
def popBoundVar : VParser Unit :=
  modify fun st => { st with boundVars := st.boundVars.tail }

-- Pops the `n` newest bound variables off the stack.
-- If `n` is greater than the size of the stack, then the stack becomes empty.
def popBoundVars (n : Nat) : VParser Unit :=
  modify fun st => { st with boundVars := st.boundVars.drop n }

/-- Perform the state-ful function `fn` with the bound vars `vars`,
    then pops them off the bound variables stack before returning. -/
def withBoundVars (vars : List (Ident × Typ)) (fn : VParser α) : VParser α := do
  pushBoundVars vars
  let a ← fn
  popBoundVars vars.length
  return a

/--
  Run function `fn` and then pop any bound vars added under `fn`.

  Note that this assumes that `fn` will only add variables and not modify
  the ones already on the stack.
-/
def restoreCurrentBoundVarsAfter (fn : VParser α) : VParser α := do
  let n := List.length <| ← getBoundVars
  let a ← fn
  let m := List.length <| ← getBoundVars
  popBoundVars (m - n)
  return a

/--
  Consults the bound vars, from newest to oldest, to see if one named `var` exists.
-/
def lookupBoundVarTyp? (var : Ident) : VParser (Option Typ) := do
  let boundVars ← getBoundVars
  match boundVars.find? (fun ⟨i, _⟩ => i == var) with
  | some (_, typ) => return some typ
  | none => return none

-- CC: TODO: addFreeVar if not bound? Marked `isMut`?

/--
  Only adds a free variable if it is not already bound locally.
-/
def addFreeVarWithTypIfNotBound (var : Ident) (typ : Typ) : VParser Unit := do
  match ← lookupBoundVarTyp? var with
  | some _ => return ()
  | none => addFreeVarWithTyp var typ

def addFreeVarIfNotBound (var : Ident) : VParser Unit := do
  addFreeVarWithTypIfNotBound var (← getTyp)

def addDecl (d : Decl) : VParser Unit :=
  modify fun st => { st with decls := st.decls.insert (name d) d }

def getDecl? (i : Ident) : VParser (Option Decl) :=
  do let st ← get; return st.decls.get? i

def coeWithState : Except String α → VParser α
  | .ok a => (fun s => Result.ok a s)
  | .error e => (fun s => Result.error e s)

instance instCoeExcept : Coe (Except String α) (VParser α) where
  coe := coeWithState

instance instCoeFunExcept {α : Type u} {β : Type} : Coe (α → ExStr β) (α → VParser β) where
  coe f := fun a => f a

end VParser

--------------------------------------------------------------------------------

open VParser

variable {m : Type → Type} [Monad m] [MonadExceptOf String m]

def xJsonFromSpanned (j : Json) : m Json :=
  j.getObjValM "x"

def widthFromJson (j : Json) : m Nat := do
  try
    j.getNatUnderKeyM "Width"
  catch _ => return 32 -- ArchWordSize, use 32 bit for now

-- TODO: This probably needs to return a namespace (list?), rather than a single ident
def pathedNameFromJson (j : Json) (pathKey : String := "path") : m Ident := do
  let pathed ← j.getObjValByPathM [pathKey, "segments"]
  Json.getStrM <| ← Json.getArrValM pathed 0

def pathedNameFromNameJson (j : Json) (pathKey : String := "path") : m Ident := do
  let nameObj ← j.getObjValM "name"
  pathedNameFromJson nameObj pathKey

partial def Typ.fromJson (j : Json) : m Typ := do
  match j.getStr? with
  | .ok "Bool" => return .Bool
  | .ok _ => throw "unsupported primitive type"
  | .error _ =>
    match ← j["Primitive", "Int", "ConstInt", "Datatype", "Boxed"] with
    | ("Primitive", obj) =>
      let t ← obj.getArrM
      match t[0]? with
      | some j =>
        match j.getStr? with
        | .ok "Array" =>
          -- In Verus, arrays are specified by their type and length
          -- We drop the length requirement (for now TODO)
          -- This type is in the first element of the array in the first index of `t`
          let ⟨arr, _⟩ ← obj.getArrWithSizeGeM 2
          let ⟨arrTyp, _⟩ ← arr[1].getArrWithSizeGeM 2
          let typ ← Typ.fromJson arrTyp[0]
          return .Array typ
        | _ => throw s!"unsupported primitive type: {j}"
      | none => throw s!"error, json: {obj}"

    | ("Int", obj) =>
      -- First, we check if the the underlying string is "Int" for mathematical integers
      match obj.getStr? with
      | .ok "Int" => return .Int
      | .ok "Nat" => return .Nat
      | .ok "USize" => return .UInt 32 -- assume 32 bit for now
      | .ok _ => throw s!"unsupported Int object string: {obj}"
      | .error _ =>
        -- Now check if it is a fixed-width integer
        match obj.getFirstVal ["U", "I"] with
        | .error _ => throw s!"unsupported Int object: {obj}"
        | .ok ("U", obj) =>
          match obj.getNat? with
          | .ok width => return Typ.UInt width
          | .error e => throw s!"[Typ.fromJson?]: {e}"
        | .ok ("I", obj) =>
          match obj.getNat? with
          | .ok width => return Typ.SInt width
          | .error e => throw s!"[Typ.fromJson?]: {e}"
        | .ok _ => throw s!"unsupported Int object: {obj}"

    | ("Datatype", obj) =>
      /-
        Filter the `Tuples` from the true datatypes.

        Verus represents tuples as Datatypes. The arity of the tuple is given
        after the colon. The elements in the array under index 1 are the type
        arguments to either the tuple or to the datatype.

        Because these aren't "Datatypes" on Lean's side of things, we direct
        any "Tuple" serialization to the correct type.
      -/
      let ⟨arr, _⟩ ← obj.getArrWithSizeGeM 3
      match arr[0].getNatUnderKey? "Tuple" with
      | .ok arity =>
        match arity with
        | 0 => return .Unit
        | 1 => throw "Tuples should not have a single type"
        | a + 2 =>
          let ⟨typArray, _⟩ ← arr[1].getArrWithSizeGeM (a + 2)
          let typeParams ← typArray.mapM Typ.fromJson

          -- Fold from the right (because product is right-associative)
          match typeParams.foldr (init := none) (fun typ acc  =>
              match acc with
              | none => some typ
              | some acc => some <| .Tuple typ acc) with
          | none => throw "no type params"
          | some ty => return ty
      | .error _ =>
        let name ← pathedNameFromJson arr[0] "Path"
        -- TODO: Ignoring parameters to the type for now
        let params := []
        return .Struct name params

    -- Boxed types are mainly used for SMT encodings in Verus.
    -- In Lean, just take the base type.
    | ("Boxed", obj) => Typ.fromJson obj
    | _ => throw "unsupported primitive type"

/--
  Parses a "span" object and forwards the underlying data to a given function `fj`.

  Also adds the type annotation for the span to the state.
  This annotation should be added to the state's `HashMap` when encountering a `Var`.
-/
def fromJsonSpanned {α : Type} (j : Json) (fj : Json → VParser α) : VParser α := do
  let typ ← Typ.fromJson <| ← j.getObjValM "typ"
  let x ← j.getObjVal? "x"
  setTyp typ
  fj x

--------------------------------------------------------------------------------

def Mode.fromJson (j : Json) : m Mode := do
  match ← j.getStrM with
  | "Spec"  => return .Spec
  | "Proof" => return .Proof
  | "Exec"  => return .Exec
  | str => throw s!"[Mode.fromJson?]: Expected one of \{ Spec, Proof, Exec }, got {str}"

def Const.fromJson (j : Json) : m Const := do
  match ← j["Bool", "Int", "StrSlice", "Char"] with
  | ("Bool", v) => return Const.Bool <| ← v.getBoolM
  | ("Int", v) =>
    -- Ints are serialized as an array, with the first element the sign enum
    -- and the second value is the data, an array of u64s.
    let ⟨arr, _⟩ ← v.getArrWithSizeGeM 2
    let s := arr[0]
    let n := arr[1]
    match ← s.getNatM with
    | 0 =>
      -- no sign
      -- CZ: according to bigint.rs, 0 is minus, 1 is no sign, 2 is plus?
      return Const.Int 0
    | 1 =>
      -- positive number
      -- TODO: Need some computation for the big int
      -- For now, take the first entry and move on
      let nArr ← n.getArrM
      let n := nArr.getD 0 (Json.num <| JsonNumber.fromNat 0)
      return Const.Int <| Int.ofNat <| ← n.getNatM
    | 2 =>
      -- negative number
      -- TODO: Need some computation for the big int
      -- For now, take the first entry and move on
      let nArr ← n.getArrM
      let n := nArr.getD 0 (Json.num <| JsonNumber.fromNat 0)
      return Const.Int <| -(Int.ofNat <| ← n.getNatM)
    | _ => throw "[Const.fromJson?]: Expected an Int sign of 0, 1, or 2"
  | ("StrSlice", _) => throw "StrSlice not yet implemented"
  | ("Char", _) => throw "Char not yet implemented"
  | _ => throw "[Const.fromJson?]: Unexpected match"

def Bitwise.fromJson (j : Json) : m BitwiseOp :=
  match j.getStr? with
  | .ok "BitXor" => return .BitXor
  | .ok "BitAnd" => return .BitAnd
  | .ok "BitOr"  => return .BitOr
  | .ok str => throw s!"[Bitwise.fromJson?]: Expected one of \{ BitXor, BitAnd, BitOr }, got {str}"
  | .error _ => do
    -- Try one of the shifts instead
    -- They are Json objects that store the width (and sign extension)
    match ← j["Shr", "Shl"] with
    | ("Shr", obj) => do
      let width ← widthFromJson obj
      return .Shr width

    | ("Shl", obj) =>
      let ⟨arr, _⟩ ← obj.getArrWithSizeGeM 2
      let width ← widthFromJson arr[0]
      return .Shl width (← arr[1].getBoolM)

    | _ => throw s!"[Bitwise.fromJson?]: Expected one of \{ Shr, Shl }, got {j}"

def ArithOp.fromJson (j : Json) : m ArithOp := do
  match ← j.getStrM with
  | "Add"          => return .Add
  | "Sub"          => return .Sub
  | "Mul"          => return .Mul
  | "EuclideanDiv" => return .EuclideanDiv
  | "EuclideanMod" => return .EuclideanMod
  | s => throw s!"[ArithOp.fromJson?]: Expected one of \{ Add, Sub, Mul, Div, Mod }, got {s}"

def InequalityOp.fromJson (j : Json) : m InequalityOp := do
  match ← j.getStrM with
  | "Le" => return .Le
  | "Ge" => return .Ge
  | "Lt" => return .Lt
  | "Gt" => return .Gt
  | s => throw s!"[InequalityOp.fromJson?]: Expected one of \{ Le, Ge, Lt, Gt }, got {s}"

def UnaryOp.fromJson (j : Json) : m UnaryOp := do
  match j.getStr? with
  | .ok "Not"    => return .Not
  | .ok "BitNot" => throw "BitNot not yet implemented"
  | .ok "Clip"   => throw "Clip not yet implemented"
  | .ok s => throw s!"[UnaryOp.fromJson?]: Expected one of \{ Not, BitNot, Clip }, got {s}"
  | .error _ =>
    match ← j["BitNot", "Trigger", "Clip"] with
    | ("BitNot", obj) => -- Try seeing if "BitNot" has a width
      let width ← widthFromJson obj
      return .BitNot width
    | ("Trigger", _) => return .Trigger
    | ("Clip", _) =>
    --   let range ← obj.getObjValM "range"
    --   let truncate ← Json.getBoolM <| ← obj.getObjValM "truncate"
    --   return .Clip range truncate
      throw "Clip not yet implemented"
    | _ => throw s!"[UnaryOp.fromJson?]: Expected one of \{ BitNot, Trigger }, got {j}"

/--
  Parses a unary operation under the "UnaryOpr" key.

  Verus divides unary operations into simple and complex operations.
  Simple ones are generally logical or bitwise operations,
  and are parsed by `UnaryOp.fromJson?`.
  This function parses the complicated ones: projection, etc.

  -- TODO: Combine into `UnaryOp.fromJson?`?
  -- TODO: Require the parser state to refer to data types?
-/
def UnaryOp.oprFromJson (j : Json) : m UnaryOp := do
  match ← j["Field", "IsVariant", "Box", "Unbox"] with
  | ("Field", obj) =>
    -- TODO: Skipping data type
    let variant ← obj.getStrUnderKeyM "variant"
    let field ← obj.getStrUnderKeyM "field"
    return .Proj variant field
  | ("IsVariant", obj) =>
    let dtObj ← obj.getObjValM "datatype"
    let dt ← pathedNameFromJson dtObj "Path"
    let variant ← obj.getStrUnderKeyM "variant"
    return .IsVariant dt variant
  | ("Box", obj) =>
    let typ ← Typ.fromJson obj
    return .Box typ
  | ("Unbox", obj) =>
    let typ ← Typ.fromJson obj
    return .Unbox typ
  | _ =>
    return .Trigger

def BinaryOp.fromJson (j : Json) : m BinaryOp :=
  -- Most are single strings, but Eq has a mode attached, etc.
  match j.getStr? with
  | .ok "And"     => return .And
  | .ok "Or"      => return .Or
  | .ok "Xor"     => return .Xor
  | .ok "Implies" => return .Implies
  | .ok "Ne"      => return .Ne
  | .ok s => throw s!"[BinaryOp.fromJson?]: Expected one of \{ And, Or, Xor, Implies, Ne }, got {s}"
  | .error _ => do
    -- Try one of the object ops instead
    match ← j["Eq", "Inequality", "Bitwise", "Arith"] with
    | ("Eq", obj)         => return .Eq (← Mode.fromJson obj)
    | ("Inequality", obj) => return .Inequality (← InequalityOp.fromJson obj)
    | ("Bitwise", obj) =>
      -- Object under "Bitwise" should be a two-element array with an op and a mode
      let ⟨arr, _⟩ ← obj.getArrWithSizeGeM 2
      let op ← Bitwise.fromJson arr[0]
      let mode ← Mode.fromJson arr[1]
      return .Bitwise op mode
    | ("Arith", obj) =>
      -- Object under "Arith" should be a two-element array with an op and a mode
      let ⟨arr, _⟩ ← obj.getArrWithSizeGeM 2
      let op ← ArithOp.fromJson arr[0]
      let mode ← Mode.fromJson arr[1]
      return .Arith op mode
    | _ => throw s!"[BinaryOp.fromJson?]: Expected one of \{ And, Or, Xor, Implies, Eq }, got something else: {j}"

def Quant.fromJson (j : Json) : m Quant := do
  match ← j.getObjValM "quant" with
  | "Forall" => return .Forall
  | "Exists" => return .Exists
  | s => throw s!"[Quant.fromJson?]: Expected one of \{ Forall, Exists }, got {s}"

def CallFun.fromJson (j : Json) : m CallFun := do
  let ⟨arr, _⟩ ← j.getArrUnderKeyWithSizeGeM "Fun" 1
  return .Fun <| ← pathedNameFromJson arr[0]

def VarBinder.fromJson (j : Json) (key : String := "typ") : m (Ident × Typ) := do
  let ⟨arr, _⟩ ← j.getArrUnderKeyWithSizeGeM "name" 1
  let name ← arr[0].getStrM
  let typ ← Typ.fromJson <| ← j.getObjValM key
  return (name, typ)

def VarBinder.typBindersFromJson (j : Json) : m (List (Ident × Typ)) := do
  let (arr : _root_.Array Json) ← j.getArrM
  arr.toList.mapM (VarBinder.fromJson · "a")

def Var.fromJson (j : Json) : m Ident := do
  let ⟨arr, _⟩ ← j.getArrWithSizeGeM 2
  let ident ← arr[0].getStrM
  match ident with
  | "tmp%" => return s!"tmp{← arr[1].getNatUnderKeyM "VirTemp"}"
  | _ => return ident


mutual /- {Bind, Exp}.fromJson -/

partial def Bind.fromJson (j : Json) : VParser Bind := do
  let obj : Json ← xJsonFromSpanned j
  match ← obj.getFirstVal ["Quant"] with
  | ("Quant", (q : Json)) =>
    let ⟨arr, _⟩ ← q.getArrWithSizeGeM 4
    let q ← Quant.fromJson arr[0]
    let binders ← VarBinder.typBindersFromJson arr[1]
    return .Quant q binders
  | _ => throw "unexpected"

partial def Exp.fromJson (j : Json) : VParser Exp := do
  -- Expect that exactly one of the enumerated options will be true
  match ← j["Const", "Var", "VarLoc", "Call", "Ctor", "Unary", "UnaryOpr", "Binary", "If", "Bind", "ArrayLiteral"] with
  | ("Const", obj) => do
    return .Const <| ← Const.fromJson obj

  | ("Var", obj) =>
    let ident ← Var.fromJson obj
    addFreeVarIfNotBound ident
    return .Var ident

  | ("VarLoc", obj) =>
    let ident ← Var.fromJson obj
    addLocVar ident
    return .Var ident

  | ("Call", obj) =>
    -- Should be an object with a function name and arguments
    -- The function's name is the 0th element, the arguments the 2nd element (an array)
    let ⟨arr, _⟩ ← obj.getArrWithSizeGeM 3
    let callFn ← CallFun.fromJson arr[0]
    let expsJson ← arr[2].getArrM
    let exps : Array Exp ← expsJson.mapM (fromJsonSpanned · Exp.fromJson)
    return .Call callFn [] exps.toList

  | ("Ctor", obj) =>
    let ⟨arr, _⟩ ← obj.getArrWithSizeGeM 3
    let pathedName ← pathedNameFromJson arr[0] "Path"

    /- TODO: This parsing code doesn't take into account more complicated
      namespace pathing in Rust. We are assuming that all paths/variants
      are contained in the same file. To be fixed later.  -/
    let dt ← arr[1].getStrM

    -- According to Verus, the order of the fields within a `Ctor` node
    -- is unspecified, so parsing should not rely on field order.
    let fields ← arr[2].getArrM

    -- For each field, parse a field name and its expression
    let parsedFields ← fields.mapM (fun fObj => do
      let name ← Json.getStrUnderKeyM fObj "name"
      -- The expression lies under two `Spanned` objects
      let a ← Json.getObjValM fObj "a"
      let exp ← fromJsonSpanned a Exp.fromJson
      return (name, exp))

    match ← getDecl? pathedName with
    | none => throw s!"[ExpX.fromJson]: Could not find datatype {pathedName}"
    | some (Decl.struct _) => return .StructCtor dt parsedFields.toList
    | some (Decl.enum _) => return .EnumCtor pathedName dt parsedFields.toList
    | _ => throw s!"[ExpX.fromJson]: Encountered an unexpected decl with name {pathedName}"

  | ("Unary", obj) =>
    -- A unary object should be an array with an op and a data element
    let ⟨arr, _⟩ ← obj.getArrWithSizeGeM 2
    let op   ← UnaryOp.fromJson arr[0]
    let data ← fromJsonSpanned arr[1] Exp.fromJson
    return .Unary op data

  | ("UnaryOpr", obj) =>
    -- A complex unary object should be an array with an op and a data element
    let ⟨arr, _⟩ ← obj.getArrWithSizeGeM 2
    let op  ← UnaryOp.oprFromJson arr[0]
    let data ← fromJsonSpanned arr[1] Exp.fromJson

    -- Erase (Un)Box operations, just return the base type or expression
    match op with
    | .Box _ | .Unbox _ => return data
    | _ => return .Unary op data

  | ("Binary", obj) =>
    -- A binary object should be an array with an op and two data elements
    let ⟨arr, _⟩ ← obj.getArrWithSizeGeM 3
    let op    ← BinaryOp.fromJson arr[0]
    let data₁ ← fromJsonSpanned arr[1] Exp.fromJson
    let data₂ ← fromJsonSpanned arr[2] Exp.fromJson
    return .Binary op data₁ data₂

  | ("If", obj) =>
    -- Should be an array with three expressions
    let ⟨arr, _⟩ ← obj.getArrWithSizeGeM 3
    let cond    ← fromJsonSpanned arr[0] Exp.fromJson
    let branch₁ ← fromJsonSpanned arr[1] Exp.fromJson
    let branch₂ ← fromJsonSpanned arr[2] Exp.fromJson
    return .If cond branch₁ branch₂

  | ("Bind", obj) =>
    -- Should be an array with a bind and an expression
    let ⟨arr, _⟩ ← obj.getArrWithSizeGeM 2
    let bind ← Bind.fromJson arr[0]
    let exp ← withBoundVars bind.idents (fromJsonSpanned arr[1] Exp.fromJson)
    return .Bind bind exp

  | ("ArrayLiteral", obj) =>
    -- `obj` should be an array with the exact elements
    let arr ← obj.getArrM
    let elems ← arr.mapM (fromJsonSpanned · Exp.fromJson)
    return .ArrayLiteral elems.toList

  | s => throw s!"[ExpX.fromJson?]: Expected an Exp branch string, got {s}"

end /- mutual -/


/--
  Parses a `Dest` expression, but with the expectation that the result
  is an identifier. Mainly used to build `Assign`s.

  In Verus, there are several ways to store a variable identifier in an
  expression (an `Exp`): `Var`, `VarLoc`, `VarAt`, `Loc`, etc.

  This function will parse the underlying `Exp` under the "dest", but
  will throw an error if the expression is not a variable identifier.

  TODO: Dropped type information?
-/
def Dest.fromJson (j : Json) : VParser (Ident × Typ) := do
  let e ← fromJsonSpanned j Exp.fromJson
  let ty ← getTyp
  match e with
  | .Var i => return (i, ty)
  | _ => throw s!"Expected a variable expression, got {e}"


partial def Stm.fromJson (j : Json) : VParser Stm := do
  match ← j["Call", "Assert", "AssertBitVector", "AssertQuery", "AssertCompute", "AssertLean",
    "Assume", "Assign", "DeadEnd", "Return", "BreakOrContinue", "If", "Loop",
    "OpenInvariant", "ClosureInner", "Block"] with

  | ("Call", _) =>
    throw "Call not yet implemented"

  | ("Assert", obj) =>
    let ⟨arr, _⟩ ← obj.getArrWithSizeGeM 3
    let e ← fromJsonSpanned arr[2] Exp.fromJson
    return .Assert e

  | ("AssertBitVector", obj) =>
    -- CC TODO: Untested. I haven't looked at an actual JSON yet to see if this matches
    let arrReq ← obj.getArrUnderKeyM "requires"
    let requires ← arrReq.mapM (fromJsonSpanned · Exp.fromJson)
    let arrEns ← obj.getArrUnderKeyM "ensures"
    let ensures ← arrEns.mapM (fromJsonSpanned · Exp.fromJson)
    return .AssertBitVector requires.toList ensures.toList

  | ("AssertQuery", obj) =>
    let stm ← fromJsonSpanned obj Stm.fromJson
    return .AssertQuery stm

  | ("AssertCompute", obj) =>
    let e ← fromJsonSpanned obj Exp.fromJson
    return .AssertCompute e

  | ("AssertLean", obj) =>
    let e ← fromJsonSpanned obj Exp.fromJson
    return .AssertLean e

  | ("Assume", obj) =>
    let e ← fromJsonSpanned obj Exp.fromJson
    return .Assume e

  | ("Assign", obj) =>
    -- CC TODO? Dropped type information? Parse RHS first?
    let lhsObj ← obj.getObjValM "lhs"
    let (lhs, lhsTy) ← Dest.fromJson <| ← lhsObj.getObjValM "dest"
    let lhsIsInit ← lhsObj.getBoolUnderKeyM "is_init"
    let rhsObj ← obj.getObjValM "rhs"
    let rhs ← fromJsonSpanned rhsObj Exp.fromJson
    return .Assign lhs lhsTy rhs lhsIsInit

  | ("DeadEnd", obj) =>
    let stm ← fromJsonSpanned obj Stm.fromJson
    return .DeadEnd stm

  | ("Return", _) =>
    return .Return (Exp.Const <| Const.Bool true)

  | ("BreakOrContinue", _) =>
    throw "BreakOrContinue not yet implemented"

  | ("If", obj) =>
    -- The three parts of an if-statement are stored in a Verus tuple
    -- So this should be an array of three elements
    let ⟨arr, _⟩ ← obj.getArrWithSizeGeM 3
    let cond ← fromJsonSpanned arr[0] Exp.fromJson
    let branch₁ ← fromJsonSpanned arr[1] Stm.fromJson

    -- If the option in Verus is `Some`, it's an object; otherwise, it's `null`
    match arr[2] with
    | .null => return .If cond branch₁ none
    | x =>
      let branch₂ ← fromJsonSpanned x Stm.fromJson
      return .If cond branch₁ (some branch₂)

  | ("Loop", obj) =>
    throw "Loop not yet implemented"

  | ("OpenInvariant", obj) =>
    let stm ← fromJsonSpanned obj Stm.fromJson
    return .OpenInvariant stm

  | ("ClosureInner", obj) =>
    let stm ← fromJsonSpanned obj Stm.fromJson
    return .ClosureInner stm

  | ("Block", obj) =>
    -- We enforce that the block has at least one statement
    let ⟨arr, _⟩ ← obj.getArrWithSizeGeM 1
    let stmts ← arr.mapM (do Stm.fromJson <| ← xJsonFromSpanned ·)
    return .Block stmts.toList

  | s => throw s!"[Stm.fromJson?]: Expected one of many Stm options, got {s}"


--------------------------------------------------------------------------------

def fnParseArgs (j : Json) : VParser (List (Ident × Typ)) := do
  let varsJson ← j.getArrUnderKeyM "pars"

  /-
    For whatever reason, Verus decides to serialize empty parameter lists
    with a single element with the name `["no%param", "AirLocal"]`.
    We filter out those (or rather, that one) parameters here.
  -/
  let varsJson := varsJson.filter (fun obj =>
    match obj.getArrByPath? ["x", "name"] with
    | .ok arr =>
      if h : arr.size > 0 then
        match arr[0].getStr? with
        | .ok name => name != "no%param"
        | _ => true
      else
        false
    | _ => true)

  let vars ← restoreCurrentBoundVarsAfter <| varsJson.mapM (fun v => do
    let ⟨i, ty⟩ ← VarBinder.fromJson <| ← xJsonFromSpanned v
    -- We build up the bound variables as we go (in case of dependent typing)
    pushBoundVar i ty
    return (i, ty))
  return vars.toList


def SpecFn.fromJson (j : Json) : VParser SpecFn := do
  let name ← pathedNameFromNameJson j
  let args ← fnParseArgs j

  -- TODO: This ignores other info about the return value, (a `Par` in Verus)
  let returnType ← Typ.fromJson <| ← j.getObjValByPathM ["ret", "x", "typ"]
  setTyp returnType

  -- Parse the body as an expression
  -- For spec functions, this expression is stored in the axioms
  let bodyObj ← j.getObjValByPath ["axioms", "spec_axioms", "body_exp"]
  let bodyExp ← fromJsonSpanned bodyObj Exp.fromJson
  return SpecFn.mk name args returnType bodyExp


def ProofFn.fromJson (j : Json) : VParser ProofFn := do
  let name ← pathedNameFromNameJson j
  let args ← fnParseArgs j

  let requiresObj ← j.getArrByPathM ["exec_proof_check", "reqs"]
  let requires ← requiresObj.mapM (fromJsonSpanned · Exp.fromJson)

  -- TODO: This ignores other postcondition information
  let ensuresObj ← j.getArrByPathM ["exec_proof_check", "post_condition", "ens_exps"]
  let ensures ← ensuresObj.mapM (fromJsonSpanned · Exp.fromJson)

  -- Parse the body as an expression
  -- For proof functions, this expression is stored in the "exec_proof_check"
  let bodyObj ← j.getObjValByPathM ["exec_proof_check", "body", "x"]
  let bodyStm ← Stm.fromJson bodyObj
  return ProofFn.mk name args requires.toList ensures.toList bodyStm


def typeParamsFromJson (j : Json) : m (List Ident) := do
  let typeParamsArr ← j.getArrUnderKeyM "typ_params"
  return Array.toList <| ← typeParamsArr.mapM (fun _ => do
    -- TODO: These are going to be tuples, which probably get serialized as an array
    let ident := "implementMePlease"
    return ident)


def dataFieldsForVariantFromJson (j : Json) : m (Ident × Typ) := do
  let name ← j.getStrUnderKeyM "name"
  -- The other two fields are `Mode` and `Visibility`, which we ignore
  let ⟨fArr, _⟩ ← j.getArrUnderKeyWithSizeGeM "a" 3
  let typ ← Typ.fromJson fArr[0]
  return (name, typ)


def Struct.fromJson (j : Json) : VParser Struct := do
  let name ← pathedNameFromNameJson j "Path"
  let typeParams ← typeParamsFromJson j

  /-
    Parse the fields of the struct, under the singleton array "variants".

    The "variants" are stored in an array because Verus places structs
    and enums into the same `DatatypeX` object. For structs, there
    is exactly one variant in the array (of the same base name as the struct),
    with its fields stored in `fields` under the 0th entry of the outer array.
  -/
  let ⟨fieldsArr, _⟩ ← j.getArrUnderKeyWithSizeGeM "variants" 1
  let fieldsArr ← fieldsArr[0].getArrUnderKeyM "fields"
  let fields ← fieldsArr.mapM dataFieldsForVariantFromJson
  return Struct.mk name typeParams fields.toList


def EnumField.fromJson (j : Json) : m EnumField := do
  let name ← j.getStrUnderKeyM "name"
  let fieldsObj ← j.getArrUnderKeyM "fields"
  let fields ← fieldsObj.mapM dataFieldsForVariantFromJson
  return EnumField.mk name fields.toList


def Enum.fromJson (j : Json) : VParser Enum := do
  let name ← pathedNameFromNameJson j "Path"
  let typeParams ← typeParamsFromJson j

  /-
    The variants of an enum are stored directly in the `variants` field.
    We enforce that there should be at least one field.
  -/
  let ⟨fields, _⟩ ← j.getArrUnderKeyWithSizeGeM "variants" 1
  let fields ← fields.mapM EnumField.fromJson
  return Enum.mk name typeParams fields.toList


/--
  Calls the appropriate `fromJson` helper function based on the
  value under the `"dt_type"` key.
-/
def datatypeFromJson (j : Json) : VParser Decl := do
  let dtType ← j.getStrUnderKeyM "dt_type"
  match dtType with
  | "Enum" =>
    let enum ← Enum.fromJson j
    let enumAsDecl := Decl.enum enum
    return enumAsDecl
  | "Struct" =>
    let struct ← Struct.fromJson j
    let structAsDecl := Decl.struct struct
    return structAsDecl
  | _ => throw s!"Unsupported datatype: {dtType}"


/--
  Parses a JSON into a `Decl`, or throws an error.

  This function expects a top-level "wrapped" object, with appropriate
  metadata according to the type of `Decl` to be parsed.
  For example, a function-level SST is tagged with "FuncCheckSst"
  as well as the function's name.

  This function will try to parse an assert first, and if that fails,
  tries to parse a function.
-/
partial def Decl.fromJson (j : Json) : VParser Decl := do
  -- Each `Decl` JSON has a `DeclType`, which allows us
  -- to call the appropriate helper function
  let declObj ← j.getObjValM "x"
  let decl ←
    match ← j.getStrUnderKeyM "DeclType" with
    | "Datatype" => datatypeFromJson declObj
    | "SpecFn" => SpecFn.fromJson declObj
    | "ProofFn" => ProofFn.fromJson declObj
    | s => throw s!"Unexpected declaration type: {s}"
/-

  match ← j["Assert", "FuncCheckSst"] with
  | ("Assert", (obj : Json)) =>
    -- First, parse the data types (structs and enums)
    let dtObjs ← j.getArrUnderKeyM "Datatypes"
    let _ ← dtObjs.mapM (fun dtJson => do
      -- Skip n-ary tuples for now (Verus places them under "Tuple")
      -- TODO: Revisit this later (can you declare an enum named `Tuple`?)
      match Json.getObjValByPath dtJson ["name", "Tuple"] with
      | .ok _ => return ()
      | .error _ => datatypeFromJson dtJson
    )

    -- Parse the spec functions
    let specObjs ← j.getArrUnderKeyM "SpecFns"
    let _ ← specObjs.mapM SpecFn.fromJson

    -- Parse the body of the assert, now that we have the spec functions
    let exp ← Exp.fromJson obj
    let vmap ← getFreeVars

    let assertId ← j.getNatUnderKeyM "AssertId"
    return Decl.assertion <| Assertion.mk s!"assert_{assertId}" vmap.toList exp

  | ("FuncCheckSst", (obj : Json)) => do
    let funcNameJson : Json ← j.getObjVal? "FnName"
    let funcName : String ← Json.getStr? funcNameJson

    -- Parse the spec functions
    let specObjs ← j.getArrUnderKeyM "SpecFns"
    let _ ← specObjs.mapM SpecFn.fromJson

    -- Parse the preconditions (requires clauses)
    let reqsArr ← obj.getArrUnderKeyM "reqs"
    let reqs ← reqsArr.mapM (fun j => do
      let obj : Json ← xJsonFromSpanned j
      Exp.fromJson obj
    )

    -- Parse the post condition (ensures clause)
    let postCondition ← obj.getObjValM "post_condition"
    let ensArr ← postCondition.getArrUnderKeyM "ens_exps"
    let enss ← ensArr.mapM (fun j => do
      let obj : Json ← xJsonFromSpanned j
      Exp.fromJson obj
    )
    let vmap ← getFreeVars

    let decl := Decl.func <| FuncCheckSst.mk funcName reqs.toList enss.toList vmap.toList
    -- dbg_trace s!"decl.pp: {decl.pp}"
    return decl

  |  _ => throw "[Decl.fromJson?]: Expected one of { Assert, FuncCheckSst }, got something else" -/


partial def Decls.fromJson? (j : Json) : VParser (List Decl) := do
  -- top-level object is an array under a "decls" key
  let declsArr ← j.getArrUnderKeyM "decls"

  /-
    We monadically extract the `Decl` in each JSON object, from left to right.
    Note that we accumulate copies of these `Decls` in the state as we go
    in the hash maps, but we are assuming that the declarations are given
    to us in a good order, so there is no need to extract the objects
    back from the hash maps at the end.
  -/
  return Array.toList <| ← declsArr.mapM (fun j => do
    let decl ← Decl.fromJson j
    addDecl decl
    return decl)

partial def Decls.fromFile? (path : String) : IO (Except String (List Decl)) := do
  let jsonStr ← IO.FS.readFile path
  let json ← IO.ofExcept <| Json.parse jsonStr
  match Decls.fromJson? json default with
  | .ok decls _ => return .ok decls
  | .error e _ => return .error e

end VerusLean
