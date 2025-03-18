import VerusLean.Json
import VerusLean.VLIR.Defs
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
  -- Acts like a stack?
  boundVars : List Ident := []
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

def getBoundVars : VParser (List Ident) :=
  do let st ← get; return st.boundVars

def addFreeVarWithTyp (var : Ident) (typ : Typ) : VParser Unit := do
  modify fun st => { st with
    freeVars := st.freeVars.insert var typ }

def addFreeVar (var : Ident) : VParser Unit := do
  addFreeVarWithTyp var (← getTyp)

/--
  Only adds a free variable if it is not already bound locally.
-/
def addFreeVarIfNotBound (var : Ident) : VParser Unit := do
  if !(← getBoundVars).contains var then
    addFreeVar var
  else
    return ()

def pushBoundVar (var : Ident) : VParser Unit :=
  modify fun st => { st with boundVars := var :: st.boundVars }

def pushBoundVars (vars : List Ident) : VParser Unit :=
  modify fun st => { st with boundVars := vars ++ st.boundVars }

def popBoundVar : VParser Unit :=
  modify fun st => { st with boundVars := st.boundVars.tail }

def popBoundVars (n : Nat) : VParser Unit :=
  modify fun st => { st with boundVars := st.boundVars.drop n }

def withBoundVars (vars : List Ident) (fn : VParser α) : VParser α := do
  pushBoundVars vars
  let a ← fn
  popBoundVars vars.length
  return a

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
  j.getNatUnderKeyM "Width"

-- TODO: This probably needs to return a namespace (list?), rather than a single ident
def pathedNameFromJson (j : Json) (pathKey : String := "path") : m Ident := do
  let pathed ← j.getObjValByPathM [pathKey, "segments"]
  Json.getStrM <| ← Json.getArrValM pathed 0

def pathedNameFromNameJson (j : Json) (pathKey : String := "path") : m Ident := do
  let nameObj ← j.getObjValM "name"
  pathedNameFromJson nameObj pathKey

def Typ.fromJson (j : Json) : m Typ := do
  match j.getStr? with
  | .ok "Bool" => return .Bool
  | .ok _ => throw "unsupported primitive type"
  | .error _ =>
    match ← j["Primitive", "Int", "ConstInt", "Array", "Datatype"] with
    | ("Primitive", obj) =>
      let t ← obj.getArrM
      match t.get? 0 with
      | some "Array" => throw "unsupported primitive type Array"
      -- .ok (Typ.Array Typ.Int)
      | some _ => throw "unsupported primitive type"
      | none => throw s!"error, json: {obj}"

    | ("Int", obj) =>
      -- First, we check if the the underlying string is "Int" for mathematical integers
      match obj.getStr? with
      | .ok "Int" => return .Int
      | .ok "Nat" => return .Nat
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
      let ⟨arr, _⟩ ← obj.getArrWithSizeGeM 3
      let name ← pathedNameFromJson arr[0] "Path"
      -- TODO: Ignoring parameters to the type for now
      let params := []
      return .Struct name params

    | _ => throw "unsupported primitive type"

/--
  Parses a "span" object and forwards the underlying data to a given function `fj`.

  Also adds the type annotation for the span to the state.
  This annotation should be added to the state's `HashMap` when encountering a `Var`.
-/
def fromJsonSpanned {α : Type} (j : Json) (fj : Json → VParser α) : VParser α := do
  let typ ← Typ.fromJson <| ← j.getObjVal? "typ"
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
  | ("StrSlice", _) => throw "not yet implemented"
  | ("Char", _) => throw "not yet implemented"
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
  | .ok "BitNot" => throw "not yet implemented"
  | .ok "Clip"   => throw "not yet implemented"
  | .ok s => throw s!"[UnaryOp.fromJson?]: Expected one of \{ Not, BitNot, Clip }, got {s}"
  | .error _ =>
    -- Try seeing if "BitNot" has a width
    match ← j["BitNot", "Trigger"] with
    | ("BitNot", obj) =>
      let width ← widthFromJson obj
      return .BitNot width
    | ("Trigger", _) => return .Trigger
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
  match ← j["Field", "IsVariant"] with
  | ("Field", obj) =>
    -- TODO: Skipping data type
    let variant ← obj.getStrUnderKeyM "variant"
    let field ← obj.getStrUnderKeyM "field"
    return .Proj variant field
  | ("IsVariant", obj) =>
    -- TODO: Skipping data type
    let variant ← obj.getStrUnderKeyM "variant"
    return .IsVariant variant "hello"
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


mutual /- {Bind, Exp}.fromJson? -/

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
  match ← j["Const", "Var", "Ctor", "Unary", "UnaryOpr", "Binary", "If", "Bind", "Call"] with
  | ("Const", obj) => do
    return Exp.Const <| ← Const.fromJson obj

  | ("Var", obj) =>
    -- Verus gives us an array, where the first element is the identifier
    let i ← obj.getArrValM 0
    let ident ← i.getStr?
    addFreeVarIfNotBound ident
    return .Var ident

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
      -- TODO: Might want to use `fromJsonSpanned?` to set the type?
      let a ← Json.getObjValM fObj "a"
      let x ← Json.getObjValM a "x"
      let exp ← Exp.fromJson x
      return (name, exp)
    )

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
    return .Unary op data

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

  | ("Call", obj) =>
    -- Should be an object with a function name and arguments
    -- The function's name is the 0th element, the arguments the 2nd element (an array)
    let ⟨arr, _⟩ ← obj.getArrWithSizeGeM 3
    let callFn ← CallFun.fromJson arr[0]
    let expsJson ← arr[2].getArrM
    let exps : Array Exp ← expsJson.mapM (fromJsonSpanned · Exp.fromJson)
    return .Call callFn [] exps.toList

  | s => throw s!"[ExpX.fromJson?]: Expected one of \{ Const, Var, Unary, Binary, If }, got {s}"

  -- | .ok ("Array", obj) =>
  --   -- Should be an array of expressions
  --   match obj.getArr? with
  --   | .error e => throw s!"[ExpX.fromJson?]: {e}"
  --   | .ok arr => do
  --     let elems ← arr.mapM (fun i => fromJsonSpanned? i ExpX.fromJson?)
  --     return ExpX.ArrayLiteral elems

end /- mutual -/

--------------------------------------------------------------------------------

def getSpecFnName (j : Json) : m String := do
  let nameObj ← j.getObjValByPathM ["name"]
  pathedNameFromJson nameObj

def SpecFn.fromJson (j : Json) : VParser Unit := do
  -- Parse the function name
  let name ← getSpecFnName j

  -- Parse the arguments
  let varsJson ← j.getArrUnderKeyM "pars"
  let vars ← coeWithState <| varsJson.foldlM (init := ∅) (fun vars v => do
    let ⟨i, ty⟩ ← VarBinder.fromJson <| ← xJsonFromSpanned v
    return Std.HashMap.insert vars i ty
  )

  -- Parse the return type
  let returnTypeJson : Json ← j.getObjValM "ret"
  let ⟨_, ty⟩ ← VarBinder.fromJson <| ← xJsonFromSpanned returnTypeJson
  let returnType : Typ := ty

  -- Parse the body as an expression
  let bodyObj : Json ← j.getObjValByPath ["axioms", "spec_axioms", "body_exp"]
  match fromJsonSpanned bodyObj Exp.fromJson {
      expectedType := returnType
      freeVars := vars
      boundVars := ∅
      decls := ∅ -- CC: TODO this probably gets accumulated as we parse?
    } with
  | .error e _ => throw e
  | .ok body _ => do
    addDecl <| SpecFn.mk name vars returnType body


def Struct.fromJson (j : Json) : VParser Unit := do
  let name ← pathedNameFromNameJson j "Path"

  /-
    The variants are stored in an array because Verus places structs
    and enums into the same `DatatypeX` object. For structs, there
    is going to be exactly one variant in the array, with its fields
    stored in the `fields` field under the 0th entry of the outer array.
  -/
  let ⟨fieldsArr, _⟩ ← j.getArrUnderKeyWithSizeGeM "variants" 1
  let fieldsArr ← fieldsArr[0].getArrUnderKeyM "fields"
  let fields ← fieldsArr.mapM (fun f => do
    let name ← f.getStrUnderKeyM "name"
    let ⟨fArr, _⟩ ← f.getArrUnderKeyWithSizeGeM "a" 3
    let typ ← Typ.fromJson fArr[0]
    return (name, typ))
  addDecl <| Struct.mk name [] fields.toList


def EnumField.fromJson (j : Json) : m EnumField := do
  let name ← j.getStrUnderKeyM "name"
  let fieldsObj ← j.getArrUnderKeyM "fields"
  let fields ← fieldsObj.mapM (fun f => do
    let name ← f.getStrUnderKeyM "name"
    -- CC: TODO for whatever reason, the type is stored in an array
    -- CC: We default to taking the first type in this array
    let ⟨tyArr, _⟩ ← f.getArrUnderKeyWithSizeGeM "a" 1
    let ty ← Typ.fromJson tyArr[0]
    return (name, ty))
  return EnumField.mk name fields.toList


def Enum.fromJson (j : Json) : VParser Unit := do
  let name ← pathedNameFromNameJson j "Path"

  /-
    The variants of an enum are stored directly in the `variants` field.
    We enforce that there should be at least one field.
  -/
  let ⟨fields, _⟩ ← j.getArrUnderKeyWithSizeGeM "variants" 1
  let fields ← fields.mapM EnumField.fromJson
  addDecl <| Enum.mk name fields.toList


/--
  Calls the appropriate `fromJson` helper function based on the
  value under the `"dt_type"` key.
-/
def datatypeFromJson (j : Json) : VParser Unit := do
  let dtType ← j.getStrUnderKeyM "dt_type"
  match dtType with
  | "Enum" => Enum.fromJson j
  | "Struct" => Struct.fromJson j
  | _ => throw s!"Unsupported datatype: {dtType}"


/--
  Parses a JSON into a `Decl`, or throws an error.

  This function expects a top-level "wrapped" object, with appropriate
  metadata according to the type of `Decl` to be parsed.
  For example, a function-level SST is tagged with "FuncCheckSST"
  as well as the function's name.

  This function will try to parse an assert first, and if that fails,
  tries to parse a function.
-/
partial def Decl.fromJson? (j : Json) : VParser Decl := do
  match ← j["Assert", "FuncCheckSST"] with
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

  | ("FuncCheckSST", _) => do

    let funcNameJson : Json ← j.getObjVal? "FnName"
    let funcName : String ← Json.getStr? funcNameJson

    throw s!"function {funcName} encountered: not yet implemented"

  |  _ => throw "[Decl.fromJson?]: Expected one of { Assert, FuncCheckSST }, got something else"

partial def Decls.fromFile? (path : String) : IO (Except String (List Decl)) := do
  let jsonStr ← IO.FS.readFile path
  let json ← IO.ofExcept <| Json.parse jsonStr
  match Decl.fromJson? json default with
  | .ok d st =>
    let decls := st.decls.values
    let dts := decls.filter (fun | .struct _ | .enum _ => true | _ => false)
    let fns := decls.filter (fun | .specFn _ => true | _ => false)
    return .ok (dts ++ fns ++ [d])
  | .error e _ => return .error e

end VerusLean
