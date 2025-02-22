import VerusLean.Json
import VerusLean.VLIR.Defs
import VerusLean.Basic.Monad
import Lean

namespace VerusLean

open Lean

abbrev VMap := Std.HashMap Ident Typ
abbrev FMap := Std.HashMap Ident SpecFn

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
  freeVars : VMap := {}
  -- Acts like a stack?
  boundVars : List Ident := []
  fns : FMap := {}
deriving Inhabited

abbrev VParser := EStateM String ParserState

/-- Alias for `Except String`. The argument following `ExStr` is the return type. -/
abbrev ExStr := Except String

namespace VParser

open EStateM

def getTyp : VParser Typ :=
  do let st ← get; return st.expectedType

def setTyp (t : Typ) : VParser Unit :=
  modify fun st => { st with expectedType := t }

def getFreeVars : VParser VMap :=
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

def addSpecFn (fn : SpecFn) : VParser Unit :=
  modify fun st => { st with fns := st.fns.insert fn.name fn }

def setFns (fns : FMap) : VParser Unit :=
  modify fun st => { st with fns := fns }

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

def Typ.fromJson? (j : Json) : ExStr Typ := do
  match j.getStr? with
  | .ok "Bool" => return .Bool
  | .ok _ => throw "unsupported primitive type"
  | .error _ =>
    match ← j["Primitive", "Int", "ConstInt", "Array"] with
    | ("Primitive", obj) =>
      let t ← obj.getArr?
      match t.get? 0 with
      | some "Array" => throw "unsupported primitive type Array"
      -- .ok (Typ.Array Typ.Int)
      | some _ => throw "unsupported primitive type"
      | none => throw s!"error, json: {obj}"

    | ("Int", obj) =>
      -- First, we check if the the underlying string is "Int" for mathematical integers
      match obj.getStr? with
      | .ok "Int" => .ok Typ.Int
      | .ok "Nat" => .ok Typ.Nat
      | .ok _ => throw s!"unsupported Int object string: {obj}"
      | .error _ =>
        -- Now check if it is a fixed-width integer
        match obj.getFirstVal ["U", "I"] with
        | .error _ => throw s!"unsupported Int object: {obj}"
        | .ok ("U", obj) =>
          match obj.getNat? with
          | .ok width => .ok (Typ.UInt width)
          | .error e => throw s!"[Typ.fromJson?]: {e}"
        | .ok ("I", obj) =>
          match obj.getNat? with
          | .ok width => .ok (Typ.SInt width)
          | .error e => throw s!"[Typ.fromJson?]: {e}"
        | .ok _ => throw s!"unsupported Int object: {obj}"

    | _ => throw "unsupported primitive type"

/--
  Parses a "span" object and forwards the underlying data to a given function `fj`.

  Also adds the type annotation for the span to the state.
  This annotation should be added to the state's `HashMap` when encountering a `Var`.
-/
def fromJsonSpanned? {α : Type} (j : Json) (fj : Json → VParser α) : VParser α := do
  let typ ← Typ.fromJson? <| ← j.getObjVal? "typ"
  let x ← j.getObjVal? "x"
  setTyp typ
  fj x

def xJsonFromSpanned? (j : Json) : ExStr Json :=
  j.getObjVal? "x"

def widthFromJson? (j : Json) : ExStr Nat := do
  j.getNatUnderKey? "Width"

-- TODO: This probably needs to return a namespace (list?), rather than a single ident
def pathedNameFromJson? (j : Json) : ExStr Ident := do
  let pathed ← j.getObjValByPath ["path", "segments"]
  Json.getStr? <| ← Json.getArrVal? pathed 0

--------------------------------------------------------------------------------

def Mode.fromJson? (j : Json) : ExStr Mode := do
  match ← j.getStr? with
  | "Spec"  => return .Spec
  | "Proof" => return .Proof
  | "Exec"  => return .Exec
  | str => throw s!"[Mode.fromJson?]: Expected one of \{ Spec, Proof, Exec }, got {str}"

def Const.fromJson? (j : Json) : ExStr Const := do
  match ← j["Bool", "Int", "StrSlice", "Char"] with
  | ("Bool", v) => return Const.Bool <| ← v.getBool?
  | ("Int", v) =>
    -- Ints are serialized as an array, with the first element the sign enum
    -- and the second value is the data, an array of u64s.
    let ⟨arr, _⟩ ← v.getArrWithSizeGe? 2
    let s := arr[0]
    let n := arr[1]
    match ← s.getNat? with
    | 0 =>
      -- no sign
      -- CZ: according to bigint.rs, 0 is minus, 1 is no sign, 2 is plus?
      .ok (Const.Int 0)
    | 1 =>
      -- positive number
      -- TODO: Need some computation for the big int
      -- For now, take the first entry and move on
      let nArr ← n.getArr?
      let n := nArr.getD 0 (Json.num <| JsonNumber.fromNat 0)
      return Const.Int <| Int.ofNat <| ← n.getNat?
    | 2 =>
      -- negative number
      -- TODO: Need some computation for the big int
      -- For now, take the first entry and move on
      let nArr ← n.getArr?
      let n := nArr.getD 0 (Json.num <| JsonNumber.fromNat 0)
      return Const.Int <| -(Int.ofNat <| ← n.getNat?)
    | _ => throw "[Const.fromJson?]: Expected an Int sign of 0, 1, or 2"
  | ("StrSlice", _) => throw "not yet implemented"
  | ("Char", _) => throw "not yet implemented"
  | _ => throw "[Const.fromJson?]: Unexpected match"

def Bitwise.fromJson? (j : Json) : ExStr BitwiseOp :=
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
      let width ← widthFromJson? obj
      return .Shr width

    | ("Shl", obj) =>
      let ⟨arr, _⟩ ← obj.getArrWithSizeGe? 2
      let width ← widthFromJson? arr[0]
      return .Shl width (← arr[1].getBool?)

    | _ => throw s!"[Bitwise.fromJson?]: Expected one of \{ Shr, Shl }, got {j}"

def ArithOp.fromJson? (j : Json) : ExStr ArithOp := do
  match ← j.getStr? with
  | "Add"          => return .Add
  | "Sub"          => return .Sub
  | "Mul"          => return .Mul
  | "EuclideanDiv" => return .EuclideanDiv
  | "EuclideanMod" => return .EuclideanMod
  | s => throw s!"[ArithOp.fromJson?]: Expected one of Add, Sub, Mul, Div, Mod, got {s}"

def InequalityOp.fromJson? (j : Json) : ExStr InequalityOp := do
  match ← j.getStr? with
  | "Le" => return .Le
  | "Ge" => return .Ge
  | "Lt" => return .Lt
  | "Gt" => return .Gt
  | s => throw s!"[InequalityOp.fromJson?]: Expected one of \{ Le, Ge, Lt, Gt }, got {s}"

def UnaryOp.fromJson? (j : Json) : ExStr UnaryOp :=
  match j.getStr? with
  | .ok "Not"    => return .Not
  | .ok "BitNot" => throw "not yet implemented"
  | .ok "Clip"   => throw "not yet implemented"
  | .ok s => throw s!"[UnaryOp.fromJson?]: Expected one of \{ Not, BitNot, Clip }, got {s}"
  | .error _ => do
    -- Try seeing if "BitNot" has a width
    match j.getObjVal? "BitNot" with
    | .ok obj => do
      let width ← widthFromJson? obj
      return .BitNot width
    | .error _ =>
      -- Try seeing if it's a trigger
      match j.getObjVal? "Trigger" with
      | .error e => throw s!"[UnaryOp.fromJson?]: {e}"
      | .ok _ => return .Trigger

def BinaryOp.fromJson? (j : Json) : ExStr BinaryOp :=
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
    | ("Eq", obj)         => return .Eq (← Mode.fromJson? obj)
    | ("Inequality", obj) => return .Inequality (← InequalityOp.fromJson? obj)
    | ("Bitwise", obj) =>
      -- Object under "Bitwise" should be a two-element array with an op and a mode
      let ⟨arr, _⟩ ← obj.getArrWithSizeGe? 2
      let op ← Bitwise.fromJson? arr[0]
      let mode ← Mode.fromJson? arr[1]
      return .Bitwise op mode
    | ("Arith", obj) =>
      -- Object under "Arith" should be a two-element array with an op and a mode
      let ⟨arr, _⟩ ← obj.getArrWithSizeGe? 2
      let op ← ArithOp.fromJson? arr[0]
      let mode ← Mode.fromJson? arr[1]
      return .Arith op mode
    | _ => throw s!"[BinaryOp.fromJson?]: Expected one of \{ And, Or, Xor, Implies, Eq }, got something else: {j}"

def Quant.fromJson? (j : Json) : ExStr Quant := do
  match ← j.getObjVal? "quant" with
  | "Forall" => return .Forall
  | "Exists" => return .Exists
  | s => throw s!"[Quant.fromJson?]: Expected one of \{ Forall, Exists }, got {s}"

def CallFun.fromJson? (j : Json) : ExStr CallFun := do
  let obj ← j.getObjVal? "Fun"
  let ⟨arr, _⟩ ← obj.getArrWithSizeGe? 1
  return .Fun (← pathedNameFromJson? arr[0])

def Par.fromJson? (j : Json) : ExStr Par := do
  let obj ← j.getObjVal? "name"
  let ⟨arr, _⟩ ← obj.getArrWithSizeGe? 1
  let name ← arr[0].getStr?
  let typ ← Typ.fromJson? <| ← j.getObjVal? "typ"
  return Par.mk name typ

def VarBinder.typBinderFromJson? (j : Json) : ExStr (VarBinder Typ) := do
  let obj ← j.getObjVal? "name"
  let ⟨arr, _⟩ ← obj.getArrWithSizeGe? 1
  let nameObj := arr[0]
  let (name : String) ← nameObj.getStr?
  let typ ← Typ.fromJson? (← j.getObjVal? "a")
  return VarBinder.mk name typ

def VarBinder.typBindersFromJson? (j : Json) : ExStr (List (VarBinder Typ)) := do
  let (arr : _root_.Array Json) ← j.getArr?
  arr.toList.mapM VarBinder.typBinderFromJson?

mutual /- {Bind, Exp}.fromJson? -/

partial def Bind.fromJson? (j : Json) : VParser Bind := do
  let obj : Json ← xJsonFromSpanned? j
  match ← obj.getFirstVal ["Quant"] with
  | ("Quant", (q : Json)) =>
    let ⟨arr, _⟩ ← coeWithState <| q.getArrWithSizeGe? 4
    let q ← Quant.fromJson? arr[0]
    let binders ← VarBinder.typBindersFromJson? arr[1]
    return .Quant q binders
  | _ => throw "unexpected"

partial def Exp.fromJson? (j : Json) : VParser Exp := do
  -- Expect that exactly one of the enumerated options will be true
  match ← j["Const", "Var", "Unary", "Binary", "If", "Bind", "Call"] with
  | ("Const", obj) => do
    return Exp.Const <| ← Const.fromJson? obj
  | ("Var", obj) =>
    -- Verus gives us an array, where the first element is the identifier
    let (i : Json) ← obj.getArrVal? 0
    let (ident : Ident) ← i.getStr?
    addFreeVarIfNotBound ident
    return .Var ident
  | ("Unary", obj) =>
    -- A unary object should be an array with an op and a data element
    let ⟨arr, _⟩ ← coeWithState <| obj.getArrWithSizeGe? 2
    let op   ← UnaryOp.fromJson? arr[0]
    let data ← fromJsonSpanned? arr[1] Exp.fromJson?
    return .Unary op data
  | ("Binary", obj) =>
    -- A binary object should be an array with an op and two data elements
    let ⟨arr, _⟩ ← coeWithState <| obj.getArrWithSizeGe? 3
    let op    ← BinaryOp.fromJson? arr[0]
    let data₁ ← fromJsonSpanned? arr[1] Exp.fromJson?
    let data₂ ← fromJsonSpanned? arr[2] Exp.fromJson?
    return .Binary op data₁ data₂
  | ("If", obj) =>
    -- Should be an array with three expressions
    let ⟨arr, _⟩ ← coeWithState <| obj.getArrWithSizeGe? 3
    let cond    ← fromJsonSpanned? arr[0] Exp.fromJson?
    let branch₁ ← fromJsonSpanned? arr[1] Exp.fromJson?
    let branch₂ ← fromJsonSpanned? arr[2] Exp.fromJson?
    return .If cond branch₁ branch₂
  | ("Bind", obj) =>
    -- Should be an array with a bind and an expression
    let ⟨arr, _⟩ ← coeWithState <| obj.getArrWithSizeGe? 2
    let bind ← Bind.fromJson? arr[0]
    let exp ← withBoundVars bind.idents (fromJsonSpanned? arr[1] Exp.fromJson?)
    return .Bind bind exp
  | ("Call", obj) =>
    -- Should be an object with a function name and arguments
    -- The function's name is the 0th element, the arguments the 2nd element (an array)
    let ⟨arr, _⟩ ← coeWithState <| obj.getArrWithSizeGe? 3
    let callFn ← CallFun.fromJson? arr[0]
    let (expsJson : Array Json) ← arr[2].getArr?
    let exps : Array Exp ← expsJson.mapM (fromJsonSpanned? · Exp.fromJson?)
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

/-partial def Exp.fromFile? (path : String) : IO (Except String (Exp × VMap)) := do
  let jsonStr ← IO.FS.readFile path
  let json ← IO.ofExcept <| Json.parse jsonStr
  match Exp.fromJson? json with
  | .ok exp (_, types) => return .ok (exp, types)
  | .error e _ => return .error e -/

def getSpecFnName? (j : Json) : ExStr String := do
  let obj : Json ← j.getObjValByPath ["x", "name", "path", "segments"]
  Json.getStr? <| ← obj.getArrVal? 0

def SpecFn.fromJson? (j : Json) : ExStr SpecFn := do
  -- Parse the function name
  let name ← getSpecFnName? j

  -- Parse the arguments
  let varsJson ← (← j.getObjValByPath ["x", "pars"]).getArr?
  let vars ← varsJson.foldlM (init := Std.HashMap.empty) (fun m v => do
    let (var : Par) ← Par.fromJson? (← xJsonFromSpanned? v)
    return m.insert (Par.name var) (Par.typ var)
  )

  -- Parse the return type
  let returnTypeJson : Json ← j.getObjValByPath ["x", "ret"]
  let (ret : Par) ← Par.fromJson? (← xJsonFromSpanned? returnTypeJson)
  let returnType : Typ := ret.typ

  -- Parse the body as an expression
  let bodyObj : Json ← j.getObjValByPath ["x", "axioms", "spec_axioms", "body_exp"]
  match fromJsonSpanned? bodyObj Exp.fromJson? {
      expectedType := returnType
      freeVars := vars
      boundVars := ∅
      fns := Std.HashMap.empty -- CC: TODO this probably gets accumulated as we parse?
    } with
  | .ok body _ => return SpecFn.mk name vars returnType body
  | .error e _ => throw e

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
    -- Parse the spec functions
    let specObjs ← coeWithState <| Json.getArr? <| ← j.getObjVal? "SpecFns"
    let fnMap ← specObjs.foldlM (init := ∅) (fun m fnJson => do
      let fn ← SpecFn.fromJson? fnJson
      return Std.HashMap.insert m (SpecFn.name fn) fn
    )

    -- CC: TODO we probably shouldn't manually set the functions here (add them?)
    setFns fnMap

    -- Parse the body of the assert, now that we have the spec functions
    let exp ← Exp.fromJson? obj
    let vmap ← getFreeVars

    let assertId ← coeWithState <| j.getNatUnderKey? "AssertId"
    return Decl.assertion <| Assertion.mk s!"assert_{assertId}" vmap exp

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
    let fns := st.fns.values.map (Decl.specFn ·)
    return .ok (fns ++ [d])
  | .error e _ => return .error e

/-
def FuncCheckSST.fromJson? (j : Json) : Option FuncCheckSST :=
  -- Assume we have a top-level SST object, without a wrapping { "FuncCheckSST": ... }
  let reqs : Exps :=
    match j.getObjVal? "reqs" with
    | .error _ =>
     -/



end VerusLean
