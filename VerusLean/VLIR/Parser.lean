import VerusLean.Json
import VerusLean.VLIR.Defs
import VerusLean.Basic.Monad
import Lean

namespace VerusLean

open Lean

abbrev VMap := Std.HashMap String Typ

/--
  The parsing monad for Verus JSONs,
  which includes a state with a map from variable names to types.

  All exceptions are strings.

  The state is a mapping from variable names to their (primitive) types.
  For example, an unsigned integer of width 32 (in Rust, a `u32`) would be `UInt 32`.

  TODO: handle shadowing
-/
abbrev VParser := EStateM String (Typ × VMap)

def Typ.fromJson? (j : Json) : VParser Typ :=
  -- dbg_trace s!"[Typ.fromJson?]: {j}"
  match j.getStr? with
  | .ok "Bool" => .ok Typ.Bool
  | .ok _ => throw "unsupported primitive type"
  | .error _ =>
    match j.getFirstVal? ["Int", "Primitive", "ConstInt", "Array"] with
    | .error e => throw s!"[Typ.fromJson? 1]: {e}, json is {j}"
    | .ok ("Primitive", obj) =>
      match obj.getArr? with
      | .ok t => match t.get? 0 with
        | some "Array" => throw "unsupported primitive type Array"
        -- .ok (Typ.Array Typ.Int)
        | some _ => throw "unsupported primitive type"
        | none => throw s!"error, json: {obj}"
        -- match Typ.fromJson? t with
          -- | .ok Typ.Bool => .ok Typ.Bool
          -- | .error e => throw s!"[Typ.fromJson? 3]: {e}"
      | .error e => throw s!"{e}, json: {obj}"
    -- | .ok ("Array", obj) => throw "Array ... not yet implemented"
    -- | .ok ("ConstInt", obj) => throw "ConstInt not yet implemented"
    | .ok ("Int", obj) =>
      -- First, we check if the the underlying string is "Int" for mathematical integers
      match obj.getStr? with
      | .ok "Int" => .ok Typ.Int
      | .ok "Nat" => .ok Typ.Nat
      | .ok _ => throw s!"unsupported Int object string: {obj}"
      | .error _ =>
        -- Now check if it is a fixed-width integer
        match obj.getFirstVal? ["U", "I"] with
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

    | .ok _ => throw "unsupported primitive type"

/--
  Parses a "span" object and forwards the underlying data to a given function `fj`.

  Also adds the type annotation for the span to the state.
  This annotation should be added to the state's `HashMap` when encountering a `Var`.
-/
def fromJsonSpanned? {α : Type} (j : Json) (fj : Json → VParser α) : VParser α :=
  match j.getObjVal? "span" with
  | .error e => throw s!"[fromJsonSpanned?]: no span found: {e}"
  | .ok _ => do
    match j.getObjVal? "typ" with
    | .error _ => throw "[fromJsonSpanned?]: no typ found"
    | .ok obj => do
      let typ ← Typ.fromJson? obj
      match j.getObjVal? "x" with
      | .error e => throw s!"[fromJsonSpanned?]: no x found: {e}"
      | .ok x => (fun (_, map) => fj x (typ, map))

def widthFromJson? (j : Json) : VParser Nat :=
  match j.getObjVal? "Width" with
  | .error e => throw s!"[widthFromJson]: {e}"
  | .ok w =>
    match w.getNat? with
    | .ok width => .ok width
    | .error e => throw s!"[widthFromJson]: {e}"

def Mode.fromJson? (j : Json) : VParser Mode :=
  match j.getStr? with
  | .ok "Spec" => .ok Mode.Spec
  | .ok "Proof" => .ok Mode.Proof
  | .ok "Exec" => .ok Mode.Exec
  | .ok str => throw s!"[Mode.fromJson?]: Expected one of \{ Spec, Proof, Exec }, got {str}"
  | .error e => throw s!"[Mode.fromJson?]: {e}"

def Const.fromJson? (j : Json) : VParser Const :=
  match j.getFirstVal? ["Bool", "Int", "StrSlice", "Char"] with
  | .error _ => throw "[Const.fromJson?] Expected a JSON object under one of the const keys"
  | .ok ("Bool", v) =>
    match v.getBool? with
    | .ok b => .ok (Const.Bool b)
    | .error e => throw s!"[Const.fromJson?]: {e}"
  | .ok ("Int", v) =>
    -- Ints are serialized as an array, with the first element the sign enum
    -- and the second value is the data, an array of u64s.
    match v.getArr? with
    | .error e => throw s!"[Const.fromJson?]: {e}"
    | .ok arr =>
      if h : arr.size < 2 then
        throw s!"[Const.fromJson?]: Expected an array of size at least 2, got {arr.size}"
      else
        match arr.get 0 (by omega), arr.get 1 (by omega) with
        | s, n =>
          match s.getNat? with
          | .error e => throw s!"[Const.fromJson?]: {e}"
          | .ok 0 => -- no sign -- CZ: according to bigint.rs, 0 is minus, 1 is no sign, 2 is plus?
            .ok (Const.Int 0)
          | .ok 1 => -- positive number
            match n.getArr? with
            | .error e => throw s!"[Const.fromJson?]: {e}"
            | .ok n =>
              -- TODO: Need some computation for the big int
              -- For now, take the first entry and move on
              let n := n.getD 0 (Json.num <| JsonNumber.fromNat 0)
              match n.getNat? with
              | .ok i => .ok (Const.Int i)
              | .error e => throw s!"[Const.fromJson?]: {e}"
          | .ok 2 => -- negative number
            match n.getArr? with
            | .error e => throw s!"[Const.fromJson?]: {e}"
            | .ok n =>
              -- TODO: Need some computation for the big int
              -- For now, take the first entry and move on
              let n := n.getD 0 (Json.num <| JsonNumber.fromNat 0)
              match n.getNat? with
              | .ok i => .ok (Const.Int <| -(Int.ofNat i))
              | .error e => throw s!"[Const.fromJson?]: {e}"
          | .ok _ => throw "[Const.fromJson?]: Expected an Int sign of 0, 1, or 2"
  | .ok ("StrSlice", _) => throw "not yet implemented"
  | .ok ("Char", _) => throw "not yet implemented"
  | _ => throw "[Const.fromJson?]: Unexpected match"

def Bitwise.fromJson? (j : Json) : VParser BitwiseOp :=
  match j.getStr? with
  | .ok "BitXor" => .ok BitwiseOp.BitXor
  | .ok "BitAnd" => .ok BitwiseOp.BitAnd
  | .ok "BitOr" => .ok BitwiseOp.BitOr
  | .ok str => throw s!"[Bitwise.fromJson?]: Expected one of \{ BitXor, BitAnd, BitOr }, got {str}"
  | .error _ =>
    -- Try one of the shifts instead
    -- They are objects that store the width (and sign extension)
    match j.getFirstVal? ["Shr", "Shl"] with
    | .ok ("Shr", obj) => do
      let width ← widthFromJson? obj
      return BitwiseOp.Shr width

    | .ok ("Shl", obj) =>
      match obj.getArr? with
      | .error e => throw s!"[Bitwise.fromJson?]: {e}"
      | .ok arr => do
        if h : arr.size < 2 then
          throw s!"[Bitwise.fromJson?]: Expected an array of size at least 2, got {arr.size}"
        else
          let widthObj := arr.get 0 (by omega)
          let signExtend := arr.get 1 (by omega)
          let width ← widthFromJson? widthObj
          match signExtend.getBool? with
          | .ok signExtend => .ok (BitwiseOp.Shl width signExtend)
          | .error e => throw s!"[Bitwise.fromJson?]: {e}"

    | _ => throw s!"[Bitwise.fromJson?]: Expected one of \{ Shr, Shl }, got {j}"

def ArithOp.fromJson? (j : Json) : VParser ArithOp :=
  match j.getStr? with
  | .ok "Add" => .ok ArithOp.Add
  | .ok "Sub" => .ok ArithOp.Sub
  | .ok "Mul" => .ok ArithOp.Mul
  | .ok "EuclideanDiv" => .ok ArithOp.EuclideanDiv
  | .ok "EuclideanMod" => .ok ArithOp.EuclideanMod
  | .ok str => throw s!"[ArithOp.fromJson?]: Expected one of Add, Sub, Mul, Div, Mod, got {str}"
  | .error e => throw s!"[ArithOp.fromJson?]: {e}"

def InequalityOp.fromJson? (j : Json) : VParser InequalityOp :=
  match j.getStr? with
  | .ok "Le" => .ok InequalityOp.Le
  | .ok "Ge" => .ok InequalityOp.Ge
  | .ok "Lt" => .ok InequalityOp.Lt
  | .ok "Gt" => .ok InequalityOp.Gt
  | .ok s => throw s!"[InequalityOp.fromJson?]: Expected one of \{ Le, Ge, Lt, Gt }, got {s}"
  | .error e => throw s!"[InequalityOp.fromJson?]: {e}"

def UnaryOp.fromJson? (j : Json) : VParser UnaryOp :=
  -- dbg_trace s!"[UnaryOp.fromJson?]: {j}"
  match j.getStr? with
  | .ok "Not" => .ok UnaryOp.Not
  | .ok "BitNot" => throw "not yet implemented"
  | .ok "Clip" => throw "not yet implemented"
  | .ok s => throw s!"[UnaryOp.fromJson?]: Expected one of \{ Not, BitNot, Clip }, got {s}"
  | .error _ =>
    -- Try seeing if "BitNot" has a width
    match j.getObjVal? "BitNot" with
    | .ok obj => do
      let width ← widthFromJson? obj
      return UnaryOp.BitNot width
    | .error e =>
      -- throw s!"[UnaryOp.fromJson?]: {e}"
      -- Try seeing if it's a trigger
      match j.getObjVal? "Trigger" with
      | .error e => throw s!"[UnaryOp.fromJson?]: {e}"
      | .ok obj => .ok UnaryOp.Trigger
        -- match j.getArrVal? 1 with
        -- | .error e => throw s!"expected an array of size 2: {e}, with json {j}"
        -- | .ok obj => do
        --   let obj ← fromJsonSpanned? obj ExpX.fromJson?
        --   return UnaryOp.Trigger obj

def BinaryOp.fromJson? (j : Json) : VParser BinaryOp :=
  -- Most are single strings, but Eq has a mode attached, etc.
  match j.getStr? with
  | .ok "And" => .ok BinaryOp.And
  | .ok "Or" => .ok BinaryOp.Or
  | .ok "Xor" => .ok BinaryOp.Xor
  | .ok "Implies" => .ok BinaryOp.Implies
  | .ok "Ne" => .ok BinaryOp.Ne
  | .ok s => throw s!"[BinaryOp.fromJson?]: Expected one of \{ And, Or, Xor, Implies, Ne }, got {s}"
  | .error _ =>
    -- Try one of the object ops instead
    match j.getFirstVal? ["Eq", "Inequality", "Bitwise", "Arith"] with
    | .ok ("Eq", obj) => do return BinaryOp.Eq (← Mode.fromJson? obj)
    | .ok ("Inequality", obj) => do return BinaryOp.Inequality (← InequalityOp.fromJson? obj)
    | .ok ("Bitwise", obj) =>
      -- Object under "Bitwise" should be a two-element array with an op and a mode
      match obj.getArr? with
      | .error e => throw s!"[BinaryOp.fromJson?]: {e}"
      | .ok arr => do
        if h : arr.size < 2 then
          throw s!"[BinaryOp.fromJson?]: Expected an array of size at least 2, got {arr.size}"
        else
          let op := arr.get 0 (by omega)
          let mode := arr.get 1 (by omega)
          let op ← Bitwise.fromJson? op
          let mode ← Mode.fromJson? mode
          return BinaryOp.Bitwise op mode
    | .ok ("Arith", obj) =>
      -- Object under "Arith" should be a two-element array with an op and a mode
      match obj.getArr? with
      | .error e => throw s!"[BinaryOp.fromJson?]: {e}"
      | .ok arr => do
        if h : arr.size < 2 then
          throw s!"[BinaryOp.fromJson?]: Expected an array of size at least 2, got {arr.size}"
        else
          let op := arr.get 0 (by omega)
          let mode := arr.get 1 (by omega)
          let op ← ArithOp.fromJson? op
          let mode ← Mode.fromJson? mode
          return BinaryOp.Arith op mode
    | _ => throw s!"[BinaryOp.fromJson?]: Expected one of \{ And, Or, Xor, Implies, Eq }, got something else: {j}"

def Quant.fromJson? (j : Json) : VParser Quant :=
  match j.getObjVal? "quant" with
  | .ok "Forall" => .ok Quant.Forall
  | .ok "Exists" => .ok Quant.Exists
  | .ok s => throw s!"[Quant.fromJson?]: Expected one of \{ Forall, Exists }, got {s}"
  | .error e => throw s!"[Quant.fromJson?]: {e}, with json {j}"

def varBinderFromJson? (j : Json) : VParser (String × Typ) :=
  match j.getObjVal? "name" with
  | .error e => throw s!"[varBinderFromJson?]: no name found: {e}"
  | .ok obj => do
    match obj.getArr? with
    | .error e => throw s!"[varBinderFromJson?]: {e}"
    | .ok arr => do
      if h : arr.size < 1 then
        throw s!"[varBinderFromJson?]: Expected an array of size at least 1, got {arr.size}"
      else
        let name := arr.get 0 (by omega)
        match name.getStr? with
        | .ok name =>
          match j.getObjVal? "a" with
          | .error e => throw s!"[varBinderFromJson?]: no type found: {e}"
          | .ok typ => do
            -- dbg_trace s!"[varBinderFromJson?]: name={name}, typ={typ}"
            let typ ← Typ.fromJson? typ
            return (name, typ)
          -- throw s!"[varBinderFromJson?]: {name} not yet implemented"
          -- let typ ← Typ.fromJson? typ
          -- return (name, typ)
        | .error e => throw s!"[varBinderFromJson?]: {e}"

def VarBinders.fromJson? (j : Json) : VParser VarBinders :=
  match j.getArr? with
  | .error e => throw s!"[VarBinders.fromJson?]: {e}"
  | .ok arr => arr.toList.mapM varBinderFromJson?

def Bind.fromJson? (j : Json) : VParser Bind :=
  match j.getObjVal? "span" with
  | .error e => throw s!"[Bind.fromJson?]: no span found: {e}"
  | .ok _ =>
    match j.getObjVal? "x" with
    | .error e => throw s!"[Bind.fromJson?]: no x found: {e}"
    | .ok obj =>
      match obj.getObjVal? "Quant" with
      | .error e => throw s!"[Bind.fromJson?]: {e}"
      | .ok arr =>
        match arr.getArr? with
        | .error e => throw s!"[Bind.fromJson?]: {e}"
        | .ok arr => do
          if h : arr.size < 4 then
            throw s!"[Bind.fromJson?]: Expected an array of size at least 4, got {arr.size}"
          else
            let q := arr.get 0 (by omega)
            let binders := arr.get 1 (by omega)
            -- let trigs := arr.get 2 (by omega)
            -- let AssertByLocals := arr.get 3 (by omega)
            let q ← Quant.fromJson? q
            let binders ← VarBinders.fromJson? binders
            return Bind.Quant q binders

partial def ExpX.fromJson? (j : Json) : VParser ExpX :=
  -- Expect that exactly one of the enumerated options will be true
  match j.getFirstVal? ["Const", "Var", "Unary", "Binary", "If", "Array", "Bind"] with
  | .ok ("Const", obj) => do
    let c ← Const.fromJson? obj
    return ExpX.Const c
  | .ok ("Var", obj) =>
    -- Verus gives us an array, where the first element is the identifier
    match obj.getArrVal? 0 with
    | .error e => throw s!"[ExpX.fromJson?]: {e}"
    | .ok i =>
      match i.getStr? with
      | .error e => throw s!"[ExpX.fromJson?]: {e}"
      | .ok ident =>
        -- Add the variable to the state's map
        (fun (typ, map) =>
          let map := map.insert ident typ
          .ok (ExpX.Var ident) (typ, map))
  | .ok ("Unary", obj) =>
    -- A unary object should be an array with an op and a data element
    match obj.getArr? with
    | .error e => throw s!"[ExpX.fromJson?]: {e}"
    | .ok arr => do
      if h : arr.size < 2 then
        throw s!"[ExpX.fromJson?]: Expected an array of size at least 2, got {arr.size}"
      else
        let op := arr.get 0 (by omega)
        let data := arr.get 1 (by omega)
        let op ← UnaryOp.fromJson? op
        let data ← fromJsonSpanned? data ExpX.fromJson?
        return ExpX.Unary op data
  | .ok ("Binary", obj) =>
    -- A binary object should be an array with an op and two data elements
    match obj.getArr? with
    | .error e => throw s!"[ExpX.fromJson?]: {e}"
    | .ok arr => do
      if h : arr.size < 3 then
        throw s!"[ExpX.fromJson?]: Expected an array of size at least 3, got {arr.size}"
      else
        let op := arr.get 0 (by omega)
        let data₁ := arr.get 1 (by omega)
        let data₂ := arr.get 2 (by omega)
        let op ← BinaryOp.fromJson? op
        let data₁ ← fromJsonSpanned? data₁ ExpX.fromJson?
        let data₂ ← fromJsonSpanned? data₂ ExpX.fromJson?
        return ExpX.Binary op data₁ data₂
  | .ok ("If", obj) =>
    -- Should be an array with three expressions
    match obj.getArr? with
    | .error e => throw s!"[ExpX.fromJson?]: {e}"
    | .ok arr => do
      if h : arr.size < 3 then
        throw s!"[ExpX.fromJson?]: Expected an array of size at least 3, got {arr.size}"
      else
        let cond := arr.get 0 (by omega)
        let branch₁ := arr.get 1 (by omega)
        let branch₂ := arr.get 2 (by omega)
        let cond ← fromJsonSpanned? cond ExpX.fromJson?
        let branch₁ ← fromJsonSpanned? branch₁ ExpX.fromJson?
        let branch₂ ← fromJsonSpanned? branch₂ ExpX.fromJson?
        return ExpX.If cond branch₁ branch₂
  -- | .ok ("Array", obj) =>
  --   -- Should be an array of expressions
  --   match obj.getArr? with
  --   | .error e => throw s!"[ExpX.fromJson?]: {e}"
  --   | .ok arr => do
  --     let elems ← arr.mapM (fun i => fromJsonSpanned? i ExpX.fromJson?)
  --     return ExpX.ArrayLiteral elems
  | .ok ("Bind", obj) =>
    -- Should be an array with a bind and an expression
    match obj.getArr? with
    | .error e => throw s!"[ExpX.fromJson?]: {e}"
    | .ok arr => do
      if h : arr.size < 2 then
        throw s!"[ExpX.fromJson?]: Expected an array of size at least 2, got {arr.size}"
      else
        let bind := arr.get 0 (by omega)
        let exp := arr.get 1 (by omega)
        -- throw s!"bind: {bind}, exp: {exp}"
        let bind ← Bind.fromJson? bind
        let exp ← fromJsonSpanned? exp ExpX.fromJson?
        return ExpX.Bind bind exp
  | .ok _ => throw "[ExpX.fromJson?]: Expected one of { Const, Var, Unary, Binary, If }, got something else"
  | .error e => throw s!"[ExpX.fromJson?]: {e}"

partial def ExpX.fromFile? (path : String) : IO (Except String (ExpX × VMap)) := do
  let jsonStr ← IO.FS.readFile path
  let json ← IO.ofExcept <| Json.parse jsonStr
  match ExpX.fromJson? json (.Bool, Std.HashMap.empty) with
  | .ok exp (_, types) => return .ok (exp, types)
  | .error e _ => return .error e

/--
  Parses a JSON into a `Decl`, or throws an error.

  This function expects a top-level "wrapped" object, with appropriate
  metadata according to the type of `Decl` to be parsed.
  For example, a function-level SST is tagged with "FuncCheckSST"
  as well as the function's name.

  This function will try to parse an assert first, and if that fails,
  tries to parse a function.
-/
partial def Decl.fromJson? (j : Json) : VParser Decl :=
  match j.getFirstVal? ["Assert", "FuncCheckSST"] with
  | .ok ("Assert", obj) => do
    let exp ← ExpX.fromJson? obj
    let (_, vmap) ← get

    let assertIdJson ← j.getObjVal? "AssertId"
    let assertId : Nat ← Json.getNat? assertIdJson
    return Decl.assertion s!"assert_{assertId}" vmap exp

  | .ok ("FuncCheckSST", _) => do

    let funcNameJson : Json ← j.getObjVal? "FnName"
    let funcName : String ← Json.getStr? funcNameJson

    throw s!"function {funcName} encountered: not yet implemented"

  | .ok _ => throw "[Decl.fromJson?]: Expected one of { Assert, FuncCheckSST }, got something else"
  | .error e => throw s!"[Decl.fromJson?]: {e}"

partial def Decl.fromFile? (path : String) : IO (Except String Decl) := do
  let jsonStr ← IO.FS.readFile path
  let json ← IO.ofExcept <| Json.parse jsonStr
  match Decl.fromJson? json (.Bool, Std.HashMap.empty) with
  | .ok decl _ => return .ok decl
  | .error e _ => return .error e

/-
def FuncCheckSST.fromJson? (j : Json) : Option FuncCheckSST :=
  -- Assume we have a top-level SST object, without a wrapping { "FuncCheckSST": ... }
  let reqs : Exps :=
    match j.getObjVal? "reqs" with
    | .error _ =>
     -/



end VerusLean
