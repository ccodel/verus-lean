import Lean.Data.Json

namespace Lean.Json

/- Monadic verisons of standard Json functions. Helps when working in the `StateM` monad. -/

variable {m : Type → Type} [Monad m] [MonadExceptOf String m]

def getObjValM (j : Json) (k : String) : m Json :=
  match j.getObjVal? k with
  | .ok v => pure v
  | .error e => throw s!"{e}, got {j}"

def getArrM (j : Json) : m (Array Json) :=
  match j.getArr? with
  | .ok v => pure v
  | .error e => throw s!"{e}, got {j}"

def getStrM (j : Json) : m String :=
  match j.getStr? with
  | .ok v => pure v
  | .error e => throw s!"{e}, got {j}"

def getNatM (j : Json) : m Nat :=
  match j.getNat? with
  | .ok v => pure v
  | .error e => throw s!"{e}, got {j}"

def getBoolM (j : Json) : m Bool :=
  match j.getBool? with
  | .ok v => pure v
  | .error e => throw s!"{e}, got {j}"

def getArrValM (j : Json) (i : Nat) : m Json :=
  match j.getArrVal? i with
  | .ok v => pure v
  | .error e => throw s!"{e}, got {j}"

def isObject (j : Json) : Bool :=
  match j with
  | Json.obj _ => true
  | _ => false

def getArrUnderKey? (j : Json) (key : String) : Except String (Array Json) :=
  match j.getObjVal? key with
  | .ok (Json.arr v) => return v
  | .ok _ => throw s!"expected array under key {key}"
  | .error e => throw s!"{e} in {j}"

def getArrUnderKeyM (j : Json) (key : String) : m (Array Json) := do
  match j.getObjVal? key with
  | .ok (Json.arr v) => return v
  | .ok _ => throw s!"expected array under key {key}"
  | .error e => throw s!"{e} in {j}"

def getStrUnderKey? (j : Json) (key : String) : Except String String :=
  match j.getObjVal? key with
  | .ok (Json.str v) => return v
  | .ok _ => throw s!"expected string under key {key}"
  | .error e => throw e

def getStrUnderKeyM (j : Json) (key : String) : m String := do
  Json.getStrM <| ← j.getObjValM key

def getNatUnderKey? (j : Json) (key : String) : Except String Nat :=
  match j.getObjVal? key with
  | .ok j => j.getNat?
  | .error e => throw e

def getNatUnderKeyM (j : Json) (key : String) : m Nat := do
  Json.getNatM <| ← j.getObjValM key

def getBoolUnderKey? (j : Json) (key : String) : Except String Bool :=
  match j.getObjVal? key with
  | .ok j => j.getBool?
  | .error e => throw e

def getBoolUnderKeyM (j : Json) (key : String) : m Bool := do
  Json.getBoolM <| ← j.getObjValM key

def getArrWithSizeGeM (j : Json) (n : Nat) : m ({ arr : Array Json // arr.size ≥ n }) := do
  let arr ← getArrM j
  if h : arr.size ≥ n then
    return ⟨arr, h⟩
  else
    throw s!"expected array of size {n}, got array of size {arr.size}"

def getArrUnderKeyWithSizeGeM (j : Json) (key : String) (n : Nat) : m ({ arr : Array Json // arr.size ≥ n }) := do
  let arr ← getArrUnderKeyM j key
  if h : arr.size ≥ n then
    return ⟨arr, h⟩
  else
    throw s!"expected array of size at least {n}, got array of size {arr.size} under key \"{key}\" in {j}"

def getFirstValHelper? (j : Json) : List String → Except String (String × Json)
  | [] => throw "no keys matched"
  | k :: ks =>
    match j.getObjVal? k with
    | .ok v => .ok (k, v)
    | .error _ => getFirstValHelper? j ks

/--
  Queries the JSON for an object matching a key in the list of keys,
  in order from left to right. Returns the first match, along with the
  matching key, or none if no match is found.

  CC: Can be made faster by breaking the kvs API.
-/
def getFirstVal (j : Json) (l : List String) : Except String (String × Json) :=
  if j.isObject then
    match getFirstValHelper? j l with
    | .ok (s, v) => return (s, v)
    | .error _ => throw s!"No keys matched. Expected one of {l} in {j}"
  else
    throw s!"object expected in {j}"

def getFirstValM (j : Json) (l : List String) : m (String × Json) :=
  match getFirstVal j l with
  | .ok v => pure v
  | .error e => throw e

/--
  Gets a value underneath a "dot-path".

  Acts like `getObjVal?`, except by chaining the elements in `path`
  from left to right. If any one element fails, the whole query fails.
-/
def getObjValByPath (j : Json) (path : List String) : Except String Json :=
  match path with
  | [] => throw "empty path"
  | k :: ks =>
    match ks with
    | [] => j.getObjVal? k
    | _  =>
      match j.getObjVal? k with
      | .ok v => getObjValByPath v ks
      | .error _ => throw s!"property \"{k}\" not found in:\n{j}"

def getObjValByPathM (j : Json) (path : List String) : m Json :=
  match getObjValByPath j path with
  | .ok v => pure v
  | .error e => throw e

def getBoolUnderPathM (j : Json) (path : List String) : m Bool := do
  let v ← getObjValByPathM j path
  match v.getBool? with
  | .ok b => pure b
  | .error e => throw s!"expected boolean under path \"{path}\" in {j}:\n{e}"

/--
  Gets an array underneath a "dot-path".

  Wrapper for `getArr? <| getObjValByPath`.
-/
def getArrByPath? (j : Json) (path : List String) : Except String (Array Json) := do
  getArr? <| ← getObjValByPath j path

def getArrByPathM (j : Json) (path : List String) : m (Array Json) := do
  match getArrByPath? j path with
  | .ok v => pure v
  | .error e => throw e

def getArrByPathWithSizeGeM (j : Json) (path : List String) (n : Nat) : m ({ arr : Array Json // arr.size ≥ n }) := do
  let arr ← getArrByPathM j path
  if h : arr.size ≥ n then
    return ⟨arr, h⟩
  else
    throw s!"expected array of size at least {n}, got array of size {arr.size} under path \"{path}\" in {j}"

-- CC: Dunno how to set the priority of a notation, so we route all notation through `getFirstVal`
-- Notation to alias a Json dictionary lookup
--notation j "[" path "]" => Lean.Json.getObjVal? j path

-- Notation to alias `getFirstVal`
syntax term noWs "[" withoutPosition(sepBy(term, ", "))"]"  : term
macro_rules
  | `($j[ $elems,* ]) => do
    let es := Syntax.TSepArray.getElems elems
    match es.size with
    | 1 => `(Lean.Json.getObjValM $j (es[0]))
    | _ => `(Lean.Json.getFirstValM $j [ $elems,* ])


/-def isInJson (j : Json) (key : String) : Prop :=
  ∃ (val : Json), j.getObjVal? key = .ok val

instance instGetElem : GetElem Json String Json isInJson where
  getElem := fun j key h =>
    match h_lookup : j.getObjVal? key with
    | .ok v => v
    | .error _ => by simp[isInJson, h_lookup] at h

instance instGetElem? : GetElem? Json String Json isInJson where
  getElem? := fun j key =>
    match j.getObjVal? key with
    | .ok v => some v
    | .error _ => none -/

end Lean.Json
