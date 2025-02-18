import Lean.Data.Json

namespace Lean.Json

def isObject (j : Json) : Bool :=
  match j with
  | Json.obj _ => true
  | _ => false

def getNatUnderKey? (j : Json) (key : String) : Except String Nat := do
  Json.getNat? <| ← j.getObjVal? key

def getArrWithSizeGe? (j : Json) (n : Nat) : Except String ({ arr : Array Json // arr.size ≥ n }) := do
  let arr ← j.getArr?
  if h : arr.size ≥ n then
    return ⟨arr, h⟩
  else
    throw s!"expected array of size {n}, got array of size {arr.size}"

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
    | .error _ => throw s!"No keys matched. Expected one of {l}"
  else
    throw "object expected"

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
      | .error _ => throw "property not found"

-- CC: Dunno how to set the priority of a notation, so we route all notation through `getFirstVal`
-- Notation to alias a Json dictionary lookup
--notation j "[" path "]" => Lean.Json.getObjVal? j path

-- Notation to alias `getFirstVal`
syntax term noWs "[" withoutPosition(sepBy(term, ", "))"]"  : term
macro_rules
  | `($j[ $elems,* ]) => do
    let es := Syntax.TSepArray.getElems elems
    match es.size with
    | 1 => `(Lean.Json.getObjVal $j (es[0]))
    | _ => `(Lean.Json.getFirstVal $j [ $elems,* ])


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
