import Lean.Data.Json

namespace Lean.Json

def isObject (j : Json) : Bool :=
  match j with
  | Json.obj _ => true
  | _ => false

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
def getFirstVal? (j : Json) (l : List String) : Except String (String × Json) :=
  if j.isObject then
    getFirstValHelper? j l
  else
    throw "object expected"

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

end Lean.Json
