import VerusLean.Vstd.Set.Shim
import VerusLean.Vstd.Map.Defs

namespace Vstd

inductive Map (α : Type u) (β : Type v)
  | mk (elems : List (α × β))
deriving Repr, DecidableEq, Inhabited

instance M : VMapLikeF Map Set Set where
  empty := .mk []
  total := fun _ => .mk [] -- incorrect
  new := fun _ _ => .mk [] -- incorrect
  fromSet := fun s f => match s with
    | .mk elems => .mk (elems.map (fun k => (k, f k)))
  keys := fun m => match m with | .mk elems => S.ofList (elems.map Prod.fst)
  values := fun m => match m with | .mk elems => S.ofList (elems.map Prod.snd)
  get := fun m k h => match m with
  | .mk elems =>
    let entry := elems.find? (fun (k', _) => k' = k)
    match entry with
    | some (_, v) => v
    | none => default -- should not occur given h
  get? := fun m k =>
    match m with
    | .mk elems =>
      let entry := elems.find? (fun (k', _) => k' = k)
      entry.map Prod.snd
  get! := fun m k =>
    match m with
    | .mk elems =>
      let entry := elems.find? (fun (k', _) => k' = k)
      match entry with
      | some (_, v) => v
      | none => default
  insert := fun m k v => m -- incorrect
  remove := fun m k => m -- incorrect
  removeKeys := fun m ks => m -- incorrect
  restrict := fun m ks => m -- incorrect
  isEqualOnKey := fun m₁ m₂ k => match m₁, m₂ with
    | .mk elems₁, .mk elems₂ =>
      match elems₁.find? (fun (k', _) => k' = k), elems₂.find? (fun (k', _) => k' = k) with
      | some (_, v₁), some (_, v₂) => v₁ = v₂
      | _, _ => false
  agrees := fun m₁ m₂ => match m₁, m₂ with
    | .mk elems₁, .mk elems₂ =>
      elems₁.all (fun (k₁, v₁) => match elems₂.find? (fun (k₂, _) => k₂ = k₁) with
        | some (_, v₂) => v₁ = v₂
        | none => false)
  size := fun m => match m with | .mk elems => elems.length
  submapOf := fun m₁ m₂ => match m₁, m₂ with
    | .mk elems₁, .mk elems₂ =>
      elems₁.all (fun (k₁, v₁) => match elems₂.find? (fun (k₂, _) => k₂ = k₁) with
        | some (_, v₂) => v₁ = v₂
        | none => false)
  union_prefer_right := fun m₁ m₂ => m₂ -- incorrect
  mapEntires := fun m f => match m with
    | .mk elems => .mk (elems.map (fun (k, v) => (k, f k v)))
  mapValues := fun m f => match m with
    | .mk elems => .mk (elems.map (fun (k, v) => (k, f v)))
  isInjective := fun _ => true -- incorrect
    -- fun m => match m with
    -- | .mk elems =>
    --   let values := elems.map Prod.snd
    --   values.Nodup


-- instance : VMapF Map := by sorry

end Vstd
