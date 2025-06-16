import VerusLean.Vstd.Set.Defs

namespace Vstd

inductive Set (α : Type u)
  | mk (elems : List α)
deriving Repr, DecidableEq, Inhabited

instance S : VSetLikeF Set where
  map := fun f s => match s with | .mk elems => .mk (elems.map f)
  -- mem := fun s a => match s with | .mk elems => a ∈ elems
  -- Cedar requires [DecidableEq α]
  -- mem := fun {α} [DecidableEq α] (s : Set α) (a : α) => match s with
    -- | .mk elems => elems.contains a
  mem := fun _ _ => false -- This is totally wrong
  empty := .mk []
  -- no correspondence in Cedar
  insert := fun a s => match s with | .mk elems => .mk (a :: elems)
  -- no correspondence in Cedar
  remove := fun _ s => match s with | .mk elems => .mk (elems)  -- This is incorrect
  -- singleton := fun a => .mk [a]
  -- no correspondence in Cedar
  choose := fun s => match s with
    | .mk elems => match elems with
      | [] => default
      | (x :: _) => x
  subset := fun _ _ => false -- This is totally wrong
  union := fun s₁ s₂ => match s₁, s₂ with
    | .mk elems₁, .mk elems₂ => .mk (elems₁ ++ elems₂)
  inter := fun s₁ s₂ => match s₁, s₂ with
    | .mk elems₁, .mk _ => .mk (elems₁) -- This is incorrect
  sdiff := fun s₁ s₂ => match s₁, s₂ with
    | .mk elems₁, .mk _ => .mk (elems₁) -- This is incorrect
  disjoint := fun _ _ => false -- This is incorrect
  filter := fun s p => match s with
    | .mk elems => .mk (elems.filter p)
  findUniqueMinimal := fun _ _ => default -- This is incorrect
  findUniqueMaximal := fun _ _ => default -- This is incorrect
  all := fun s p => match s with
    | .mk elems => elems.all p
  any := fun s p => match s with
    | .mk elems => elems.any p
  filterMap := fun _ _ => .mk [] -- This is incorrect
  setIntRange := fun _ _ => .mk [] -- This is incorrect

instance FS : VSetF Set where
  card := fun s => match s with | .mk elems => elems.length
  toList := fun s => match s with | .mk elems => elems -- This is slightly incorrect
  fold := fun f init s => match s with | .mk elems => elems.foldl f init

instance IS : VSetInfF Set where
  full := .mk [] -- This is incorrect
  new := fun _ => .mk [] -- This is incorrect
  compl := fun s => match s with
    | .mk elems => .mk [] -- This is incorrect
  card := fun s => match s with
    | .mk elems => some elems.length
  toList := fun s h_finite => match s with
    | .mk elems => elems -- how to use h_finite?
  fold := fun f init s h_finite => match s with
    | .mk elems => elems.foldl f init -- how to use h_finite?


end Vstd
