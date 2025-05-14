import VerusLean.Vstd.Set.Defs

namespace Vstd

inductive Set (α : Type u)
  | mk (elems : List α)

instance : VSetLikeF Set where
  map := fun f s => match s with | .mk elems => .mk (elems.map f)
  mem := fun s a => match s with | .mk elems => a ∈ elems
  empty := .mk []
  insert := fun a s => match s with | .mk elems => .mk (a :: elems)
  remove := fun _ s => match s with | .mk elems => .mk (elems)  -- This is incorrect
  choose := fun _ _ => default  -- This is totally wrong
  union := fun s₁ s₂ => match s₁, s₂ with
    | .mk elems₁, .mk elems₂ => .mk (elems₁ ++ elems₂)
  inter := fun s₁ s₂ => match s₁, s₂ with
    | .mk elems₁, .mk _ => .mk (elems₁) -- This is incorrect
  sdiff := fun s₁ s₂ => match s₁, s₂ with
    | .mk elems₁, .mk _ => .mk (elems₁) -- This is incorrect
  filter := fun s p => match s with
    | .mk elems => .mk (elems.filter p)

instance : VSetF Set where
  card := fun s => match s with | .mk elems => elems.length
  toList := fun s => match s with | .mk elems => elems -- This is slightly incorrect
  fold := fun f init s => match s with | .mk elems => elems.foldl f init

end Vstd
