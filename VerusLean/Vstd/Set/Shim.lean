import VerusLean.Vstd.Set.Defs

namespace Vstd

inductive Set (α : Type u)
  | mk (elems : List α)

instance : VSetLikeF Set := by sorry
instance : VSetF Set := by sorry

end Vstd
