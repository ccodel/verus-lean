import VerusLean.Vstd.Map.Defs

namespace Vstd

inductive Map (α : Type u) (β : Type v)
  | mk (elems : List α)

instance : VMapLikeF Map := by sorry
instance : VMapF Map := by sorry

end Vstd
