import VerusLean.Vstd.Seq.Defs

namespace Vstd

inductive Seq (α : Type u)
  | mk (elems : List α)
deriving Repr, DecidableEq, Inhabited

instance L : VSeqLikeF Seq where
  map := fun f s => match s with | .mk elems => .mk (elems.map f)
  toList := fun s => match s with | .mk elems => elems
  ofList := fun elems => .mk elems
  new := fun len f =>
    .mk (List.range len |>.map Int.ofNat |>.map f) -- incorrect
  sortBy := fun cmp s => s
  maxVia := fun s cmp => default -- incorrect
  minVia := fun s cmp => default -- incorrect
  indexOfLast := fun s a => match s with
    | .mk elems => elems.reverse.idxOf? a
  -- foldLeft := S.foldLeftAlt -- slightly incorrect
  -- foldRight := S.foldRightAlt -- slightly incorrect
  -- flatten_alt := S.flatten -- slightly incorrect
  /-fail to show termination for
      Vstd.S
    with errors
    failed to infer structural recursion:
    no parameters suitable for structural recursion

    well-founded recursion cannot be used, 'Vstd.S' does not take any (non-fixed) arguments
    -/
  --  => S.ofList ((S.toList s).map S.toList |>.flatten)

def sort {L : Type u → Type u} [VSeqLikeF L] (s : L α) : L α := sorry


end Vstd
