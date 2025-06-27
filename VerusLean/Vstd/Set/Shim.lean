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
  insert := fun s a => match s with | .mk elems => .mk (a :: elems)
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
  fromSeq := fun s => match s with
    | .mk elems => .mk elems

instance FS : VSetF Set where
  card := fun s => match s with | .mk elems => elems.length
  toList := fun s => match s with | .mk elems => elems -- This is slightly incorrect
  fold := fun s init f => match s with | .mk elems => elems.foldl f init

instance IS : VSetInfF Set where
  full := .mk [] -- This is incorrect
  new := fun _ => .mk [] -- This is incorrect
  compl := fun s => match s with
    | .mk elems => .mk [] -- This is incorrect
  card := fun s => match s with
    | .mk elems => some elems.length
  toList := fun s h_finite => match s with
    | .mk elems => elems -- how to use h_finite?
  fold := fun s init f h_finite => match s with
    | .mk elems => elems.foldl f init -- how to use h_finite?

-- instance LS : LawfulVSetLikeF Set where
--   ext := fun s₁ s₂ h => by
--     cases s₁; cases s₂; simp [h]
--   not_mem_empty := fun a => by
--     simp [mem_iff_exists_get]
--   mem_insert_iff := fun a b s => by
--     cases s; simp [mem_iff_exists_get, List.mem_cons_iff]
--   mem_remove_iff := fun a b s => by
--     cases s; simp [mem_iff_exists_get, List.mem_cons_iff]
--   mem_singleton_iff := fun a b => by
--     simp [mem_iff_exists_get]
--   choose_mem := fun s h => by
--     cases s; cases h; simp [choose]
--   subset_iff := fun s₁ s₂ => by
--     cases s₁; cases s₂; simp [subset_iff, mem_iff_exists_get]
--   mem_union_iff := fun a s₁ s₂ => by
--     cases s₁; cases s₂; simp [mem_union_iff, mem_iff_exists_get]
--   mem_inter_iff := fun a s₁ s₂ => by
--     cases s₁; cases s₂; simp [mem_inter_iff, mem_iff_exists_get]
--   mem_sdiff_iff := fun a s₁ s₂ => by
--     cases s₁; cases s₂; simp [mem_sdiff_iff, mem_iff_exists_get]
--   mem_symmDiff_iff := fun a s₁ s₂ => by
--     cases s₁; cases s₂; simp [mem_symmDiff_iff, mem_iff_exists_get]
--   disjoint_iff := fun _ _ => by
--     simp [disjoint_iff, mem_inter_iff]
--   mem_filter_iff := fun p s a => by
--     cases s; simp [mem_filter_iff, mem_iff_exists_get]
--   mem_ofList_iff := fun a l => by
--     simp [mem_ofList_iff, mem_iff_exists_get]
--   mem_map_iff := fun f _ _ b => by
--     simp [mem_map_iff, mem_iff_exists_get]
--   mem_filterMap_iff := fun f _ _ b => by
--     simp [mem_filterMap_iff, mem_iff_exists_get]

end Vstd
