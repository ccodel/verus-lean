import Std.Data.HashMap

namespace Vstd

/--
  Verus `Vstd` sequences. They are always finite.
-/
class VSeqLikeF (L : Type u → Type v)
  extends
    Functor L
  where
  empty : {α : Type u} → L α
  new : {α : Type u} → (len : Nat) → (f : Nat → α) → L α
  length : {α : Type u} → L α → Nat
  get? : {α : Type u} → L α → Nat → Option α
  get : {α : Type u} → (s : L α) → (i : Nat) → (h : i < length s) → α
  get! : {α : Type u} → L α → Nat → α
  push : {α : Type u} → L α → α → L α
  update : {α : Type u} → L α → Nat → α → L α
  extract : {α : Type u} → L α → Nat → Nat → L α
  take : {α : Type u} → L α → Nat → L α -- return the whole seq if n > length
  drop : {α : Type u} → L α → Nat → L α -- return the empty seq if n > length
  add : {α : Type u} → L α → L α → L α
  last : {α : Type u} → L α → α -- if empty, return a default value, or requires `length s > 0`?
  first : {α : Type u} → L α → α -- same

  mapEntries : {α β : Type u} → (int → α → β) → L α → L β
  isPrefixOf : {α : Type u} → L α → L α → Bool
  isSuffixOf : {α : Type u} → L α → L α → Bool
  sortBy : {α : Type u} → (α → α → Bool) → L α → L α
  filter : {α : Type u} → (L α) → (α → Bool) → L α
  maxVia : {α : Type u} → (L α) → (α → α → Bool) → α
  minVia : {α : Type u} → (L α) → (α → α → Bool) → α
  mem : {α : Type u} → (L α) → α → Prop
  indexOf : {α : Type u} → (L α) → α → Int
  indexOfFirst : {α : Type u} → (L α) → α → Option Int
  firstIndexHelper : {α : Type u} → (L α) → α → Int
  indexOfLast : {α : Type u} → (L α) → α → Option Int
  lastIndexHelper : {α : Type u} → (L α) → α → Int
  dropLast : {α : Type u} → L α → L α
  dropFirst : {α : Type u} → L α → L α
  noDuplicates : {α : Type u} → L α → Bool
  disjoint : {α : Type u} → L α → L α → Bool
  insert : {α : Type u} → L α → Int → α → L α
  remove : {α : Type u} → L α → Int → L α
  removeValue : {α : Type u} → L α → α → L α
  reverse : {α : Type u} → L α → L α
  zipWith : {α β : Type u} → L α → L β → L (α × β)
  foldLeft : {α β : Type u} → L α → β → (β → α → β) → β
  foldLeftAlt : {α β : Type u} → L α → β → (β → α → β) → β
  foldRight : {α β : Type u} → L α → (α → β → β) → β → β
  foldRightAlt : {α β : Type u} → L α → (α → β → β) → β → β
  updateSubrangeWith : {α : Type u} → L α → Int → L α → L α


-- #check List.get
-- #check List.get?
-- #check List.get!
-- #check List.getD
-- #check List.IsPrefix
-- #check List.isPrefixOf
-- #check Array.isPrefixOf

namespace VSeqLikeF

variable {L : Type u → Type v} [VSeqLikeF L]

instance instEmptyCollection : EmptyCollection (L α) := ⟨empty⟩
instance instInhabited : Inhabited (L α) := ⟨∅⟩
-- instance instSingleton : Singleton α (L α) := ⟨singleton⟩
instance instMembership : Membership α (L α) := ⟨mem⟩
instance instHAdd : HAdd (L α) (L α) (L α) := ⟨add⟩
-- instance instCoeList : Coe (List α) (S α) := ⟨ofList⟩
instance instGetElem : GetElem (L α) Nat α (fun s i => i < length s) := ⟨get⟩
instance instGetElem? : GetElem? (L α) Nat α (fun s i => i < length s) where
  getElem? := get?
  getElem! := get!

end VSeqLikeF


open VSeqLikeF in
class LawfulVSeqLikeF (L : Type u → Type v) [VSeqLikeF L]
  extends
    LawfulFunctor L
  where
  protected ext (s₁ s₂ : L α) : (length s₁ = length s₂ ∧ ∀ i, i < length s₁→ get? s₁ i = get? s₂ i) → s₁ = s₂

  length_empty : length (empty : L α) = 0
  length_new {α : Type u} (len : Nat) (f : Nat → α) : length (new len f : L α) = len
  length_push {α : Type u} (s : L α) (a : α) : length (push s a) = length s + 1
  length_update {α : Type u} (s : L α) (i : Nat) (a : α) (h : i < length s) :
    length (update s i a) = length s
  length_extract {α : Type u} (s : L α) (i j : Nat) (h₁ : i ≤ j) (h₂ : j ≤ length s) :
    length (extract s i j) = j - i
  length_take {α : Type u} (s : L α) (n : Nat) : length (take s n) = if n < length s then n else length s
  length_drop {α : Type u} (s : L α) (n : Nat) : length (drop s n) = if n < length s then length s - n else 0
  length_add {α : Type u} (s₁ s₂ : L α) : length (s₁ + s₂) = length s₁ + length s₂
  length_last {α : Type u} (s : L α) (h : length s > 0) : length (dropLast s) = length s - 1
  length_first {α : Type u} (s : L α) (h : length s > 0) : length (dropFirst s) = length s - 1
  length_map {α β} (f : α → β) (s : L α) : length (f <$> s) = length s
  -- length_filter {α} (s : L α) (p : α → Bool) : length (filter s p) ≤ length s


  get?_empty {α} (i : Nat) : get? (empty : L α) i = none
  get?_push {α} (s : L α) (a : α) (i : Nat) :
    get? (push s a) i = if i = length s then some a else get? s i
  get?_update {α} (s : L α) (i j : Nat) (a : α) :
    get? (update s i a) j = if i = j then some a else get? s j
  get?_extract {α} (s : L α) (i j k: Nat) : -- I think no need to check pos in range?
    get? (extract s i j) k = get? s (i + k)
  get?_take {α} (s : L α) (n i : Nat):
    get? (take s n) i = if i < n then get? s i else none
  get?_drop {α} (s : L α) (n i : Nat) :
    get? (drop s n) i = get? s (n + i)
  get?_add {α} (s₁ s₂ : L α) (i : Nat) :
    get? (s₁ + s₂) i = if i < length s₁ then get? s₁ i else get? s₂ (i - length s₁)
  get?_last {α} (s : L α) (h : length s > 0) : get? s (length s - 1) = some (last s)
  get?_first {α} (s : L α) (h : length s > 0) : get? s 0 = some (first s)
  get?_map {α β} (f : α → β) (s : L α) (i : Nat) :
    get? (f <$> s) i = if i < length s then some (f (get! s i)) else none

  extract_eq {α} (s : L α) (i j : Nat) :
    extract s i j = take (drop s i) (j - i)

  mem_iff_exists_get {α} (s : L α) (a : α) :
    a ∈ s ↔ ∃ i, i < length s ∧ get? s i = some a

  filter_empty {α} (p : α → Bool) : filter (empty : L α) p = empty
  filter_push {α} (s : L α) (a : α) (p : α → Bool) :
    filter (push s a) p = if p a then push (filter s p) a else filter s p
  -- filter_pred {α} (s : L α) (p : α → Bool) (h : i < length (filter s p)) :
    -- p (get (filter s p) i h)

  eq_push_last {α} (s : L α) (h : length s > 0) :
    (push (dropLast s) (last s)) = s
  eq_push_first_to_drop_first {α} (s : L α) (h : length s > 0) :
    (push (dropFirst s) (first s)) = s

  dropLast_eq {α} (s : L α) (h : length s > 0) :
    dropLast s = extract s 0 (length s - 1)
  dropFirst_eq {α} (s : L α) (h : length s > 0) :
    dropFirst s = extract s 1 (length s)

  -- not_mem_empty : ∀ (a : α), a ∉ (∅ : S α)
  -- mem_insert_iff {a b : α} {s : S α} : b ∈ (s + a) ↔ b = a ∨ b ∈ s
  -- mem_remove_iff {a b : α} {s : S α} : b ∈ (s - a) ↔ b ≠ a ∧ b ∈ s
  -- mem_singleton_iff {a b : α} : b ∈ ({a} : S α) ↔ b = a
  -- -- choose_mem {α : Type u} [Inhabited α] : ∀ (s : S α) (h : ∃ x, x ∈ s), choose s h ∈ s
  -- choose_mem {α : Type u} [Inhabited α] : ∀ (s : S α), (h : ∃ x, x ∈ s) → choose s ∈ s
  -- subset_iff {s₁ s₂ : S α} : s₁ ⊆ s₂ ↔ ∀ a, a ∈ s₁ → a ∈ s₂
  -- mem_union_iff  {a : α} {s₁ s₂ : S α} : a ∈ s₁ ∪ s₂ ↔ a ∈ s₁ ∨ a ∈ s₂
  -- mem_inter_iff  {a : α} {s₁ s₂ : S α} : a ∈ s₁ ∩ s₂ ↔ a ∈ s₁ ∧ a ∈ s₂
  -- mem_sdiff_iff  {a : α} {s₁ s₂ : S α} : a ∈ s₁ \ s₂ ↔ a ∈ s₁ ∧ a ∉ s₂
  -- mem_symmDiff_iff {a : α} {s₁ s₂ : S α} : a ∈ symmDiff s₁ s₂ ↔ (a ∈ s₁ \ s₂ ∨ a ∈ s₂ \ s₁)
  -- disjoint_iff {s₁ s₂ : S α} : disjoint s₁ s₂ ↔ ∀ a, a ∉ s₁ ∩ s₂
  -- mem_filter_iff {p : α → Bool} {s : S α} {a : α} : a ∈ filter s p ↔ a ∈ s ∧ p a
  -- mem_ofList_iff {a : α} {l : List α} : a ∈ (ofList l : S α) ↔ a ∈ l
  -- mem_map_iff {f : α → β} {s : S α} {b : β}
  --   : b ∈ f <$> s ↔ ∃ a, a ∈ s ∧ f a = b
  -- mem_filterMap_iff {α β : Type u} {f : α → Option β} {s : S α} {b : β}
  --   : b ∈ filterMap f s ↔ ∃ a, a ∈ s ∧ f a = some b

open LawfulVSeqLikeF in
-- attribute [simp] not_mem_empty mem_singleton_iff mem_ofList_iff
-- attribute [ext] LawfulVSeqLikeF.ext

class FoldCommutative (op : α → β → α) : Prop where
  comm : (a : α) → (b₁ b₂ : β) → op (op a b₁) b₂ = op (op a b₂) b₁

class FoldCommutativeR (op : α → β → β) : Prop where
  comm : (a₁ a₂ : α) → (b : β) → op a₁ (op a₂ b) = op a₂ (op a₁ b)


open Std in
def SeqVstdTranslationNames : HashMap Lean.Name Lean.Name := HashMap.ofList <|
  List.map (f := fun ⟨x, y⟩ => (String.toName s!"Vstd.Seq.{x}", String.toName y)) <| [
  /- from seq.rs -/
  ("empty", ""),
  ("new", ""),
  ("len", ""),
  ("index", ""), -- how to support direct indexing s[i]?
  ("spec_index", ""), -- same as index
  ("push", ""),
  ("update", ""),
  ("subrange", "VSeqLikeF.extract"),
  ("take", "VSeqLikeF.take"),
  ("skip", "VSeqLikeF.drop"),
  ("add", ""),
  ("spec_add", ""), -- same as add
  ("last", ""),
  ("first", ""),

  /- from seq_lib.rs -/
  ("map", ""), -- Verus TODO: rename to `map_entries`?
  ("map_values", "Functor.map"), -- Verus TODO: rename to `map`?
  ("is_prefix_of", ""),
  ("is_suffix_of", ""),
  ("sort_by", ""),
  ("filter", ""),
  ("max_via", ""),
  ("min_via", ""),
  ("contains", "VSeqLikeF.mem"),
  ("index_of", ""),
  ("index_of_first", ""),
  ("first_index_helper", ""),
  ("index_of_last", ""),
  ("last_index_helper", ""),
  ("drop_last", ""),
  ("drop_first", ""),
  ("no_duplicates", ""),
  ("disjoint", ""),
  ("to_set", ""), -- ignored for now as Lean doesn't support build cycle
  ("to_multiset", ""), -- ignored for now
  ("insert", ""),
  ("remove", ""),
  ("remove_value", ""),
  ("reverse", ""),
  ("zip_with", ""),
  ("fold_left", ""),
  ("fold_left_alt", ""),
  ("fold_right", ""),
  ("fold_right_alt", ""),
  ("update_subrange_with", ""),

  -- currently ignore the functions in `impl<A, B> Seq<(A, B)>`, `impl<A> Seq<Seq<A>>`, and `impl Seq<int>`
  ]
end Vstd
