/-
  Verus-Lean intermediate representation (VLIR).

  The "common language" shared by Verus and Lean.
  Statements in Verus and Lean are communicated with a serialization into JSON.
  In Verus, this is the statement syntax tree (SST) level.
  See `source/vir/src/sst.rs`.
-/

import Lean.Data.Json
import VerusLean.Basic

namespace VerusLean

open Lean (Json ToJson FromJson)

abbrev Ident := String
abbrev Idents := Array Ident

inductive Mode where
  | Spec
  | Proof
  | Exec
deriving Repr, DecidableEq, Inhabited

/-- Describes integer types -/
inductive IntRange where
  /-- The set of all mathematical integers Z (..., -2, -1, 0, 1, 2, ...) -/
  | Int
  /-- The set of all natural numbers N (0, 1, 2, ...) -/
  | Nat
  /-- n-bit unsigned numbers (natural numbers up to 2^n - 1) for the specified n: u32 -/
  | U : UInt32 → IntRange
  /-- n-bit signed numbers (integers -2^(n-1), ..., 2^(n-1) - 1) for the specified n: u32 -/
  | I : UInt32 → IntRange
  /-- Rust's USize type -/
  | USize
  /-- Rust's isize type -/
  | ISize
deriving Repr, Inhabited, DecidableEq

/-- Rust type, but without Box, Rc, Arc, etc. -/
inductive Typ where
  | Bool
  | Int                   /- Mathematical integers            -/
  | Nat                   /- Mathematical natural numbers     -/
  | UInt (width : Nat)    /- Unsigned fixed-width integers    -/
  | SInt (width : Nat)    /- Signed fixed-width integers      -/
  | Char
  | StrSlice
  | Array (t : Typ)       /- Array, ignore length in Rust     -/
  /--
    Rust structs, corresponding to Lean `structure`s.

    Note that these are closed-term type "references" to a struct,
    not a definition of a struct. (That would be a `Decl`, defined below.)

    In Rust, structs can be polymorphic in other types (i.e., `params`).
    In most cases, `params` will be empty.

    To refer to the actual declaration/definition of the struct,
    use the datatype map in `Parser.lean`.
  -/
  | Struct (name : Ident) (params : List Typ)
deriving Repr, Inhabited

/-- Constant value literals -/
inductive Const
  /-- Booleans. Uses Rust's built-in `bool` type. -/
  | Bool (b : Bool)
  /-- Integers of arbitrary size. Rust encodes these as a sign bit plus a vector of `u64`s. -/
  | Int (i : Int)
  /-- String slices. Verus encodes this as an `Arc<String>`, a reference-counted pointer to a string in the heap. -/
  | StrSlice (s : String)
  /-- UTF-8 Unicode chars. In Rust, these are always four bytes. -/
  | Char (c : Char)
deriving Repr, Inhabited, DecidableEq

/-- Bitwise operations.  -/
inductive BitwiseOp
  | BitXor
  | BitAnd
  | BitOr
  | Shr (width : Nat) -- CC: Replace width with enum later?
  | Shl (width : Nat) (signExtend : Bool)
deriving Repr, Inhabited, DecidableEq

/-- Arithmetic operations that might fail due to overflow or divide by zero. -/
inductive ArithOp
  /-- Addition on `IntRange`. -/
  | Add
  /-- Subtractio on `IntRange`. -/
  | Sub
  /-- Multiplication on `IntRange`. -/
  | Mul
  /-- Euclidean division on `IntRange` (round towards -inf, not round-towards-zero truncation). -/
  | EuclideanDiv
  /-- Euclidean mod (non-negative result, even for negative divisors). -/
  | EuclideanMod
deriving Repr, Inhabited, DecidableEq

/-- Arithmetic inequality operations. -/
inductive InequalityOp
  | Le
  | Ge
  | Lt
  | Gt
deriving Repr, Inhabited, DecidableEq

/-- Primitive unary operations
 (not arbitrary user-defined functions -- these are represented by Expr::Call) -/
inductive UnaryOp where
  /-- Boolean not -/
  | Not
  /-- Bitwise not -/
  | BitNot (width? : Option Nat)
  /-- Force integer value into range given by IntRange (e.g. by using mod). -/
  | Clip (range: IntRange) (truncate: Bool)
  /-
  StrLen, // Str Slices
  StrIsAscii, // strslice_is_ascii
  InferSpecForLoopIter { print_hint: Bool }, // loops?
  CastToInteger, // coercion after casting to an integer (type argument?)
  -/
  /--
    Quantifier trigger annotations, used to guide SMT solvers.

    Note: These are largely ignored by Lean. We keep them, though, for two
    reasons. First, they simplify parsing, so we don't need to special-case
    on whether we encounter a trigger or not. Second, if Lean ever *does*
    use SMT solvers to discharge the goals, the trigger information is
    useful to have around.

    But for the most part, when creating Lean code from serialized objects,
    we drop trigger information.
  -/
  | Trigger
  /--
    A field projection out of a structure. For example `p.fst`.

    In Verus, this is called a `Field`, and is defined under `UnaryOpr`.
  -/
  | Proj (dt field : Ident)
  /--
    Determines whether the element matches a given variant of an enum.

    In Verus, this is defined under `UnaryOpr`.
  -/
  | IsVariant (dt variant : Ident)
deriving Repr, Inhabited, DecidableEq

/--
  Primitive binary operations.

  All integer operations are on mathematical integers (`IntRange`).
  Finite-width operations are represented with a combination of `IntRange` operations
  and `UnaryOp.Clip` operations.
-/
inductive BinaryOp
  /-- Boolean AND. Short-circuits. -/
  | And
  /-- Boolean OR. Short-circuits. -/
  | Or
  /-- Boolean XOR. No short-circuiting. -/
  | Xor
  /-- Boolean implication. Short-circuiting (RHS evaluated only if LHS is true). -/
  | Implies
  /-- SMT equality for types. Equality differs based on the mode.
      Some types only support compilable equality (Mode == Exec),
        while others only support spec equality (Mode == Spec). -/
  | Eq (mode : Mode)
  /-- Not equals. (Verus doesn't have a mode option here?) -/
  | Ne
  /-- Arithmetic inequality -/
  | Inequality (op : InequalityOp)
  /-- Arithmetic operations. Overflow checking is done when `mode = Exec`. -/
  | Arith (op : ArithOp) (mode : Mode)
  /-- Bitwise operations. Overflow checking is done when `mode = Exec`. -/
  | Bitwise (op : BitwiseOp) (mode : Mode)
    -- /// Used only for handling builtin::strslice_get_char (CC: ??)
  -- | StrGetChar
deriving Repr, Inhabited, DecidableEq

inductive Quant where
  | Forall
  | Exists
deriving Repr, Inhabited, DecidableEq

inductive CallFun where
  | Fun (fn : Ident) -- an optional resolved Fun for methods currently not implemented
  -- | Recursive (name : Ident)
  -- | InternalFun (name : Ident)
deriving Repr, Inhabited, DecidableEq

mutual

/--
  Variable binders.

  Introduces bound variables of different types.

  Note: The `BndX` analogue in Verus has lots of triggers, which we ignore.
-/
inductive Bind where
  -- CC: Verus says this is a `VarBinders`, but for now, we say that each `let x := e` has a single variable binding
  | Let (v : Ident) (e : Exp)
  | Quant (q : Quant) (vars : List (Ident × Typ))
  | Lambda (vars : List (Ident × Typ))
  -- CC: Ignore choose for now
  -- | Choose ()
deriving Repr, Inhabited

/--
  Flattened Verus expressions.

  Expressions have return values.
-/
inductive Exp where
  /-- Constant value literals. -/
  | Const (c : Const)
  /-- Local variables, as a right-hand side of an expression. -/
  | Var (ident : Ident)
  /-- A struct constructor -/
  | StructCtor (dt : Ident) (fields : List (Ident × Exp))
  /-- A constructor for the datatype with the name `dt` and the given `fields`. -/
  | EnumCtor (dt variant : Ident) (data : List (Ident × Exp))
  /-- Primitive unary function application. -/
  | Unary (op : UnaryOp) (arg : Exp)
  -- | UnaryOpr (op : UnaryOp) (arg : Exp)
  /-- Primitive binary function application. -/
  | Binary (op : BinaryOp) (arg₁ arg₂ : Exp)
  -- | BinaryOpr (op : BinaryOp) (arg₁ arg₂ : Exp)
  | If (cond branch₁ branch₂ : Exp)
  -- | ArrayLiteral (elems : Array Exp)
  | Bind (bind : Bind) (exp : Exp)
  /-- Call to spec function -/
  | Call (fn : CallFun) (typs : List Typ) (exps : List Exp)
deriving Repr, Inhabited

end /- mutual -/

/--
  Flattened Verus statements.

  Statements don't have return values.
-/
/-
inductive StmX where
  -- CC: Is this needed, since the only way assertions end up in Lean is via AssertLean?
  -- A normal Verus assertion.
  --| Assert (exp : Exp)
  -- An assertion on a bitvector statement.
  -- | AssertBitVector (requires ensures : Exps)
  --| Return ()
  /-- If-statements. Second branch can be optionally omitted. -/
  | If (exp : Exp) (branch₁ : StmX) (branch₂ : Option StmX)
deriving Repr, Inhabited -/

--abbrev Stms := Array StmX

--------------------------------------------------------------------------------

inductive PostConditionKind
  | Ensures
  | DecreasesImplicitLemma
  | DecreasesBy
deriving Repr, Inhabited

/-
structure PostConditionSST where
  dest : Option Ident
  ensExps : Exps
  ensSpecPreconditionStms : Stms
  kind : PostConditionKind
deriving Repr, Inhabited

-- CC: Let's not implement everything just yet
structure FuncCheckSST where
  reqs : Exps
  postCondition : PostConditionSST
  body : StmX
deriving Repr, Inhabited -/

/--
  All declarations have names associated with them.

  We prefer this over `ToString` or `Repr` because we want to use
  the name for hashing, but we want to leave the typical string
  classes alone for printing, debugging, etc.

  We call this `VName` (Verus Name) to avoid clashes with Lean's `Name`.
 -/
class VName (α : Type u) where
  name : α → String

structure Assertion where
  name : Ident
  decls : List (Ident × Typ)
  body : Exp
deriving Repr, Inhabited

structure SpecFn where
  name : Ident
  inputs : Std.HashMap Ident Typ
  returnType : Typ
  body : Exp
deriving Repr, Inhabited

structure Struct where
  name : Ident
  params : List Ident := []
  fields : List (Ident × Typ)
deriving Repr, Inhabited

structure EnumField where
  name : Ident
  data : List (Ident × Typ) := []
deriving Repr, Inhabited

structure Enum where
  name : Ident
  fields : List EnumField
deriving Repr, Inhabited

/--
  These are top-level "Lean" objects that Lean will evantually turn into
  `def`s and `theorem`s. See `Elab.lean`.
-/
inductive Decl where
  | assertion (a : Assertion)
  | specFn (f : SpecFn)
  | struct (s : Struct)
  | enum (e : Enum)
  --| func (f : FuncCheckSST)
deriving Repr, Inhabited

instance Assertion.instCoeDecl : Coe Assertion Decl := ⟨Decl.assertion⟩
instance SpecFn.instCoeDecl : Coe SpecFn Decl := ⟨Decl.specFn⟩
instance Struct.instCoeDecl : Coe Struct Decl := ⟨Decl.struct⟩
instance Enum.instCoeDecl : Coe Enum Decl := ⟨Decl.enum⟩

instance Assertion.instVName : VName Assertion := ⟨Assertion.name⟩
instance SpecFn.instVName : VName SpecFn := ⟨SpecFn.name⟩
instance Struct.instVName : VName Struct := ⟨Struct.name⟩
instance Enum.instVName : VName Enum := ⟨Enum.name⟩
instance Decl.instVName : VName Decl where
  name := fun d => match d with
    | .assertion a => a.name
    | .specFn f => f.name
    | .struct s => s.name
    | .enum e => e.name

--------------------------------------------------------------------------------

def Bind.idents : Bind → List Ident
  | .Let v _ => [v]
  | .Quant _ vars => vars.map (·.fst)
  | .Lambda vars => vars.map (·.fst)

mutual

def Typ.decEq (t₁ t₂ : Typ) : Decidable (t₁ = t₂) := by
  cases t₁ <;> cases t₂
  <;> try { apply isFalse; intro h; injection h }
  <;> try { apply isTrue; rfl }
  <;> simp
  <;> try infer_instance
  -- Array
  · rename_i t₁ t₂
    exact Typ.decEq t₁ t₂
  -- Struct
  · rename_i i₁ f₁ i₂ f₂
    by_cases hi : i₁ = i₂
    <;> simp [hi]
    · exact Typ.decListEq f₁ f₂
    · exact instDecidableFalse

def Typ.decListEq (ts₁ ts₂ : List Typ) : Decidable (ts₁ = ts₂) := by
  match ts₁, ts₂ with
  | [], [] => exact isTrue rfl
  | (_ :: _), [] | [], (_ :: _) => simp; exact instDecidableFalse
  | (t₁ :: ts₁), (t₂ :: ts₂) =>
    simp
    match Typ.decEq t₁ t₂ with
    | isTrue ht => simp [ht]; exact Typ.decListEq ts₁ ts₂
    | isFalse ht => simp [ht]; exact instDecidableFalse

end /- mutual -/

instance Typ.instDecidableEq : DecidableEq Typ := Typ.decEq
instance Typ.instDecidableEqList : DecidableEq (List Typ) := Typ.decListEq

-- CC: Unnecessary?
theorem Typ.sizeOf_lt_of_mem (i : Ident) (params : List Typ)
    : ∀ {ty : Typ}, ty ∈ params → sizeOf ty < sizeOf (Typ.Struct i params) := by
  intro typ
  induction params with
  | nil => simp
  | cons t ts ih =>
    intro h_mem
    rcases List.mem_cons.mp h_mem with (rfl | h_mem)
    · simp
      omega
    · have := ih h_mem
      simp at this ⊢
      omega
  done

def Typ.height : Typ → _root_.Nat
  | .Array ty => 1 + ty.height
  | .Struct _ params => 1 + params.attach.foldl (init := 0) (λ acc ⟨ty, _⟩ => max acc ty.height)
  | _ => 1

def Exp.height : Exp → Nat
  | .Const _
  | .Var _ => 1
  | .Unary _ e => 1 + e.height
  | .StructCtor _ _ => 2
  | .EnumCtor _ _ _ => 2
    /-let exps := fields.map Prod.snd
    have : sizeOf exps ≤ sizeOf fields := by
      sorry
      done
    1 + exps.attach.foldl (init := 0) (λ acc ⟨e, _⟩ =>
      have : sizeOf exps ≤ sizeOf dt + sizeOf fields + 1 := by
        sorry
        done
      max acc e.height
    ) -/
  | .Binary _ e₁ e₂ => 1 + max e₁.height e₂.height
  | .If c b₁ b₂ => 1 + max c.height (max b₁.height b₂.height)
  | .Bind _ e => 1 + e.height
  | .Call _ _ es => 1 + es.attach.foldl (init := 0) (λ acc ⟨e, _⟩ => max acc e.height)

end VerusLean
