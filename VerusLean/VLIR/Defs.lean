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

inductive Mode where
  | Spec
  | Proof
  | Exec
deriving Repr, DecidableEq, Inhabited, Hashable

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
deriving Repr, Inhabited, DecidableEq, Hashable

/-- Rust type, but without Box, Rc, Arc, etc. -/
inductive Typ where
  | Unit                  /- In Verus, this is represented as a 0-ary tuple. -/
  | Tuple (ty₁ ty₂ : Typ) /- In Lean, these are `Prod`s. -/
  | Bool
  | Int                   /- Mathematical integers            -/
  | Nat                   /- Mathematical natural numbers     -/
  | UInt (width : Nat)    /- Unsigned fixed-width integers    -/
  | SInt (width : Nat)    /- Signed fixed-width integers      -/
  | Char
  | StrSlice
  | Array (t : Typ)       /- Array, ignore length in Rust     -/
  | TypParam (i : Ident)  /- Type parameter. For example, `α` in `List α`. -/
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
  /--
    Rust enums, corresponding to Lean `inductive` types.

    Note that these are closed-term type "references" to an enum,
    not a definition of an enum. (That would be a `Decl`, defined below.)

    In Rust, enums can be polymorphic in other types (i.e., `params`).
    In most cases, `params` will be empty.

    To refer to the actual declaration/definition of the enum,
    use the datatype map in `Parser.lean`.
  -/
  | Enum (name : Ident) (params : List Typ)
deriving Repr, Inhabited, Hashable

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
deriving Repr, Inhabited, DecidableEq, Hashable

/-- Bitwise operations.  -/
inductive BitwiseOp
  | BitXor
  | BitAnd
  | BitOr
  | Shr (width : Nat) -- CC: Replace width with enum later?
  | Shl (width : Nat) (signExtend : Bool)
deriving Repr, Inhabited, DecidableEq, Hashable

/-- Arithmetic operations that might fail due to overflow or divide by zero. -/
inductive ArithOp
  /-- Addition on `IntRange`. -/
  | Add
  /-- Subtraction on `IntRange`. -/
  | Sub
  /-- Multiplication on `IntRange`. -/
  | Mul
  /-- Euclidean division on `IntRange` (round towards -inf, not round-towards-zero truncation). -/
  | EuclideanDiv
  /-- Euclidean mod (non-negative result, even for negative divisors). -/
  | EuclideanMod
deriving Repr, Inhabited, DecidableEq, Hashable

/-- Arithmetic inequality operations. -/
inductive InequalityOp
  | Le
  | Ge
  | Lt
  | Gt
deriving Repr, Inhabited, DecidableEq, Hashable

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
  /--
    coerce Typ --> Boxed(Typ)

    In Verus, this is defined under `UnaryOpr`.
  -/
  | Box (t : Typ)
  /--
    coerce Boxed(Typ) --> Typ

    In Verus, this is defined under `UnaryOpr`.
  -/
  | Unbox (t : Typ)
deriving Repr, Inhabited, Hashable

/--
  Primitive binary operations.

  All integer operations are on mathematical integers (`IntRange::Int`).
  Finite-width operations are represented with a combination of `IntRange::Int` operations
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
deriving Repr, Inhabited, DecidableEq, Hashable

inductive Quant where
  | Forall
  | Exists
deriving Repr, Inhabited, DecidableEq, Hashable

inductive CallFun where
  | Fun (fn : Ident) -- an optional resolved Fun for methods currently not implemented
  -- | Recursive (name : Ident)
  -- | InternalFun (name : Ident)
deriving Repr, Inhabited, DecidableEq, Hashable

mutual

/--
  Variable binders.

  Introduces bound variables of different types.

  Note: The `BndX` analogue in Verus has lots of triggers, which we ignore.
-/
inductive Bind where
  -- CC: Verus says this is a `VarBinders`, but for now, we say that each `let x := e` has a single variable binding
  | Let (v : Ident) (ty : Typ) (e : Exp)
  | Quant (q : Quant) (vars : List (Ident × Typ))
  | Lambda (vars : List (Ident × Typ))
  -- CC: Ignore choose for now
  -- | Choose ()
deriving Repr, Inhabited, Hashable

/--
  Flattened Verus expressions.

  Expressions have return values.
-/
inductive Exp where
  /-- Constant value literals. -/
  | Const (c : Const)
  /-- Local variables, as a right-hand side of an expression. -/
  | Var (ident : Ident)
  /-- Call to spec function -/
  | Call (fn : CallFun) (typs : List Typ) (exps : List Exp)
  /-- A struct constructor -/
  | StructCtor (dt : Ident) (fields : List (Ident × Exp))
  /-- A constructor for the datatype with the name `dt` and the given `fields`. -/
  | EnumCtor (dt variant : Ident) (data : List (Ident × Exp))
  /-- Primitive unary function application. -/
  | Unary (op : UnaryOp) (arg : Exp)
  /-- Primitive binary function application. -/
  | Binary (op : BinaryOp) (arg₁ arg₂ : Exp)
  | If (cond branch₁ branch₂ : Exp)
  | Bind (bind : Bind) (exp : Exp)
  | ArrayLiteral (elems : List Exp)
deriving Repr, Inhabited, Hashable

end /- mutual -/

structure LoopInvariant where
  atEntry : Bool
  atExit : Bool
  body : Exp
deriving Repr, Inhabited, Hashable

/--
  Flattened Verus statements.

  Statements don't have return values.
-/
inductive Stm where
  | Call (fn : Ident) (typArgs : List Typ) (args : List Exp)  -- misisng split, dest
  | Assert (exp : Exp)
  | AssertBitVector (requires ensures : List Exp)
  | AssertQuery (body : Stm) -- missing mode, typ_inv_exps, typ_inv_vars
  | AssertCompute (exp : Exp) -- should never occur (removed by elaborate_function2() in verus)
  | AssertLean (exp : Exp)
  | Assume (exp : Exp)  -- we could treat these as axioms, or just "by verus"?
  | Assign (lhs : Ident) (lhsTy : Typ) (rhs : Exp) (lhsIsInit : Bool) -- CC: In verus, LHS is a Dest, but we take a shortcut
  | DeadEnd (stm : Stm)
  | Return (exp : Option Exp)
  | BreakOrContinue (label : Option String) (isBreak : Bool)
  | If (cond : Exp) (branch₁ : Stm) (branch₂ : Option Stm)
  | Loop (isForLoop : Bool) (label : Option String) (cond : Option (Stm × Exp)) (body : Stm)
         (invariants : List LoopInvariant) -- missing decrease, typ_inv_vars
  | OpenInvariant (stm : Stm)
  | ClosureInner (body : Stm) -- missing typ_inv_vars
  | Block (stms : List Stm)
deriving Repr, Inhabited, Hashable

--------------------------------------------------------------------------------

inductive PostConditionKind
  | Ensures
  | DecreasesImplicitLemma
  | DecreasesBy
deriving Repr, Inhabited, Hashable

/-
-- simplified as postCondition : Exp in FuncCheckSst
structure PostConditionSST where
  dest : Option Ident
  ensExps : Exps
  ensSpecPreconditionStms : Stms
  kind : PostConditionKind
deriving Repr, Inhabited
 -/
structure FuncCheckSst where
  name : Ident
  reqs : List Exp
  postCondition : List Exp
  -- Ignore mask_set, unwind, body, and statics for now
  -- Expects no return value, and an empty body instead of a stmX in a proof fn?
  decls : List (Ident × Typ)
deriving Repr, Inhabited, Hashable

/--
  A type class to extract the name of a declaration.

  In Verus (and in Lean), all declarations have names associated with them.
  We use this type class to refer to them.

  We prefer this over `ToString` or `Repr` because we want to use
  this name for hashing, but we want to leave the typical string
  classes alone for printing, debugging, etc.

  We call this `VName` (Verus Name) to avoid clashes with Lean's `Name`.
 -/
class VName (α : Type u) where
  name : α → String

structure Assertion where
  name : Ident
  decls : List (Ident × Typ)
  body : Exp
deriving Repr, Inhabited, Hashable

structure SpecFn where
  name : Ident
  inputs : List (Ident × Typ)
  returnType : Typ
  body : Exp
deriving Repr, Inhabited, Hashable

structure ProofFn where
  name : Ident
  inputs : List (Ident × Typ)
  requires : List Exp
  ensures : List Exp
  body : Stm
deriving Repr, Inhabited, Hashable

structure Struct where
  name : Ident
  typeParams : List Ident := []
  fields : List (Ident × Typ)
deriving Repr, Inhabited, Hashable

structure EnumField where
  name : Ident
  data : List (Ident × Typ) := []
deriving Repr, Inhabited, Hashable

structure Enum where
  name : Ident
  typeParams : List Ident := []
  fields : List EnumField
deriving Repr, Inhabited, Hashable

/--
  These are top-level "Lean" objects that Lean will evantually turn into
  `def`s and `theorem`s. See `Elab.lean`.
-/
inductive Decl where
  | assertion (a : Assertion)
  | specFn (f : SpecFn)
  | proofFn (f : ProofFn)
  | struct (s : Struct)
  | enum (e : Enum)
  | func (f : FuncCheckSst)
deriving Repr, Inhabited, Hashable

instance Assertion.instCoeDecl : Coe Assertion Decl := ⟨Decl.assertion⟩
instance SpecFn.instCoeDecl : Coe SpecFn Decl := ⟨Decl.specFn⟩
instance ProofFn.instCoeDecl : Coe ProofFn Decl := ⟨Decl.proofFn⟩
instance Struct.instCoeDecl : Coe Struct Decl := ⟨Decl.struct⟩
instance Enum.instCoeDecl : Coe Enum Decl := ⟨Decl.enum⟩
instance FuncCheckSst.instCoeDecl : Coe FuncCheckSst Decl := ⟨Decl.func⟩

instance Assertion.instVName : VName Assertion := ⟨Assertion.name⟩
instance SpecFn.instVName : VName SpecFn := ⟨SpecFn.name⟩
instance ProofFn.instVName : VName ProofFn := ⟨ProofFn.name⟩
instance Struct.instVName : VName Struct := ⟨Struct.name⟩
instance Enum.instVName : VName Enum := ⟨Enum.name⟩
instance FuncCheckSst.instVName : VName FuncCheckSst := ⟨FuncCheckSst.name⟩
instance Decl.instVName : VName Decl where
  name := fun d => match d with
    | .assertion a => a.name
    | .specFn f => f.name
    | .proofFn f => f.name
    | .struct s => s.name
    | .enum e => e.name
    | .func f => f.name

--------------------------------------------------------------------------------

def Bind.idents : Bind → List (Ident × Typ)
  | .Let v ty _ => [(v, ty)]
  | .Quant _ vars => vars
  | .Lambda vars => vars

mutual

def Typ.decEq (t₁ t₂ : Typ) : Decidable (t₁ = t₂) := by
  cases t₁ <;> cases t₂
  <;> try { apply isFalse; intro h; injection h }
  <;> try { apply isTrue; rfl }
  <;> simp
  <;> try infer_instance
  -- Tuple
  · rename_i t₁ t₂ t₃ t₄
    match Typ.decEq t₁ t₃, Typ.decEq t₂ t₄ with
    | isTrue ht₁, isTrue ht₂ => simp [ht₁, ht₂]; exact instDecidableTrue
    | isFalse ht₁, _ => simp [ht₁]; exact instDecidableFalse
    | _, isFalse ht₂ => simp [ht₂]; exact instDecidableFalse
  -- Array
  · exact Typ.decEq _ _
  -- Struct/Enum
  all_goals
  ( rename_i i₁ f₁ i₂ f₂
    by_cases hi : i₁ = i₂
    <;> simp [hi]
    · exact Typ.decListEq f₁ f₂
    · exact instDecidableFalse )

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
  | .Struct _ params
  | .Enum _ params => 1 + params.attach.foldl (init := 0) (λ acc ⟨ty, _⟩ => max acc ty.height)
  | _ => 1

def Exp.height : Exp → Nat
  | .Const _
  | .Var _ => 1
  | .Unary _ e => 1 + e.height
  | .Call _ _ es => 1 + es.attach.foldl (init := 0) (λ acc ⟨e, _⟩ => max acc e.height)
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
  | .ArrayLiteral es => 1 + es.attach.foldl (init := 0) (λ acc ⟨e, _⟩ => max acc e.height)

/--
  Extracts the identifier in the expression.

  Some, but not all, of the `Exp` branches stand in for variable names
  and identifiers. This function gets out that identifier.

  Mainly used to elaborate `let` expressions at the Lean level.

  TODO: In Rust, you can use let expressions to decompose RHS expressions.
  In Lean, that is usually done with `have`. (But maybe `let` works as well?)

  TODO: CC Remove?
-/
def Exp.ident? : Exp → Option Ident
  | .Var i => some i
  | _ => none

end VerusLean
