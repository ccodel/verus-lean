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

def Ident := String
deriving ToJson, FromJson, Repr, DecidableEq, Hashable, Inhabited

def Idents := Array Ident
deriving ToJson, FromJson, Repr, DecidableEq, Hashable, Inhabited

-- CC: Figure out `ToJson`, `FromJson` here, because Rust's serialization is different

-- CC: A pair, because the second element is a disambiguation (a way to tell apart two identical variable strings)
--     that I didn't want to implement atm
def VarIdent := (Ident × Unit)
deriving Repr, DecidableEq, Inhabited

inductive Mode where
  | Spec
  | Proof
  | Exec
deriving Repr, DecidableEq, Hashable, Inhabited

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
/-
inductive Typ
  /-- Bool, Int, Datatype are translated directly into corresponding SMT types (they are not SMT-boxed) -/
  | Bool
  | Int : IntRange → Typ
  /-- UTF-8 character type -/
  | Char
  /--
    `FnSpec` type (TODO rename from 'Lambda' to just 'FnSpec')
    (t1, ..., tn) -> t0. -/
  | Lambda : Array Typ → Typ → Typ
  /-- Datatype (concrete or abstract) applied to type arguments -/
  | Datatype : Path → Array Typ → Typ
  | Array : Typ → Typ → Typ
  | Slice : Typ → Typ
  /-- Type parameter (inherently SMT-boxed, and cannot be unboxed) -/
  | TypParam : Ident → Typ
  /-- Const integer type argument (e.g. for array sizes) -/
  | ConstInt : Int → Typ
deriving ToJson, FromJson, Repr, Inhabited -/

inductive Typ where
  | Bool
  | Int                   /- Mathematical integers            -/
  | Nat                   /- Mathematical natural numbers     -/
  | UInt (width : Nat)    /- Unsigned fixed-width integers    -/
  | SInt (width : Nat)    /- Signed fixed-width integers      -/
  | Char
  | StrSlice
  -- | ConstInt (i : Int)    /- Const integer type argument      -/
  | Array (t : Typ)       /- Array, ignore length in Rust     -/
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
  /-- Euclidean divisoin on `IntRange` (round towards -inf, not round-towards-zero truncation). -/
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
  | Trigger
deriving Repr, Inhabited

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

def VarBinders := List (Ident × Typ)
deriving Repr, Inhabited

inductive Bind where
  -- | Let ()
  | Quant (q : Quant) (vars : VarBinders)
  -- | Lambda ()
  -- | Choose ()
deriving Repr, Inhabited

/--
  Flattened Verus expressions.

  Expressions have return values.
-/
inductive ExpX where
  /-- Constant value literals. -/
  | Const (c : Const)
  /-- Local variables, as a right-hand side of an expression. -/
  | Var (ident : Ident)
  /-- Primitive unary function application. -/
  | Unary (op : UnaryOp) (arg : ExpX)
  -- | UnaryOpr (op : UnaryOp) (arg : ExpX)
  /-- Primitive binary function application. -/
  | Binary (op : BinaryOp) (arg₁ arg₂ : ExpX)
  -- | BinaryOpr (op : BinaryOp) (arg₁ arg₂ : ExpX)
  | If (cond branch₁ branch₂ : ExpX)
  -- | ArrayLiteral (elems : Array ExpX)
  | Bind (bind : Bind) (exp : ExpX)
deriving Repr, Inhabited

abbrev Exps := Array ExpX

/--
  Flattened Verus statements.

  Statements don't have return values.
-/
/-
inductive StmX where
  -- CC: Is this needed, since the only way assertions end up in Lean is via AssertLean?
  -- A normal Verus assertion.
  --| Assert (exp : ExpX)
  -- An assertion on a bitvector statement.
  -- | AssertBitVector (requires ensures : Exps)
  --| Return ()
  /-- If-statements. Second branch can be optionally omitted. -/
  | If (exp : ExpX) (branch₁ : StmX) (branch₂ : Option StmX)
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
  dest : Option VarIdent
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

/-
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FuncCheckSst {
    pub reqs: Exps,
    pub post_condition: Arc<PostConditionSst>,
    pub mask_set: Arc<crate::inv_masks::MaskSetE<Exp>>,
    pub unwind: UnwindSst,
    pub body: Stm,
    pub local_decls: Arc<Vec<LocalDecl>>,
    pub statics: Arc<Vec<Fun>>,
}
 -/

/--
  These are top-level "Lean" objects that Lean will evantually turn into
  `def`s and `theorem`s. See `Elab.lean`.
-/
inductive Decl where
  | assertion (theoremName : Ident) (decls : Std.HashMap Ident Typ) (exp : ExpX)
  --| func (f : FuncCheckSST)
deriving Repr, Inhabited

end VerusLean
