import VerusLean.VLIR.Elab
import Lean.PrettyPrinter
import Lean.Elab.Command
import Lean.Util.SearchPath

namespace VerusLean

open Lean PrettyPrinter

-- TODO: Replace with actual delaboration later

def Ident.pp (i : Ident) : String := i
def VarIdent.pp (i : VarIdent) : String := i.1

def Const.pp (c : Const) : String :=
  match c with
  | .Bool b => toString b
  | .Int i => toString i
  | .StrSlice s => s
  | .Char c => toString c

def BitwiseOp.pp (op : BitwiseOp) : String :=
  match op with
  | .BitXor => " ^^^ "
  | .BitAnd => " &&& "
  | .BitOr  => " ||| "
  | .Shr _ => " >>> "
  | .Shl _ _ => " <<< "

def ArithOp.pp (op : ArithOp) : String :=
  match op with
  | .Add => " + "
  | .Sub => " - "
  | .Mul => " * "
  | .EuclideanDiv => " / "
  | .EuclideanMod => " % "

def InequalityOp.pp (op : InequalityOp) : String :=
  match op with
  | .Lt => " < "
  | .Le => " ≤ "
  | .Gt => " > "
  | .Ge => " ≥ "

def UnaryOp.pp (op : UnaryOp) : String :=
  match op with
  | .Not => "!"
  | .BitNot _ => "!"
  | _ => "unsupported unary op"

def BinaryOp.pp (op : BinaryOp) : String :=
  match op with
  | .And => " ∧ "
  | .Or => " ∨ "
  | .Xor => " ^^ "
  | .Implies => " → "
  | .Eq _ => " = "
  | .Ne => " ≠ "
  | .Inequality ineq => InequalityOp.pp ineq
  | .Arith arith _ => ArithOp.pp arith
  | .Bitwise bitwise _ => BitwiseOp.pp bitwise

def Bind.pp (b : Bind) : String :=
  match b with
  | Quant Quant.Forall _ => "∀"
  | Quant Quant.Exists _ => "∃"

partial def ExpX.pp (e : ExpX) : String :=
  match e with
  | .Const c => Const.pp c
  | .Var ident => ident
  | .Unary op e =>
    let e := ExpX.pp e
    "(" ++ UnaryOp.pp op ++ e ++ ")"
  | .Binary op lhs rhs =>
    let lhs := ExpX.pp lhs
    let rhs := ExpX.pp rhs
    "(" ++ lhs ++ BinaryOp.pp op ++ rhs ++ ")"
  | .If cond b₁ b₂ =>
    let cond := ExpX.pp cond
    let b₁ := ExpX.pp b₁
    let b₂ := ExpX.pp b₂
    "if (" ++ cond ++ ") then (" ++ b₁ ++ ") else (" ++ b₂ ++ ")"
  -- | .ArrayLiteral es =>
  --   let es := es.map ExpX.pp
  --   "#[" ++ String.intercalate ", " es.toList ++ "]"
  | .Bind bnd exp =>
    let bnd := Bind.pp bnd
    let exp := ExpX.pp exp
    bnd ++ ", " ++ exp
  | .Call fn typs exps =>
    dbg_trace s!"delab get here?"
    let fn := match fn with
      | CallFun.Fun fn => fn
    -- let typs := typs.map Typ.pp
    dbg_trace s!"delab get here!!"
    let exps := exps.map ExpX.pp
    let exps := String.intercalate ", " exps
    fn ++ "(" ++ exps ++ ")"

def ExpX.toTheoremString (e : ExpX) (name : String := "verus_thm") (decls : String := "") : String :=
  "theorem " ++ name ++ " " ++ decls ++ ": " ++ ExpX.pp e ++ " := by sorry\n\n"

-- def ?.toDefString (name : String) (decls : String := "") (retTyp : String) (e : ExpX) : String :=
--   "def " ++ name ++ decls ++ " : " ++ retTyp ++ " := " ++ ExpX.pp e ++ "\n\n"
-- def add_one (x : Int) : Int := x + 1

unsafe def Decl.toFormat (d : Decl) : IO String := do
  searchPathRef.set compile_time_search_path%
  let res : Except Exception Format ← Lean.withImportModules
    (imports := #[{ module := `Init : Import }])
    (opts := Options.empty)
    (trustLevel := 0)
    (fun env => EIO.toIO' <|
      Core.CoreM.run'
        (ctx := {
          fileName := "Example.lean"
          fileMap := default
        })
        (s := {
          env
        })
        (do
          try
            dbg_trace "Delaborating"
            let syns ← Lean.liftCommandElabM d.toSyntax
            dbg_trace "Performing typechecking"
            for syn in syns do
              dbg_trace s!"{syn}"
              Lean.liftCommandElabM <| Elab.Command.elabCommandTopLevel syn
            dbg_trace "Formatting"
            let mut fmt : Format := ""
            for syn in syns do
              fmt := fmt ++ .line ++ (
                ← Lean.PrettyPrinter.format (Formatter.categoryFormatter `command) syn
              )
            return fmt
          catch e =>
            dbg_trace s!"{← e.toMessageData.toString}"
            throw e
        )
    )
  match res with
  | .error _ => return "bad syntax"
  | .ok res => return Std.Format.pretty res

end VerusLean
