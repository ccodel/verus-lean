import VerusLean.VLIR.Elab
import Lean.PrettyPrinter
import Lean.Elab.Command
import Lean.Util.SearchPath

namespace VerusLean

open Lean PrettyPrinter

-- TODO: Replace with actual delaboration later

def Ident.pp (i : Ident) : String := i
def VarIdent.pp (i : VarIdent) : String := i.1

def Typ.pp (ty : Typ) : String :=
  match ty with
  | .Bool => "Bool"
  | .Int => "Int"
  | .Nat => "Nat"
  | .UInt w => s!"UInt{w}"
  | .SInt w => s!"Int{w}"
  | .Char => "Char"
  | .Array t => s!"Array ({Typ.pp t})"
  | _ => "Unit"

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

def Quant.pp (q : Quant) : String :=
  match q with
  | .Forall => "∀"
  | .Exists => "∃"

mutual

partial def Bind.pp (b : Bind) : String :=
  match b with
  | .Let v =>
    let valStr := Exp.pp v.val
    s!"let {v.name} := {valStr}; "
  | .Quant q vars =>
    let qStr := Quant.pp q
    let varsStr := vars.map (fun v => s!"({v.name} : {Typ.pp v.val})")
    s!"{qStr} {varsStr}, "
  | .Lambda vars =>
    let varsStr := vars.map (fun v => s!"({v.name} : {Typ.pp v.val})")
    s!"λ {varsStr} =>"

partial def Exp.pp (e : Exp) : String :=
  match e with
  | .Const c => Const.pp c
  | .Var ident => ident
  | .Unary op e =>
    let e := Exp.pp e
    "(" ++ UnaryOp.pp op ++ e ++ ")"
  | .Binary op lhs rhs =>
    let lhs := Exp.pp lhs
    let rhs := Exp.pp rhs
    "(" ++ lhs ++ BinaryOp.pp op ++ rhs ++ ")"
  | .If cond b₁ b₂ =>
    let cond := Exp.pp cond
    let b₁ := Exp.pp b₁
    let b₂ := Exp.pp b₂
    "if (" ++ cond ++ ") then (" ++ b₁ ++ ") else (" ++ b₂ ++ ")"
  | .Bind bnd exp =>
    let bnd := Bind.pp bnd
    let exp := Exp.pp exp
    bnd ++ exp
  | .Call fn _ exps =>
    dbg_trace s!"delab get here?"
    let fn := match fn with
      | CallFun.Fun fn => fn
    -- let typs := typs.map Typ.pp
    dbg_trace s!"delab get here!!"
    let exps := exps.map Exp.pp
    let exps := String.intercalate ", " exps
    fn ++ "(" ++ exps ++ ")"

end /- mutual -/

def Exp.toTheoremString (e : Exp) (name : String := "verus_thm") (decls : String := "") : String :=
  "theorem " ++ name ++ " " ++ decls ++ ": " ++ Exp.pp e ++ " := by sorry\n\n"

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
            -- dbg_trace "Delaborating"
            let syns ← Lean.liftCommandElabM d.toSyntax
            -- dbg_trace "Performing typechecking"
            for syn in syns do
              -- dbg_trace s!"{syn}"
              Lean.liftCommandElabM <| Elab.Command.elabCommandTopLevel syn
            -- dbg_trace "Formatting"
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
