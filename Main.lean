import Lean
import Lean.PrettyPrinter
import VerusLean

open VerusLean

open Lean PrettyPrinter

def extract (j : Json) : (Exp × VMap × FMap) :=
  match Exp.fromJson? j default with
  | .ok exp st => (exp, st.freeVars, st.fns)
  | .error e _ =>
    dbg_trace e
    (.Const (.Bool true), ∅, ∅)

def preludeString := "import VerusLean.Basic\n\nnamespace VerusLean\n"
def postludeString := "end VerusLean"

/-
def genFromDir (dirPath : String) : IO String := do
  -- For each file in the directory
  let files ← System.FilePath.walkDir dirPath
  let (str, _) ← files.foldlM (init := ("", 1)) (fun (str, counter) entry => do
    -- Get out the filepath in the entry, open it, and run `genFromFile`
    let res ← Exp.fromFile? entry.toString
    match res with
    | .ok (e, map) =>
      let declsString := map.fold (init := "") (fun str k v => str ++ s!"({k} : {v.toSyntax}) ")
      let str := str ++ e.toTheoremString (name := s!"verus_thm_{counter}") (decls := declsString)
      return (str, counter + 1)
    | .error _ => do
      -- TODO: Error handling?
      let str := str ++ s!"-- The JSON at {entry} failed to generate\n\n"
      return (str, counter)
  )

  return str -/

#check addDecl

unsafe def genFromDir' (dirPath : String) : IO String := do
  -- For each file in the directory
  let files ← System.FilePath.walkDir dirPath
  let files := files.insertionSort (fun a b => a.toString < b.toString)
  let str ← files.foldlM (init := "") (fun str entry => do
    let res ← Decls.fromFile? entry.toString
    match res with
    | .ok decls => do
      --let mut res := str

      let res ← decls.foldrM (init := str) (fun d res => do
        let fmt ← d.toFormat
        dbg_trace s!"Adding formatted {fmt}"
        return res ++ fmt ++ "\n\n"
      )

      -- for debugging purpose, avoid segfault: function expected at add_one
      --let d := decls.get! 0
      --let fmt ← d.toFormat
      --res := res ++ fmt ++ "\n\n"

      return res
      -- return str ++ fmt ++ "\n\n"
    | .error e => do
      dbg_trace e
      let str := str ++ s!"-- The JSON at {entry} failed to generate\n\n"
      return str
  )

  return str

unsafe def main : List String → IO Unit
  | [path] => do
    let res ← Decls.fromFile? path
    match res with
    | .ok ds =>
      --let declsString := map.fold (init := " ") (fun str k _ => str ++ s!"({k} : Bool) ")
      --IO.println <| preludeString ++ e.toTheoremString (decls := declsString) ++ postludeString
      IO.println "Ignored for now"
    | .error e => IO.println e
  | ["dir", path] => do
    -- IO.println "Reading from a directory"
    let res ← genFromDir' path
    IO.println <| preludeString ++ res ++ postludeString
  | [path, toFile] => do
    /-let res ← Exp.fromFile? path
    match res with
    | .ok (e, map) =>
      let declsString := map.fold (init := "") (fun str k _ => str ++ s!"({k} : Bool) ")
      IO.FS.writeFile toFile (preludeString ++ e.toTheoremString (decls := declsString) ++ postludeString)
    | .error e => IO.println e-/
    IO.println "Ignored for now"
  | ["dir", path, toFile] => do
    -- IO.println "Reading from a directory"
    let res ← genFromDir' path
    IO.FS.writeFile toFile (preludeString ++ res ++ postludeString)
  | _ =>
    IO.println "Wrong number of arguments"

#exit
--#check Elab.Command.liftTermElabM
--#check delab
#check ppCommand
#check ppTerm
#check PPContext
#check Environment

/-
structure PPContext where
  env           : Environment
  mctx          : MetavarContext := {}
  lctx          : LocalContext := {}
  opts          : Options := {}
  currNamespace : Name := Name.anonymous
  openDecls     : List OpenDecl := []
-/

#check Lean.liftCommandElabM
#check Elab.TermElabM Term

unsafe def formatter (t : Elab.TermElabM Term) : IO String := do
  let r ← Elab.Command.liftTermElabM t

  let res : Except Exception Format ← Lean.withImportModules
    (imports := #[`Init])
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
          Lean.PrettyPrinter.ppCategory `hello syn
          /-let mut fmt : Format := ""
          let syn ← Lean.liftCommandElabM syn
          for c in syn do
            Lean.liftCommandElabM <| Elab.Command.elabCommandTopLevel c
          for c in syn do
            fmt := fmt ++ .line ++ (
              ← Lean.PrettyPrinter.format (Formatter.categoryFormatter `command) c
            )
          return fmt -/
        )
    )
  match res with
  | .error _ => return "bad syntax"
  | .ok res => return Std.Format.pretty res

#eval formatter synF1



/-

opaque STOP_ON_ERROR : Bool := true

def format (formatter : Formatter) (stx : Syntax) : CoreM Format := do
  trace[PrettyPrinter.format.input] "{Std.format stx}"
  let options ← getOptions
  let table ← Parser.builtinTokenTable.get
  catchInternalId backtrackExceptionId
    (do
      let (_, st) ← (Formatter.concat formatter { table, options }).run { stxTrav := .fromSyntax stx }
      let mut f := st.stack[0]!
      if pp.oneline.get options then
        let mut s := f.pretty' options |>.trim
        let lineEnd := s.find (· == '\n')
        if lineEnd < s.endPos then
          s := s.extract 0 lineEnd ++ " [...]"
        -- TODO: preserve `Format.tag`s?
        f := s
      return .fill f)
    (fun ex => throwError "format: uncaught backtrack exception: {ex.toMessageData}")

unsafe def main (args : List String) : IO Unit := do
  let path := args[0]!
  let resPath := args[1]!
  IO.println s!"Reading file {path}"
  let json_str ← IO.FS.readFile path
  let fns ← do
    let arr ← IO.ofExcept <| (do (← Lean.Json.parse json_str).getArr?)
    arr.filterMapM fun j => do
      match Function.fromJson? j with
      | .ok j => return some j
      | .error e =>
        if STOP_ON_ERROR then
          throw (.userError e)
        else
          IO.println e
          return none
  IO.println s!"Converting functions to Lean syntax"
  let fns' ← Lean.withImportModules
    (imports := #[`Init])
    (opts := Options.empty)
    (trustLevel := 0)
    <| fun env => EIO.toIO' <|
    Lean.Core.CoreM.run'
      (ctx := {
        fileName := "Example.lean"
        fileMap := default
      })
      (s := {
        env
      })
      (fns.filterMapM (fun f => do
        IO.println s!"{f.id.segments}: processing"
        try
          let syn ← Lean.liftCommandElabM (Function.toSyntax f)
          IO.println s!"{f.id.segments}: typechecking"
          for c in syn do
            Lean.liftCommandElabM <| Elab.Command.elabCommandTopLevel c
          IO.println s!"{f.id.segments}: formatting"
          let mut fmt : Format := ""
          for c in syn do
            fmt := fmt ++ .line ++ (
              ← _root_.format (Formatter.categoryFormatter `command) c
            )
          IO.println s!"{f.id.segments}: done"
          return some fmt
        catch exc =>
          IO.println s!"{f.id.segments}: error: {← exc.toMessageData.toString}"
          return none)
      )
  match fns' with
  | .error exc =>
    IO.println (← exc.toMessageData.toString)
  | .ok fns' =>
  IO.println s!"Writing syntax to file {resPath}"
  let formatted : Lean.Format :=
    fns'.foldr (fun x acc => x ++ .line ++ .line ++ acc)
      ""
  IO.FS.writeFile resPath (formatted.pretty)
  IO.println s!"Finished!"

#eval main ["example/example_verus/vir.json", "example/example_verus/Example.lean"]

-/
