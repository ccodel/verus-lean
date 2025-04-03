import Lean
import Lean.PrettyPrinter
import VerusLean

open VerusLean

open Lean PrettyPrinter
open VName

def extract (j : Json) : (Exp × VarMap × DeclMap) :=
  match Exp.fromJson j default with
  | .ok exp st => (exp, st.freeVars, st.decls)
  | .error e _ =>
    dbg_trace e
    (.Const (.Bool true), ∅, ∅)

def preludeString := "import VerusLean.Basic\nimport VerusLean.Tactic.ByVerus\n\nnamespace VerusLean\n"
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

unsafe def genFromDir' (dirPath : String) : IO String := do
  -- Get all the files in the requested directory
  let files ← System.FilePath.walkDir dirPath

  /-
    Currently, each assertion (filename) is tagged with an increasing ID.
    Later assertions may depend on earlier spec functions or assertions.

    TODO: Place all asserts into one file? Use something other than IDs?
  -/
  let files := files.insertionSort (fun a b =>
    let a := a.toString
    let b := b.toString
    if a.length < b.length then true
    else if a.length > b.length then false
    else a < b)

  -- Accumulate the function map, assertions, and proof functions across all files
  -- Store serializations that fail to parse as error strings
  -- We use an `Array` for `Assertion`s because `push` is O(1) for arrays
  let (fmap, dtmap, asserts, prooffns, failures) ← files.foldlM (init := ((∅, ∅, #[], #[], "") : FnMap × DeclMap × Array Assertion × Array FuncCheckSst × String))
    (fun (fnmap, dtmap, as, ps, str) filePath => do
    match ← Decls.fromFile? filePath.toString with
    | .ok ds => do
      let ⟨fnmap, dtmap, as, ps⟩ ←
        ds.foldlM (init := (fnmap, dtmap, as, ps)) (fun (fnmap, dtmap, as, ps) decl => do
          match decl with
          | .specFn f => return (fnmap.insert (name f) f, dtmap, as, ps)
          | .proofFn f => return (fnmap, dtmap, as, ps) -- CC TODO This is broken
          | .struct s => return (fnmap, dtmap.insert (name s) s, as, ps)
          | .enum e => return (fnmap, dtmap.insert (name e) e, as, ps)
          | .assertion a => return (fnmap, dtmap, as.push a, ps)
          | .func f => return (fnmap, dtmap, as, ps.push f))
      return (fnmap, dtmap, as, ps, str)
    | .error e => do
      dbg_trace e
      return (fnmap, dtmap, as, ps, str ++ s!"-- The JSON at {filePath} failed to generate\n\n")
  )

  let decls := dtmap.values
               ++ fmap.values.map (.specFn ·)
               ++ asserts.toList.map (.assertion ·)
               ++ prooffns.toList.map (.func ·)

  match ← Decl.toFormat decls with
  | .ok s => return s ++ failures
  | .error e => return s!"Error: {e}"

unsafe def main : List String → IO Unit
  | [path] => do
    let res ← Decls.fromFile? path
    match res with
    | .ok decls =>
      match ← Decl.toFormat decls with
      | .ok str => IO.println <| preludeString ++ str ++ postludeString
      | .error e => IO.println s!"Error: {e}"
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
