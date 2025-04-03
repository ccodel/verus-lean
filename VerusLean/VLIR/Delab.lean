import VerusLean.VLIR.Elab
import Lean.PrettyPrinter
import Lean.Elab.Command
import Lean.Util.SearchPath

namespace VerusLean

open Lean PrettyPrinter

/-
  Attempts to take a list of `Decl`s, sorted with the spec functions first
  and the theorems/assertions last, and performs delaboration.

  Delaboration proceeds by adding prior definitions to the context/environment,
  just to ensure that everything type-checks.

  TODO: Support mutually-recursive functions
  TODO: Set the namespace to be `VerusLean` to prevent clash with e.g. `factorial` or `add`
    (CC: I think we're okay for most things, but root-level functions like `max`
         could be problematic.)
-/
unsafe def Decl.toFormat (ds : List Decl) : IO (Except String String) := do
  searchPathRef.set compile_time_search_path%
  let res : Except Exception Format ← Lean.withImportModules
    (imports := #[{ module := `Init }, { module := `VerusLean.Basic }, { module := `VerusLean.Tactic.ByVerus }])
    (opts := Options.empty)
    (trustLevel := 0)
    (fun env => EIO.toIO' <|
      Core.CoreM.run'
        (ctx := {
          -- Since we're not making an actual Lean file, use a dummy name.
          fileName := "Example.lean"
          fileMap := default
        })
        (s := { env })
        (do
          try
            -- Convert the `Decl`s into Lean `Term`s
            let syns : List (TSyntax `command) ← ds.mapM (·.toTerm.run')

            /-
              Now add the `Term`s into the meta-context to ensure that
              they type-check.

              This block of code doesn't actually extract any printable strings,
              but it acts as a good sanity check that things are okay.

              Note: Wojciech claims that lifting into `CommandElabM` multiple
              times causes bad things to happen, so do it only once.
            -/
            /-let _ ← Lean.liftCommandElabM <| syns.mapM (fun syn => do
              Elab.Command.elabCommandTopLevel syn.raw
            ) -/

            /-
              Now ask Lean for a pretty-printed version of the command syntax.
              This part is untrusted, in the sense that this can return
              bad Lean syntax (i.e., syntax that doesn't compile).
              However, the block above should prevent this from happening.
            -/
            let mut fmt : Format := ""
            for syn in syns do
              fmt := fmt ++ .line ++ (
                ← format (Formatter.categoryFormatter `command) syn
              ) ++ .line
            return fmt ++ .line
          catch e =>
            dbg_trace s!"{← e.toMessageData.toString}"
            throw e
        )
    )

  match res with
  | .error _ => return throw "bad syntax"
  | .ok res => return (return Std.Format.pretty res)

end VerusLean
