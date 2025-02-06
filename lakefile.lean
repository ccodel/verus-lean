import Lake
open Lake DSL

package «verus-lean» where
  -- add package configuration options here

lean_lib «VerusLean» where
  -- add library configuration options here

@[default_target]
lean_exe «verus-lean» where
  root := `Main

lean_exe VerusParser where
  root := `VerusLean.VLIRParser

require batteries from git "https://github.com/leanprover-community/batteries" @ "512d7fa38234139a34c04e3b3438fc142b51bbee"
