import Lean.Elab.Tactic

namespace VerusLean

open Lean Elab

-- TODO: Log the current hypothesis to the infoview
-- For now, leave it as a sorry wrapper

macro (name := byVerus) "verus" : tactic =>
  `(tactic| sorry)

-- Stand-in automation tactic to discharge trivial proofs.
macro (name := byAuto) "auto?" : tactic => `(tactic|
    first
    | trivial
    | rfl
    | assumption
    | simp
    | omega
    | grind
  )

end VerusLean
