import Lean

namespace Vstd

def Map (α : Type u) (β : Type v) := α → Option β
  --List (α × β)

namespace Map

--instance Map.instDecEq [DecidableEq α] [DecidableEq β] (m₁ m₂ : Map α β) : Decidable (m₁ = m₂) := by
  --induction m₁ <;>

end Map

end Vstd
