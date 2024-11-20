-- Facts on moands


namespace EStateM

def coeWithState : Except ε α → EStateM ε σ α
  | .ok a => (fun s => Result.ok a s)
  | .error e => (fun s => Result.error e s)

instance coeExcept : Coe (Except ε α) (EStateM ε σ α) where
  coe := coeWithState

end EStateM
