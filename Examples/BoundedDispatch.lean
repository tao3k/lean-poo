import LeanPoo.Object.Multimethod

/-! A service discovers renderer families at runtime. Calls through many
different C4 shapes retain only the most recent eight candidate sequences;
an evicted shape can always be resolved again from the method index. -/

namespace LeanPoo.Examples.BoundedDispatch

open LeanPoo.Object

abbrev Shape := List (List String)

def renderer (index : Nat) : Shape :=
  [[s!"Renderer{index}"], ["Json"]]

def generic : Multimethod Shape String (List String) :=
  { arity := 2
    precedence := id
    combine := fun methods _ => methods.toList }

def usage : Except MultimethodError
    (List String × Nat × List String × Nat) := do
  let initial ← generic.register [.any, .any] "fallback"
  let (before, _) ← initial.call (renderer 0)
  let mut current := initial
  for index in [:20] do
    let (_, updated) ← current.call (renderer index)
    current := updated
  let retained := current.cache.size
  let (after, refreshed) ← current.call (renderer 0)
  return (before, retained, after, refreshed.cache.size)

#eval usage

end LeanPoo.Examples.BoundedDispatch
