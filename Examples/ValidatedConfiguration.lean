import LeanPoo.Functional.Codec

/-! A context-dependent descriptor for nested weighted routes: each route is
positive and bounded; the entire configuration has a joint capacity constraint.
Two wire layouts feed the same proof-aware consumer, including exact refusals. -/
namespace LeanPoo.Examples.ValidatedConfiguration
open Functional

abbrev Route (capacity : Nat) :=
  {entry : String × Nat // 0 < entry.2 ∧ entry.2 ≤ capacity}

def load {capacity : Nat} (routes : List (Route capacity)) : Nat :=
  (routes.map (fun route => route.val.2)).sum

abbrev Configuration (capacity : Nat) := {routes : List (Route capacity) // load routes ≤ capacity}

def routeCodec (capacity : Nat) : Codec (Route capacity) (String × Nat) String :=
  ((Codec.identity String String).product (Codec.identity Nat String)).refine
    (fun entry => 0 < entry.2 ∧ entry.2 ≤ capacity) "route outside capacity"

def schema : Factory Nat (fun capacity => Codec (Configuration capacity) (List (String × Nat)) String) :=
  fun capacity => (routeCodec capacity).list.refine
    (fun routes => load routes ≤ capacity) "combined load outside capacity"

def alternate (capacity : Nat) : Codec (Configuration capacity) (List (Nat × String)) String :=
  (schema capacity).represent (List.map Prod.swap) (List.map Prod.swap) (by
    intro rows
    induction rows with
    | nil => rfl
    | cons row rest ih => simp [ih])

structure Summary (capacity : Nat) where
  names : List String
  total : Nat
  bounded : total ≤ capacity

def summarize {capacity : Nat} (configuration : Configuration capacity) : Summary capacity :=
  ⟨configuration.val.map (fun route => route.val.1), load configuration.val, configuration.property⟩

def configure (rows : List (String × Nat)) : Factory Nat (fun capacity => Except String (Summary capacity)) :=
  fun capacity => ((schema capacity).decode rows).map summarize

/-- Public results and errors agree for every wire batch, even invalid ones. -/
theorem layouts_agree (capacity : Nat) (rows : List (String × Nat)) :
    ((alternate capacity).decode (rows.map Prod.swap)).map summarize = configure rows capacity := by
  rw [alternate, Codec.represent_decode]
  rfl

/-- A valid configuration round-trips with all per-route and joint proofs. -/
theorem configuration_roundtrip (capacity : Nat) (configuration : Configuration capacity) :
    (schema capacity).decode ((schema capacity).encode configuration) = .ok configuration :=
  (schema capacity).decode_encode configuration

-- Per-item admission is useful independently of the joint configuration check.
def validateRoutes (rows : List (String × Nat)) :=
  Factory.traverseExcept rows (fun capacity => (routeCodec capacity).decode)

#guard ((configure [("api", 3), ("worker", 4)] 10).toOption.map (·.total)) == some 7
#guard (configure [("api", 6), ("worker", 6)] 10).toOption.isNone
#guard ((schema 10).decode [("api", 6), ("worker", 6)]).toOption.isNone
#guard ((schema 10).decode [("bad", 0), ("overflow", 30)]).toOption.isNone
#guard ((schema 10).decode []).toOption.isSome

#eval do
  for rows in [[("api", 3), ("worker", 4)], [("api", 6), ("worker", 6)],
      [("bad", 0), ("overflow", 30)], []] do
    match configure rows 10 with
    | .ok summary => IO.println s!"accepted routes={summary.names}, load={summary.total} <= 10"
    | .error message => IO.println s!"configuration refused: {message}"

end LeanPoo.Examples.ValidatedConfiguration
