import LeanPoo.C4.Prepared

open LeanPoo.C4

private def chain (count : Nat) : Graph :=
  { nodes := (List.range count).map fun index =>
      { name := toString index
        parentOrders := if index == 0 then [] else [[toString (index - 1)]] } }

private def fanIn (count : Nat) : Graph :=
  let leaves := (List.range count).map fun index =>
    ({ name := s!"L{index}" } : Node)
  let names := leaves.map Node.name
  { nodes := leaves ++ [{ name := "Root", parentOrders := [names] }] }

private def sample (shape : String) (graph : Graph) (root : String) : IO Unit := do
  let started ← IO.monoNanosNow
  let result := linearize graph root
  let .ok order := result | throw (IO.userError s!"C4 failed: {repr result}")
  unless order.length == graph.nodes.length do
    throw (IO.userError "C4 precedence length mismatch")
  let elapsedUs := ((← IO.monoNanosNow) - started) / 1000
  IO.println s!"shape={shape} nodes={graph.nodes.length} elapsed_us={elapsedUs} precedence={order.length}"

@[noinline] private def execute (run : String → Except Error (List String))
    (roots : List String) : IO (List (Except Error (List String))) := pure (roots.map run)

private def shared (shape : String) (graph : Graph) : IO Unit := do
  let names := graph.nodes.map Node.name
  let requests := names ++ names
  let start ← IO.monoNanosNow
  let reference ← execute (linearize graph) requests
  let ordinary ← IO.monoNanosNow
  let prepared := prepare graph
  let actual ← execute prepared.at requests
  let finished ← IO.monoNanosNow
  unless reprStr actual == reprStr reference do
    throw (IO.userError "shared C4 changed complete result")
  IO.println s!"C4-PREPARED-SCALE shape={shape} nodes={names.length} requests={requests.length} ordinary_ns={ordinary-start} prepare_and_replay_ns={finished-ordinary} equal=true"
  IO.println s!"measurement: c4.{shape}.nodes{names.length}.ordinary {ordinary-start} ns"
  IO.println s!"measurement: c4.{shape}.nodes{names.length}.prepared {finished-ordinary} ns"

def main : IO Unit := do
  for count in [32, 64, 128, 256] do
    sample "chain" (chain count) (toString (count - 1))
    sample "fanIn" (fanIn count) "Root"
    shared "chain" (chain count)
    shared "fanIn" (fanIn count)
