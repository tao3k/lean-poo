import LeanPoo.C4.Linearize

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

def main : IO Unit := do
  for count in [32, 64, 128, 256] do
    sample "chain" (chain count) (toString (count - 1))
    sample "fanIn" (fanIn count) "Root"
