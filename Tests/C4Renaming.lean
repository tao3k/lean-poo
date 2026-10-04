import LeanPoo.C4.Renaming
import LeanPoo.C4.AuditedResolver

namespace LeanPoo.Tests.C4Renaming
open C4

private def prefixed (name : String) := "数学::" ++ name
private theorem prefixed_injective : Function.Injective prefixed := by
  intro a b same
  exact (String.append_right_inj "数学::").mp same

private def swap (name : String) : String :=
  if name = "A" then "B" else if name = "B" then "A" else name
private theorem swap_twice (name : String) : swap (swap name) = name := by
  by_cases a : name = "A"
  · subst name; decide
  · by_cases b : name = "B"
    · subst name; decide
    · simp [swap, a, b]
private theorem swap_injective : Function.Injective swap := by
  intro a b same
  have twice := congrArg swap same
  simpa only [swap_twice] using twice

-- Generic client: migration maps the retained data; fresh compiler execution
-- is needed only by this independent regression, not by the public operation.
example (order : VerifiedOrder graph root) (unique : (graph.nodes.map Node.name).Nodup) :
    (order.rename prefixed prefixed_injective unique).precedes (prefixed left) (prefixed right) =
      order.precedes left right := order.rename_precedes prefixed prefixed_injective unique

#eval do
  IO.println "C4-RENAMING-START"
  let mut families := 0
  let mut runs := 0
  let mut accepted := 0
  let mut pairs := 0
  for p in [[["A"]], [["A", "B"]], [["B", "A"]], [[], ["A"], ["A"], []]] do
    for s in [[["A"]], [["B"]], [["A", "B"]], [["B", "A"]]] do
      for flags in List.range 4 do
        for localOrders in [[["P", "S"]], [["S", "P"]], [["P"], ["S"]], [[], ["P", "S"], ["P"], []]] do
          let graph : Graph := { nodes := [
            {name := "A"}, {name := "B"},
            {name := "P", parentOrders := p, suffix := flags % 2 == 1},
            {name := "S", parentOrders := s, suffix := flags / 2 == 1},
            {name := "Root", parentOrders := localOrders}] }
          have unique : (graph.nodes.map Node.name).Nodup := by
            change ["A", "B", "P", "S", "Root"].Nodup
            decide
          for transformation in [(⟨prefixed, prefixed_injective⟩ : {f : String → String // Function.Injective f}),
              ⟨swap, swap_injective⟩] do
            let renamed := graph.rename transformation.val
            let original := linearizeAuditedVerified graph "Root"
            let rebuilt := linearizeAuditedVerified renamed (transformation.val "Root")
            unless (rebuilt.map VerifiedOrder.output).toOption ==
                ((original.map VerifiedOrder.output).toOption.map (List.map transformation.val)) do
              throw (IO.userError "renamed execution success/output differs")
            if let .ok order := original then
              let migrated := order.rename transformation.val transformation.property unique
              let .ok fresh := rebuilt | throw (IO.userError "fresh renamed compilation failed")
              unless migrated.output == fresh.output do
                throw (IO.userError "transported order differs from independent compilation")
              for left in ["Root", "P", "S", "A", "B", "Missing"] do
                for right in ["Root", "P", "S", "A", "B", "Missing"] do
                  unless migrated.precedes (transformation.val left) (transformation.val right) ==
                      order.precedes left right do
                    throw (IO.userError "renaming changed pair query")
                  pairs := pairs + 1
              accepted := accepted + 1
            runs := runs + 1
          families := families + 1
          if families % 64 == 0 then IO.println s!"C4-RENAMING-PROGRESS families={families}"
  unless runs == 512 && accepted == 232 && pairs == 8352 do
    throw (IO.userError "unexpected renaming corpus size")
  IO.println s!"C4-RENAMING-OK families={families} runs={runs} accepted={accepted} pairs={pairs}"

private def diamond : Graph := {nodes := [{name := "A"}, {name := "B"},
  {name := "Root", parentOrders := [["A", "B"]]}]}
#guard (linearizeChecked diamond "Root").toOption == some ["Root", "A", "B"]
-- A noninjective map changes identity and validation, not just labels.
#guard (linearizeChecked (diamond.rename (fun _ => "Same")) "Same").toOption.isNone

#eval do
  let malformed : List Graph := [
    {nodes := [{name := "Root", parentOrders := [["Unknown"]]}]},
    {nodes := [{name := "Root", parentOrders := [["Root"]]}]},
    {nodes := [{name := "Root"}, {name := "Root"}]}]
  for graph in malformed do
    unless (linearizeAudited (Graph.rename graph prefixed) (prefixed "Root")).toOption.isNone do
      throw (IO.userError "renaming admitted malformed graph")
  IO.println "C4-RENAMING-BOUNDARIES-OK malformed=3 collapse=1"

#print axioms Renaming.choose
#print axioms Renaming.trace
#print axioms Renaming.node
#print axioms GraphTrace.rename
#print axioms VerifiedOrder.rename
#print axioms VerifiedOrder.rename_unique
#print axioms VerifiedOrder.rename_precedes
end LeanPoo.Tests.C4Renaming
