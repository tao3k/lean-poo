import LeanPoo.C4.VerifiedOrder

namespace LeanPoo.Tests.VerifiedOrder
open C4 LinearizeState

example (valid : MetadataInvariant graph table)
    (success : resolveNode (nodeIndex graph) root name table true fuel = .ok ready) :
    MetadataInvariant graph ready ∧ CacheGrowth table ready (Ancestor graph · name) ∧
      ∃ entry, lookup ready name = some entry := resolveNode_checked_sound valid success

example (success : linearizeChecked graph root = .ok output) :
    ∃ tail, GraphTrace graph root output tail := linearizeChecked_graph_sound success

example (order : C4.VerifiedOrder graph root) : linearize graph root = .ok order.output := order.compiled

example (index : AncestryIndex graph root) (query : String)
    (yes : index.isAncestor query = true) : Ancestor graph query root := index.isAncestor_iff.mp yes

example (index : AncestryIndex graph root) (query : String)
    (no : index.isAncestor query = false) : ¬ Ancestor graph query root := by
  intro path
  have yes := index.isAncestor_iff.mpr path
  rw [no] at yes
  cases yes

/- Client code can use the index's executable decision without installing a
global graph-ancestry instance or traversing the graph again. -/
def ancestryDecision (index : AncestryIndex graph root) (query : String) :
    {answer : Bool // answer = true ↔ Ancestor graph query root} :=
  letI := index.decideAncestor query
  ⟨decide (Ancestor graph query root), by simp⟩

private def sameResult : Except Error (List String) → Except Error (List String) → Bool
  | .ok first, .ok second => first == second
  | .error first, .error second => first == second
  | _, _ => false

#eval do
  let mut families := 0
  let mut accepted := 0
  IO.println "VERIFIED-ORDER-START"
  for a in [[], [["B"]], [["Missing"]], [["A"]]] do
    for b in [[], [["A"]], [["Missing"]], [["B"]]] do
      for parents in [[], [["A", "B"]], [["B", "A"]], [[], ["A"], ["A"], []]] do
        for flags in List.range 8 do
          let graph : Graph := { nodes := [
            { name := "A", parentOrders := a, suffix := flags % 2 == 1 },
            { name := "B", parentOrders := b, suffix := flags / 2 % 2 == 1 },
            { name := "Root", parentOrders := parents, suffix := flags / 4 % 2 == 1 }] }
          let verified := linearizeVerified graph "Root"
          unless sameResult (verified.map (fun (order : C4.VerifiedOrder graph "Root") => order.output))
              (linearizeChecked graph "Root") do
            throw (IO.userError "verified projection changed output or error")
          match verified with
          | .error _ => pure ()
          | .ok order =>
            unless (reconstruct graph "Root").toOption.map (fun (result : GraphResult graph "Root") => result.output) ==
                some order.output do
              throw (IO.userError "original graph reconstruction disagrees")
            let index := order.indexAncestors
            for query in ["Root", "A", "B", "Missing", "Unused"] do
              unless index.isAncestor query == order.isAncestor query &&
                  (ancestryDecision index query).val == index.isAncestor query do
                throw (IO.userError "indexed ancestry decision disagrees")
            accepted := accepted + 1
          families := families + 1
          if families % 128 == 0 then IO.println s!"VERIFIED-ORDER-PROGRESS families={families}"
  IO.println s!"VERIFIED-ORDER-OK families={families} accepted={accepted}"

private def disconnected : Graph := { nodes := [
  { name := "Root" }, { name := "Broken", parentOrders := [["Missing"]] },
  { name := "Unused" }, { name := "Unused" }] }
#guard (linearizeVerified disconnected "Root").toOption.map (·.output) == some ["Root"]
#guard sameResult ((linearizeVerified disconnected "Missing").map (fun order => order.output))
  (.error (.unknownNode "Missing"))

#print axioms resolveParents_sound
#print axioms resolveNode_checked_sound
#print axioms resolveNode_checked_graph_sound
#print axioms linearizeChecked_graph_sound
#print axioms linearizeVerified_projection
#print axioms C4.VerifiedOrder.covers
#print axioms C4.VerifiedOrder.ancestor_suffix
#print axioms C4.VerifiedOrder.indexAncestors
#print axioms AncestryIndex.isAncestor_iff

end LeanPoo.Tests.VerifiedOrder
