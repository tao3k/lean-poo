import LeanPoo.Functional.Presentation
import LeanPoo.C4.AuditedResolver
import LeanPoo.C4.OrderRelation

namespace LeanPoo.Tests.C4Presentation
open C4 Functional
variable {graph other : Graph}

-- This instance is only for checking that the enumerated test lists really
-- are permutations. The public retained-order operation takes erased evidence.
deriving instance DecidableEq for Node

universe u v w x
example {Context : Type u} {Key : Type v} {Value : Context → Key → Type w}
    {Result : Type x} (order : VerifiedOrder graph root)
    (same : graph.nodes.Perm other.nodes) (unique : (graph.nodes.map Node.name).Nodup)
    (providers : String → Provider Context Key Value) (keys : List Key)
    (consume : Requirements.Factories Context Value keys → Result) :
    (Requirements.prepare (assemble (order.permute same unique) providers) keys).map consume =
      (Requirements.prepare (assemble order providers) keys).map consume :=
  congrArg (fun result => result.map consume)
    (Requirements.prepare_permute order same unique providers keys)

example {Context : Type u} {Key : Type v} {Value : Context → Key → Type w}
    {Result : Type x} (order : VerifiedOrder graph root)
    (same : graph.nodes.Perm other.nodes) (unique : (graph.nodes.map Node.name).Nodup)
    (providers : String → Provider Context Key Value) (keys : List Key)
    (consume : Requirements.Factories Context Value keys → Result)
    (Claim : Except Key Result → Prop)
    (known : Claim ((Requirements.prepare (assemble order providers) keys).map consume)) :
    Claim ((Requirements.prepare (assemble (order.permute same unique) providers) keys).map consume) := by
  rw [Requirements.prepare_permute]
  exact known

private def providers : String → Provider Nat Bool (fun context _ => {n : Nat // context ≤ n}) :=
  fun name key =>
    if name == "Root" then none
    else if name == "P" && key then none
    else some (fun context => ⟨context + (if name == "A" then 1 else if name == "B" then 2 else 3), by omega⟩)

private def signature (order : VerifiedOrder graph "Root") : List (Option Nat) :=
  [0, 7].flatMap fun context => [false, true].map fun key =>
    (Functional.apply (assemble order providers) context key).map Subtype.val

#eval do
  IO.println "C4-PRESENTATION-START"
  let mut families := 0
  let mut runs := 0
  let mut accepted := 0
  let mut pairs := 0
  for parents in [[["A"]], [["B"]], [["A", "B"]], [[], ["A"], ["A"], []]] do
    for localOrders in [[["P", "B"]], [["B", "P"]], [["P"], ["B"]], [[], ["P", "B"], []]] do
      for flags in List.range 4 do
        let graph : Graph := {nodes := [
          {name := "A"}, {name := "B", suffix := flags % 2 == 1},
          {name := "P", parentOrders := parents, suffix := flags / 2 == 1},
          {name := "Root", parentOrders := localOrders}]}
        have unique : (graph.nodes.map Node.name).Nodup := by
          change ["A", "B", "P", "Root"].Nodup
          decide
        let original := linearizeVerified graph "Root"
        for a in List.range 4 do
          for b in List.range 4 do
            for c in List.range 4 do
              for d in List.range 4 do
                if a != b && a != c && a != d && b != c && b != d && c != d then
                  let reordered : Graph := {nodes := [graph.nodes[a]!, graph.nodes[b]!, graph.nodes[c]!, graph.nodes[d]!]}
                  if same : graph.nodes.Perm reordered.nodes then
                    let fresh := linearizeVerified reordered "Root"
                    unless (fresh.map VerifiedOrder.output).toOption == (original.map VerifiedOrder.output).toOption do
                      throw (IO.userError "independent checked output changed")
                    unless (linearizeAudited reordered "Root").toOption ==
                        (linearizeAudited graph "Root").toOption do
                      throw (IO.userError "audited acceptance/output changed")
                    if let .ok order := original then
                      let retained := order.permute same unique
                      let .ok rebuilt := fresh | throw (IO.userError "reordered graph rejected")
                      unless retained.output == rebuilt.output && signature retained == signature order do
                        throw (IO.userError "retained selection or dependent values changed")
                      for left in ["Root", "P", "A", "B", "Missing"] do
                        for right in ["Root", "P", "A", "B", "Missing"] do
                          unless retained.precedes left right == order.precedes left right do
                            throw (IO.userError "retained precedence query changed")
                          pairs := pairs + 1
                      accepted := accepted + 1
                    runs := runs + 1
                  else throw (IO.userError "enumerated declaration list is not a permutation")
        families := families + 1
        if families % 8 == 0 then IO.println s!"C4-PRESENTATION-PROGRESS families={families} runs={runs}"
  unless families == 64 && runs == 1536 && accepted > 0 && accepted < runs && pairs == accepted * 25 do
    throw (IO.userError "unexpected corpus coverage")
  IO.println s!"C4-PRESENTATION-OK families={families} permutations={runs} accepted={accepted} pairs={pairs}"

-- Unique names do not make first validation diagnostics independent of list
-- order. Both are rejected, while the reported missing reference changes.
private def errorOf (result : Except Error α) : Option Error :=
  match result with | .error error => some error | .ok _ => none
private def missing : Graph := {nodes := [
  {name := "Root", parentOrders := [["A", "B"]]},
  {name := "A", parentOrders := [["MissingA"]]},
  {name := "B", parentOrders := [["MissingB"]]}]}
#guard errorOf (linearizeChecked missing "Root") == some (.unknownNode "MissingA")
#guard errorOf (linearizeChecked {nodes := missing.nodes.reverse} "Root") == some (.unknownNode "MissingB")

-- Without unique names, permutation can change first-declaration lookup.
private def duplicated : Graph := {nodes := [{name := "Root"}, {name := "Root", suffix := true}]}
#guard (duplicated.findNode? "Root").map Node.suffix == some false
#guard (({nodes := duplicated.nodes.reverse} : Graph).findNode? "Root").map Node.suffix == some true

#print axioms Graph.sameLookup_of_perm
#print axioms GraphTrace.represent
#print axioms VerifiedOrder.permute
#print axioms VerifiedOrder.permute_unique
#print axioms linearizeChecked_permute_ok
#print axioms assemble_permute
#print axioms Requirements.prepare_permute
#eval IO.println "C4-PRESENTATION-BOUNDARIES-OK diagnostic-order=2 duplicate-lookup=2"
end LeanPoo.Tests.C4Presentation
