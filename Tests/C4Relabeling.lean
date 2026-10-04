import LeanPoo.Functional.Relabeling

namespace LeanPoo.Tests.C4Relabeling
open C4 Functional
variable {graph other : Graph}
deriving instance DecidableEq for Node

private def prefixed (name : String) := "模块::" ++ name
private theorem prefixed_injective : Function.Injective prefixed := by
  intro a b same
  exact (String.append_right_inj "模块::").mp same
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

universe u v w x
example {Context : Type u} {Key : Type v} {Value : Context → Key → Type w}
    {Result : Type x} (order : VerifiedOrder graph root) (change : graph.Relabeling other)
    (unique : (graph.nodes.map Node.name).Nodup)
    (providers mapped : String → Provider Context Key Value) (keys : List Key)
    (aligned : ∀ name, Ancestor graph name root → ∀ key ∈ keys,
      mapped (change.rename name) key = providers name key)
    (consume : Requirements.Factories Context Value keys → Result)
    (Claim : Except Key Result → Prop)
    (known : Claim ((Requirements.prepare (assemble order providers) keys).map consume)) :
    Claim ((Requirements.prepare (assemble (order.relabel change unique) mapped) keys).map consume) := by
  rw [Requirements.prepare_relabel order change unique providers mapped keys aligned]
  exact known

private def providers : String → Provider Nat Bool (fun context _ => {n : Nat // context ≤ n}) :=
  fun name key =>
    if name == "Root" then none
    else if name == "P" && key then none
    else if name == "A" || name == "B" || name == "P" then
      some (fun context => ⟨context + (if name == "A" then 1 else if name == "B" then 2 else 3), by omega⟩)
    else none
private def mapped (rename : String → String) :
    String → Provider Nat Bool (fun context _ => {n : Nat // context ≤ n}) :=
  fun name => if name == rename "A" then providers "A"
    else if name == rename "B" then providers "B"
    else if name == rename "P" then providers "P" else fun _ => none
private def signature (order : VerifiedOrder graph root)
    (dictionary : String → Provider Nat Bool (fun context _ => {n : Nat // context ≤ n})) : List (Option Nat) :=
  [0, 7].flatMap fun context => [false, true].map fun key =>
    (Functional.apply (assemble order dictionary) context key).map Subtype.val

#eval do
  IO.println "C4-RELABELING-START"
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
                    let middle := reordered.rename swap
                    let first : graph.Relabeling middle := ⟨swap, swap_injective, same.map (Node.rename swap)⟩
                    let target : Graph := {nodes := (middle.rename prefixed).nodes.reverse}
                    let second : middle.Relabeling target :=
                      ⟨prefixed, prefixed_injective, (List.reverse_perm _).symm⟩
                    let combined := first.trans second
                    let freshMiddle := linearizeVerified middle (swap "Root")
                    let fresh := linearizeVerified target (combined.rename "Root")
                    unless (freshMiddle.map VerifiedOrder.output).toOption ==
                        ((original.map VerifiedOrder.output).toOption.map (List.map swap)) do
                      throw (IO.userError "first fresh migration output changed")
                    unless (fresh.map VerifiedOrder.output).toOption ==
                        ((original.map VerifiedOrder.output).toOption.map (List.map combined.rename)) do
                      throw (IO.userError "combined fresh migration output changed")
                    if let .ok order := original then
                      let direct := order.relabel combined unique
                      let sequential := (order.relabel first unique).relabel second (first.unique unique)
                      let .ok rebuilt := fresh | throw (IO.userError "target graph rejected")
                      unless direct.output == rebuilt.output && direct.output == sequential.output do
                        throw (IO.userError "direct/sequential migration changed output")
                      unless signature direct (mapped combined.rename) == signature order providers do
                        throw (IO.userError "aligned dependent factory values changed")
                      for left in ["Root", "P", "A", "B", "Missing"] do
                        for right in ["Root", "P", "A", "B", "Missing"] do
                          unless direct.precedes (combined.rename left) (combined.rename right) == order.precedes left right do
                            throw (IO.userError "mapped precedence query changed")
                          pairs := pairs + 1
                      accepted := accepted + 1
                    runs := runs + 1
                  else throw (IO.userError "enumerated declaration list is not a permutation")
        families := families + 1
        if families % 8 == 0 then IO.println s!"C4-RELABELING-PROGRESS families={families} runs={runs}"
  unless families == 64 && runs == 1536 && accepted > 0 && accepted < runs && pairs == accepted * 25 do
    throw (IO.userError "unexpected corpus coverage")
  IO.println s!"C4-RELABELING-OK families={families} cases={runs} target-compilations={runs * 2} accepted={accepted} pairs={pairs}"


-- A renamed graph does not update a dictionary automatically. Here the target
-- name lacks the old entry, so provider alignment is a real premise.
#guard (select ["A"] providers false).isSome
#guard (select [prefixed "A"] providers false).isNone
#guard (select [prefixed "A"] (mapped prefixed) false).isSome

#print axioms Graph.Relabeling.trans
#print axioms Graph.Relabeling.unique
#print axioms VerifiedOrder.relabel
#print axioms VerifiedOrder.relabel_unique
#print axioms VerifiedOrder.relabel_trans_output
#print axioms VerifiedOrder.relabel_precedes
#print axioms assemble_relabel
#print axioms Requirements.prepare_relabel
#eval IO.println "C4-RELABELING-BOUNDARY-OK unaligned=missing aligned=present"
end LeanPoo.Tests.C4Relabeling
