import LeanPoo.C4.OrderRelation
import LeanPoo.C4.AuditedResolver

namespace LeanPoo.Tests.OrderRelation
open C4

example (order : VerifiedOrder graph root)
    (ancestorOrder : VerifiedOrder graph ancestor) (path : Ancestor graph ancestor root)
    (before : ancestorOrder.precedes left right = true) : order.precedes left right = true :=
  order.monotone_precedes ancestorOrder path before

-- Independent positional oracle: missing names must not inherit idxOf's sentinel.
private def positional (items : List String) (left right : String) : Bool :=
  items.contains left && items.contains right && items.idxOf left < items.idxOf right

#eval do
  IO.println "ORDER-RELATION-START"
  let mut families := 0
  let mut accepted := 0
  let mut comparisons := 0
  let mut inherited := 0
  for p in [[["A"]], [["A", "B"]], [["B", "A"]], [[], ["A"], ["A"], []]] do
    for s in [[["A"]], [["B"]], [["A", "B"]], [["B", "A"]]] do
      for flags in List.range 4 do
        for localOrders in [[["P", "S"]], [["S", "P"]], [["P"], ["S"]], [[], ["P", "S"], ["P"], []]] do
          let graph : Graph := { nodes := [
            {name := "A"}, {name := "B"},
            {name := "P", parentOrders := p, suffix := flags % 2 == 1},
            {name := "S", parentOrders := s, suffix := flags / 2 == 1},
            {name := "Root", parentOrders := localOrders}] }
          if let .ok order := linearizeAuditedVerified graph "Root" then
            accepted := accepted + 1
            for left in ["Root", "P", "S", "A", "B", "Missing"] do
              for right in ["Root", "P", "S", "A", "B", "Missing"] do
                unless order.precedes left right == positional order.output left right do
                  throw (IO.userError "pair query disagrees with positional oracle")
                comparisons := comparisons + 1
            for name in order.output do
              let .ok parent := linearizeAuditedVerified graph name
                | throw (IO.userError "reachable ancestor failed verified compilation")
              for left in parent.output do
                for right in parent.output do
                  if parent.precedes left right then
                    unless order.precedes left right do
                      throw (IO.userError "ancestor precedence reversed in root")
                    inherited := inherited + 1
              for base in parent.output do
                if name != base then
                  unless order.precedes name base do
                    throw (IO.userError "inheritance precedence reversed in root")
              let some declaration := graph.findNode? name
                | throw (IO.userError "reachable declaration missing")
              for row in declaration.parentOrders do
                for left in row do
                  for right in row do
                    if positional row left right then
                      unless order.precedes left right do
                        throw (IO.userError "reachable local precedence reversed")
          families := families + 1
          if families % 64 == 0 then IO.println s!"ORDER-RELATION-PROGRESS families={families}"
  unless accepted == 116 && comparisons == 4176 do
    throw (IO.userError "unexpected accepted/query corpus size")
  IO.println s!"ORDER-RELATION-OK families={families} accepted={accepted} comparisons={comparisons} inherited={inherited}"

#print axioms Precedes.included
#print axioms GraphTrace.inheritance_precedes
#print axioms VerifiedOrder.precedes_iff
#print axioms VerifiedOrder.precedes_irrefl
#print axioms VerifiedOrder.precedes_members
#print axioms VerifiedOrder.local_precedes
#print axioms VerifiedOrder.monotone_precedes
#print axioms VerifiedOrder.inheritance_precedes
end LeanPoo.Tests.OrderRelation
