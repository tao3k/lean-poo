import LeanPoo.C4.ExecutionInvariant
import LeanPoo.C4.GraphCertificate

namespace LeanPoo.Tests.ExecutionInvariant
open C4 LinearizeState

example (success : computeNode table node true = .ok result) :
    computeNode table node false = .ok result := computeNode_checked_ordinary success
example (success : resolveNode index root name table true fuel = .ok ready) :
    resolveNode index root name table false fuel = .ok ready := resolveNode_checked_ordinary success
example (success : linearizeChecked graph root = .ok output) :
    linearize graph root = .ok output := linearizeChecked_ordinary success
example (success : computeNode table node true = .ok result) :
    result.precedence.Nodup ∧ result.precedence.head? = some node.name ∧
      (selectedTail table result.inheritedSuffix).IsSuffix result.precedence ∧
      ∃ entries, collectParents table (parents node) = .ok entries ∧
        ∀ order ∈ entries.map (·.precedence) ++ MergeState.pending node.parentOrders,
          order.Sublist result.precedence := computeNode_checked_laws success
example (success : certifyNode name orders tails claimed = .ok certificate) :
    certificate.selection.output = claimed := certifyNode_claimed success

private def entries (name : String) : List (Option Linearization) :=
  [none, some ⟨[name], none, none⟩, some ⟨[name], none, some name⟩,
    some ⟨[name, name], some "Missing", some name⟩]
private def add (table : Table) (name : String) (entry : Option Linearization) : Table :=
  match entry with | none => table | some entry => table.insert name entry
private def caches : List Table :=
  (entries "A").flatMap fun first => (entries "B").map fun second =>
    add (add {} "A" first) "B" second
private def nodes : List Node :=
  [[], [[]], [["A"]], [["B"]], [["A", "B"]], [["B", "A"]], [[], ["A"], ["A"], []]].flatMap fun orders =>
    [false, true].map fun marked => { name := "Root", parentOrders := orders, suffix := marked }
#eval do
  let mut examined := 0
  let mut accepted := 0
  IO.println "EXECUTION-INVARIANT-START"
  for table in caches do
    for node in nodes do
      match computeNode table node true with
      | .error _ => pure ()
      | .ok result =>
        unless (computeNode table node false).toOption == some result do
          throw (IO.userError s!"node execution mismatch: {repr node}")
        accepted := accepted + 1
      examined := examined + 1
      if examined % 56 == 0 then IO.println s!"EXECUTION-INVARIANT-PROGRESS nodes={examined}"
  let mut resolved := 0
  for node in nodes do
    let graph : Graph := { nodes := [{ name := "A" }, { name := "B", parentOrders := [["A"]] }, node] }
    for table in caches do
      for fuel in List.range 5 do
        match resolveNode (nodeIndex graph) "Root" "Root" table true fuel with
        | .error _ => pure ()
        | .ok ready =>
          match resolveNode (nodeIndex graph) "Root" "Root" table false fuel with
          | .error error => throw (IO.userError s!"resolver execution mismatch: {repr error}")
          | .ok ordinary =>
            for name in ["A", "B", "Root", "Missing"] do
              unless lookup ordinary name == lookup ready name do
                throw (IO.userError s!"cache mismatch at {name}")
          resolved := resolved + 1
    IO.println s!"EXECUTION-INVARIANT-PROGRESS resolved={resolved}"
    match linearizeChecked graph "Root" with
    | .error _ => pure ()
    | .ok output =>
      unless (linearize graph "Root").toOption == some output do throw (IO.userError "top-level mismatch")
  IO.println s!"EXECUTION-INVARIANT-OK nodes={examined} accepted={accepted} resolved={resolved}"

/- Ordinary acceptance alone does not supply node freshness on an arbitrary
starting cache; checked mode detects this malformed parent result. -/
private def malicious : Table := ({} : Table).insert "A" ⟨["A", "Root"], none, none⟩
private def root : Node := { name := "Root", parentOrders := [["A"]] }
#guard (computeNode malicious root false).toOption.map (·.precedence) == some ["Root", "A", "Root"]
#guard match computeNode malicious root true with
  | .error (.cycle "Root") => true
  | _ => false

/- A valid, acyclic graph also separates ordinary and checked acceptance.
The selected S,A tail intersects P's unmarked ancestry before B. Removing
that tail preserves Root's local P,S constraint but reverses P's A,B one. -/
private def suffixCrossing : Graph := { nodes := [
  { name := "A" }, { name := "B" },
  { name := "P", parentOrders := [["A", "B"]] },
  { name := "S", parentOrders := [["A"]], suffix := true },
  { name := "Root", parentOrders := [["P", "S"]] }] }

#guard (suffixCrossing.validate).toOption.isSome
#guard (linearize suffixCrossing "P").toOption == some ["P", "A", "B"]
#guard (linearize suffixCrossing "Root").toOption == some ["Root", "P", "B", "S", "A"]
#guard match linearizeChecked suffixCrossing "Root" with
  | .error .suffixOrderViolation => true
  | _ => false
#guard match reconstruct suffixCrossing "Root" with
  | .error .suffixOrderViolation => true
  | _ => false

/- Moving A to the end of P's order makes the same inherited tail compatible.
The root output is unchanged, but it now has the strengthened contract. -/
private def compatibleCrossing : Graph := { nodes := suffixCrossing.nodes.map fun node =>
  if node.name == "P" then {node with parentOrders := [["B", "A"]]} else node }
#guard (linearizeChecked compatibleCrossing "Root").toOption ==
  some ["Root", "P", "B", "S", "A"]
#guard (reconstruct compatibleCrossing "Root").toOption.map (·.output) ==
  some ["Root", "P", "B", "S", "A"]

private def noSharedSuffix : Graph := { nodes := suffixCrossing.nodes.map fun node =>
  {node with suffix := false} }
#guard (linearizeChecked noSharedSuffix "Root").toOption ==
  some ["Root", "P", "S", "A", "B"]

/-- The observed ordinary output cannot have an original GraphTrace, for
any selected tail. This proof uses the original declared ancestor order. -/
theorem suffixCrossing_no_trace :
    ¬ ∃ tail, GraphTrace suffixCrossing "Root" ["Root", "P", "B", "S", "A"] tail := by
  rintro ⟨tail, trace⟩
  have path : Ancestor suffixCrossing "P" "Root" := .parent (by rfl) (by simp) .self
  have retained := trace.ancestor_local_order path
    (show suffixCrossing.findNode? "P" = some {name := "P", parentOrders := [["A", "B"]]} by rfl)
    (show ["A", "B"] ∈ ([["A", "B"]] : List (List String)) by simp)
  have impossible : ¬ (["A", "B"] : List String).Sublist ["Root", "P", "B", "S", "A"] := by decide
  exact impossible retained

#print axioms certifyNode_claimed
#print axioms suffixCrossing_no_trace
#print axioms GraphTrace.ancestor_local_order
#eval IO.println "SUFFIX-CROSSING-OK ordinary=accepted checked=rejected trace=impossible"
#print axioms readSuffix_sound
#print axioms computeNode_checked_evidence
#print axioms computeNode_checked_laws
#print axioms computeNode_checked_ordinary
#print axioms resolveNode_checked_ordinary
#print axioms linearizeChecked_ordinary

end LeanPoo.Tests.ExecutionInvariant
