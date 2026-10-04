import LeanPoo.C4.Ranked
import LeanPoo.C4.Linearize
import LeanPoo.Proof.Invalidation

namespace LeanPoo.Tests.C4Ranked

private def diamond : C4.Graph :=
  { nodes :=
      [{ name := "Leaf", parentOrders := [["Left", "Right"]] },
       { name := "Right", parentOrders := [["Seed"]] },
       { name := "Left", parentOrders := [["Seed"]] },
       { name := "Seed", suffix := true },
       { name := "Detached" }] }

#guard match diamond.inferRanked with
  | .error _ => false
  | .ok ranked => ranked.rank "Seed" == 0 && ranked.rank "Right" == 1 &&
      ranked.rank "Left" == 2 && ranked.rank "Leaf" == 3 && ranked.rank "Detached" == 4

#guard Proof.invalidatedNodes diamond ["Seed", "Seed"] == ["Seed", "Right", "Left", "Leaf"]
#guard Proof.invalidatedNodes diamond ["Right"] == ["Right", "Leaf"]
#guard Proof.invalidatedNodes diamond ["Detached"] == ["Detached"]
#guard Proof.invalidatedNodes diamond ["Unknown", "Unknown"] == ["Unknown"]

#guard match Proof.certifyInvalidation diamond ["Seed", "Seed"] with
  | .ok result => result.names == ["Seed", "Right", "Left", "Leaf"]
  | .error _ => false
#guard match Proof.certifyInvalidation diamond [] with
  | .ok result => result.names.isEmpty
  | .error _ => false

-- Independently supplied ranks are checked at every node and edge.
#guard match diamond.checkRank (fun _ => 0) with
  | .error .invalidRank => true | _ => false
#guard match diamond.checkRank (fun _ => 5) with
  | .error .invalidRank => true | _ => false

private def duplicate : C4.Graph := { nodes := [{ name := "A" }, { name := "A" }] }
#guard match duplicate.inferRanked with
  | .error (.graph (.duplicateNode "A")) => true | _ => false

private def missing : C4.Graph := { nodes := [{ name := "A", parentOrders := [["Lost"]] }] }
#guard match missing.inferRanked with
  | .error (.graph (.unknownNode "Lost")) => true | _ => false

private def selfCycle : C4.Graph := { nodes := [{ name := "A", parentOrders := [["A"]] }] }
#guard match selfCycle.inferRanked with
  | .error (.blocked ["A"]) => true | _ => false

private def hiddenCycle : C4.Graph :=
  { nodes := [{ name := "Seed" },
      { name := "A", parentOrders := [["B"]] },
      { name := "B", parentOrders := [["A"]] }] }
#guard match C4.linearize hiddenCycle "Seed" with
  | .ok ["Seed"] => true | _ => false
#guard match hiddenCycle.inferRanked with
  | .error (.blocked ["A", "B"]) => true | _ => false

-- A rank certifies parent-edge acyclicity, independently of method-order
-- consistency or suffix compatibility. Both C4 failures remain failures.
private def inconsistent : C4.Graph :=
  { nodes := [{ name := "A" }, { name := "B" },
      { name := "X", parentOrders := [["A", "B"]] },
      { name := "Y", parentOrders := [["B", "A"]] },
      { name := "Z", parentOrders := [["X", "Y"]] }] }
#guard match inconsistent.inferRanked with | .ok _ => true | .error _ => false
#guard match C4.linearize inconsistent "Z" with
  | .error .inconsistentOrder => true | _ => false

private def incompatibleSuffixes : C4.Graph :=
  { nodes := [{ name := "A", suffix := true }, { name := "B", suffix := true },
      { name := "Z", parentOrders := [["A", "B"]] }] }
#guard match incompatibleSuffixes.inferRanked with | .ok _ => true | .error _ => false
#guard match C4.linearize incompatibleSuffixes "Z" with
  | .error .incompatibleSuffixes => true | _ => false

private def empty : C4.Graph := { nodes := [] }
#guard match empty.inferRanked with | .ok _ => true | .error _ => false
#guard Proof.invalidatedNodes empty ["Outside"] == ["Outside"]

-- A reversed declaration order does not truncate propagation down a chain.
private def chain : C4.Graph :=
  { nodes := (List.range 32).reverse.map fun n =>
      { name := toString n, parentOrders := if n == 0 then [] else [[toString (n - 1)]] } }
#guard match chain.inferRanked with
  | .ok ranked => ranked.rank "0" == 0 && ranked.rank "31" == 31
  | .error _ => false
#guard (Proof.invalidatedNodes chain ["0"]).length == 32
#guard (Proof.invalidatedNodes chain ["0"]).contains "31"

example (graph : C4.Graph) (ranked : C4.Ranked graph) (changed : List String) (name : String) :
    name ∈ Proof.invalidatedNodes graph changed ↔
      ∃ origin ∈ changed, ∃ steps, Proof.Descendant graph origin steps name :=
  Proof.mem_invalidated_iff_descendant ranked changed name

example (graph : C4.Graph) (ranked : C4.Ranked graph) (name : String) (steps : Nat) :
    ¬ Proof.Descendant graph name (steps + 1) name :=
  Proof.Descendant.no_positive_cycle ranked name steps

example (graph : C4.Graph) (ranked : C4.Ranked graph) (changed : List String) (name : String) :
    name ∈ Proof.impactStep graph (Proof.invalidatedNodes graph changed) ↔
      name ∈ Proof.invalidatedNodes graph changed :=
  Proof.mem_impactStep_invalidated_iff ranked changed name

#print axioms Proof.mem_invalidated_iff_descendant
#print axioms Proof.mem_impactStep_invalidated_iff
#print axioms Proof.certifyInvalidation

end LeanPoo.Tests.C4Ranked
