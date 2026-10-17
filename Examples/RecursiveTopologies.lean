import Examples.Support.RecursiveTopology

/-! Executable multi-round SCC reclosure controls over shared example fixtures. -/
namespace LeanPoo.Examples.RecursiveTopologies
open Functional

/-- Simultaneous merges/splits, failed crossed merge/retry, restored topology,
computed-only selection and one-pair body revision match the Scheme fixture. -/
def test : Except String Unit := do
  let s0 ← initial
  unless (s0.graph.payload 11).total == 82 && members s0.source 0 == some [0,1] do throw "initial SCC"
  let firstProvider ← (s0.graph.payload 8).call 1
  let firstService ← (s0.graph.payload 0).call 1
  unless firstProvider == 4 && firstService == 6 do throw "initial callable mapping"
  let s1 ← step s0 ⟨1,false⟩
  let nextProvider ← (s1.graph.payload 9).call 1
  let nextService ← (s1.graph.payload 0).call 1
  unless nextProvider == 9 && nextService == 11 do throw "migrated callable mapping"
  unless (s1.graph.payload 11).total == 108 && members s1.source 0 == some [0,1,2,3] &&
    members s1.source 4 == some [4,5,6,7] do throw "two merges"
  let s2 ← step s1 ⟨2,false⟩
  unless (s2.graph.payload 11).total == 128 && members s2.source 0 == some [0,2] &&
    members s2.source 1 == some [1,3] && members s2.source 4 == some [4,6] &&
    members s2.source 5 == some [5,7] do throw "two splits"
  match step s2 ⟨3,true⟩ with
  | .error "joint refusal" => pure () | _ => throw "failure published"
  let s3 ← step s2 ⟨3,false⟩
  unless (s3.graph.payload 11).total == 132 && members s3.source 0 == some [0,2,4,6] &&
    members s3.source 1 == some [1,3,5,7] do throw "crossed retry"
  let s4 ← step s3 ⟨4,false⟩
  unless (s4.graph.payload 11).total == 127 && members s4.source 0 == members s0.source 0 do throw "restored groups"
  unless !(RecursiveMigration.recognizes (names s4.source) s4.epochs 0 (s0.graph.canonical 0)) do throw "old group revived"
  let s5 ← step s4 ⟨5,false⟩
  unless s5.evaluated == [10,11,13] && (s5.graph.payload 11).total == 134 do throw "computed replay"
  let s6 ← step s5 ⟨6,false⟩
  let revisedService ← (s6.graph.payload 0).call 1
  let retainedService ← (s6.graph.payload 7).call 1
  unless revisedService == 12 && retainedService == 18 do throw "retained callable mapping"
  unless s6.evaluated == [0,1,11,13] && (s6.graph.payload 13).total == 135 do throw "independent SCC rebuilt"
  unless s6.graph.canonical 7 == s4.graph.canonical 7 && s6.graph.canonical 12 == s0.graph.canonical 12 do throw "clean reference"
  unless !(RecursiveMigration.recognizes (names s6.source) s6.epochs 8 (s0.graph.canonical 8)) do throw "removed provider"
  unless (ObjectContract.diagnose (schema 135) s6 []).isEmpty do throw "refine"
  let root := s6.graph.canonical 11
  let bound := Call.bindEvidence root 7 6 (fun value => value)
  let produce (subject : Node × Nat) (context : Nat) (_ : Node × Nat) :
      Except String (((Node × Nat) × Nat × Nat) × Nat) := .ok ((subject,7,context),7)
  match bound.publish 6 (produce (s2.graph.canonical 11) 6) root with
  | (.error .logic,6) => pure () | _ => throw "old subject"
  match bound.publish 6 (produce root 5) root with
  | (.error .logic,6) => pure () | _ => throw "old context"
  match bound.publish 6 (produce root 6) root with
  | (.ok _,7) => pure () | _ => throw "evidence retry"

#print axioms RecursiveTopology.removed_edge_dirty
#print axioms RecursiveTopology.old_path_dirty
#print axioms RecursiveTopology.old_scc_atomic
#print axioms RecursiveTopology.new_scc_atomic
#print axioms RecursiveTopology.clean_members
#print axioms RecursiveTopology.membership_changed_dirty
#print axioms RecursiveMigration.invalidate_least
#print axioms RecursiveMigration.bound_root
#eval match test with
  | .ok () => IO.println "RECURSIVE-TOPOLOGIES-OK"
  | .error cause => throw (IO.userError cause)
end LeanPoo.Examples.RecursiveTopologies
