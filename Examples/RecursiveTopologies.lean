import LeanPoo.Functional.RecursiveTopology
import LeanPoo.Functional.FunctionValidation

/-! Seven matching multi-SCC rounds. A common finite name universe reserves both
provider positions for old/new path comparison; inactive providers are hidden by
membership recognition. Actual support/index lowering uses RecursiveMigration's
proved boundary. This fixture is not a host allocation/performance model. -/
namespace LeanPoo.Examples.RecursiveTopologies
open Functional
abbrev Node := Fin 14

/-- Eight services, two providers, computed summary/report, idle and meter. -/
structure Source where
  stage : Nat
  refuse : Bool := false

/-- Four pairs, two quartets, crossed pairs, crossed quartets, then original pairs. -/
def peer (stage : Nat) (node : Fin 8) : Fin 8 :=
  (if stage = 1 then (#v[1,2,3,0,5,6,7,4] : Vector (Fin 8) 8)
   else if stage = 2 then #v[2,3,0,1,6,7,4,5]
   else if stage = 3 then #v[2,3,4,5,6,7,0,1]
   else #v[1,0,3,2,5,4,7,6]).get node

/-- Stable service names embed into the common graph independently of support rows. -/
def embed (node : Fin 8) : Node := ⟨node.val,by omega⟩

/-- Provider migration first moves one quartet and then all services. -/
def secondary (source : Source) (node : Fin 8) : Bool :=
  decide (source.stage ≥ 2 ∨ source.stage = 1 ∧ node.val < 4)

/-- Current computed-reader selection changes independently of service peer edges. -/
def selected (source : Source) : Fin 8 :=
  if source.stage = 1 then 6 else if source.stage = 2 then 1 else if source.stage = 3 then 5
  else if source.stage ≥ 5 then 7 else 0

/-- A later local body edit changes one member of one restored pair. -/
def weight (source : Source) (node : Fin 8) : Int :=
  if node = 0 ∧ source.stage = 6 then 3 else node.val+2

/-- Inactive reserved providers are not supported references. -/
def active (source : Source) (node : Node) : Bool :=
  if node = 8 then decide (source.stage < 2) else if node = 9 then decide (source.stage > 0) else true

/-- Actual published membership is distinct from the common comparison universe. -/
def names (source : Source) : List Node := (List.finRange 14).filter (active source)

/-- Complete declared links include checked provider captures and computed readers. -/
def edges (source : Source) (node : Node) : List Node :=
  if service : node.val < 8 then
    let index : Fin 8 := ⟨node.val,service⟩
    [embed (peer source.stage index),if secondary source index then 9 else 8]
  else if node = 10 then [embed (selected source)]
  else if node = 11 then (List.finRange 8).map embed ++ [10]
  else if node = 13 then [11] else []

/-- Explicit body/support seeds supplement changed declared footprints. -/
def body (old next : Source) (node : Node) : Bool :=
  decide (active old node ≠ active next node) ||
  (decide (node = 0) && decide (weight old 0 ≠ weight next 0)) ||
  (decide (node = 10) && decide (old.refuse ≠ next.refuse))

/-- Current checked Function result for one service request. -/
def serviceValue (source : Source) (node : Fin 8) : Int :=
  1 + (if secondary source node then 8 else 3) + weight source node

/-- Joint report uses all checked service branches plus the selected computed branch. -/
def reportTotal (source : Source) : Int :=
  ((List.finRange 8).map (serviceValue source)).foldl (·+·) 0 + serviceValue source (selected source)

/-- Actual callable and computed data remain opaque cached values. -/
structure Payload where
  call : Int → Except String Int
  total : Int

/-- Source construction uses the existing checked Function normalization combinator. -/
def payload (source : Source) (node : Node) : Payload :=
  let total := if service : node.val < 8 then serviceValue source ⟨node.val,service⟩
    else if node = 8 then (if active source node then 3 else 0)
    else if node = 9 then (if active source node then 8 else 0)
    else if node = 10 then serviceValue source (selected source)
    else if node = 12 then 99 else reportTotal source
  -- Providers store their increment; services store the result of input 1.
  let offset := if node = 8 ∨ node = 9 then total else total-1
  ⟨FunctionValidation.wrap Except.ok Except.ok (fun value => .ok (value+offset)),total⟩

abbrev Graph := RecursiveValidation.Graph 14 (Node × Nat) Payload

/-- Every current final obligation runs after all selected actual normalizers. -/
def admit (source : Source) (candidate : Graph) (node : Node) : Except String Unit :=
  if source.refuse && node == 10 then .error "joint refusal"
  else if (candidate.payload node).total = (payload source node).total ∧
      candidate.links node = (edges source node).map candidate.canonical then .ok () else .error "current admission"

/-- Complete published model state; logical epochs are not Scheme serialized data. -/
structure Snapshot where
  source : Source
  epochs : Node → Nat
  graph : Graph
  evaluated : List Node

/-- Start from all-or-error finite graph closure; inactive vertices are placeholders. -/
def initial : Except String Snapshot := do
  let source : Source := ⟨0,false⟩
  let graph ← RecursiveValidation.close (fun node => (node,0)) (edges source) (fun _ => .ok ())
    (fun node => .ok (payload source node)) (admit source)
  return ⟨source,fun _ => 0,graph,names source⟩

/-- Actual footprint/body seeds alone compute least invalidation. Normalization and
shape callbacks deliberately fail on clean nodes to expose unintended replay. -/
def step (old : Snapshot) (next : Source) : Except String Snapshot := do
  let dirty := RecursiveTopology.dirty (edges old.source) (edges next) (body old.source next)
  let epochs := RecursiveMigration.advanceKey (names old.source) (names next) dirty old.epochs
  let graph ← RecursiveValidation.close (fun node => (node,epochs node)) (edges next)
    (RecursiveRevision.select dirty (fun _ => ()) (fun node => if dirty node then .ok () else .error "clean shape"))
    (RecursiveRevision.select dirty old.graph.payload (fun node => if dirty node then .ok (payload next node) else .error "clean normalizer"))
    (admit next)
  return ⟨next,epochs,graph,(names next).filter dirty⟩

/-- Optional exact SCC discovery is for inspection, not the construction path. -/
def members (source : Source) (root : Node) : Option (List Nat) :=
  (StrongComponents.discover (RecursiveTopology.edge (edges source))).map
    (fun checked => (checked.members root).map Fin.val)

/-- Current whole-value refinement checks computed identity as well as arithmetic. -/
def schema (expected : Int) : ObjectContract.Contract Snapshot String Unit String :=
  ObjectContract.refine
    {view := ⟨fun _ => true,fun _ => true,fun _ => [],fun _ _ => none⟩
     fields := [],strict := true,constraints := [],validInventory := Or.inl rfl,obligations := fun _ _ => []}
    (fun value path => if (value.graph.payload 11).total == expected &&
      value.graph.links 10 == [value.graph.canonical (embed (selected value.source))]
      then [] else [.rejected path "computed identity"])

/-- Existing independent invocation policy composes with exact evidence binding. -/
def Call : DeclarativeMetadata.Contract Unit (Node × Nat) ((Node × Nat) × Nat × Nat) where
  input := ⟨"reference",fun _ => True,fun _ => isTrue True.intro⟩
  output := ⟨"evidence",fun _ => True,fun _ => isTrue True.intro⟩
  meaning := fun _ _ _ => True
  decide := fun _ _ _ => isTrue True.intro
  rule := .atom ()

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
