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

end LeanPoo.Examples.RecursiveTopologies
