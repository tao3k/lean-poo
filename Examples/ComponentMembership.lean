import LeanPoo.Functional.SupportRevision
import LeanPoo.Functional.SupportedComponents
import LeanPoo.Prototype.ComponentClosure

/-! Component insertion/removal in a fixed declared lens universe. Active support
changes before whole SCC closure and current cross-service admission. -/
namespace LeanPoo.Examples.ComponentMembership
open Functional.StrongComponents Prototype Prototype.Generalized
/-- Native positions: quota/spare/shared, A–F, monitor, settlement, stable. -/
abbrev Key := Fin 12
/-- Comparable wider carrier; inactive positions do not have observable components. -/
abbrev Raw := Vector Nat 12
/-- Two bridge positions become actual components only after insertion. -/
def support (expanded : Bool) : List Key :=
  if expanded then List.finRange 12 else [0,1,2,3,4,5,6,9,10,11]
/-- Declared footprints are validated before masking inactive lens positions. -/
def reads (expanded : Bool) (key : Key) : List Key :=
  match key.val with
  | 2 => if expanded then [1,4] else [0,4]
  | 3 => [2,4]
  | 4 => if expanded then [3,8] else [3]
  | 5 => if expanded then [2,6,7] else [0,6]
  | 6 => [5]
  | 7 => if expanded then [2,5,8] else []
  | 8 => if expanded then [7] else []
  | 9 => [2]
  | 10 => if expanded then [3,4,5,6,7,8] else [3,4,5,6]
  | 11 => [11]
  | _ => []
/-- Active graph semantics use the same consumer-to-provider direction as Scheme. -/
def edge (expanded : Bool) (key dep : Key) : Bool := decide (dep ∈ reads expanded key)
/-- Existing functional vector lenses preserve every unrelated storage position. -/
def focus (key : Key) : MonoLens Raw Nat :=
  MonoLens.ofGetSet (fun raw => raw.get key) (fun value raw => raw.set key.val value key.isLt)
/-- Universal storage laws remain independent of operational sample checks. -/
theorem focus_laws (key : Key) :
    LensLaws (fun raw : Raw => raw.get key) (fun value raw => raw.set key.val value key.isLt) := by
  constructor
  · intro raw; simp [Vector.get]
  · intro raw value
    change (raw.set key.val value key.isLt)[key.val] = value
    exact Vector.getElem_set_self key.isLt
  · intro raw first second; simp
/-- Same complete component equations as the native bridge insertion scenario. -/
def equation (quota spare : Nat) (expanded : Bool) (key : Key) (read : Key → Nat) : Nat :=
  match key.val with
  | 0 => quota
  | 1 => spare
  | 2 => min (read (if expanded then 1 else 0)) (1 + read 4)
  | 3 => min (read 2) (1 + read 4)
  | 4 => if expanded then min (read 3) (read 8) else read 3
  | 5 => if expanded then min (read 2) (1 + max (read 6) (read 7)) else min (read 0) (1 + read 6)
  | 6 => read 5
  | 7 => min (read 2) (1 + max (read 5) (read 8))
  | 8 => read 7
  | 9 => read 2
  | 10 => read 3 + read 4 + read 5 + read 6 + (if expanded then read 7 + read 8 else 0)
  | _ => min 2 (1 + read 11)
/-- Reuse the existing generic lens family and actual whole-equation closure. -/
def parts (quota spare : Nat) (expanded : Bool) (external : Raw) :=
  componentParts focus (equation quota spare expanded) (fun key (raw : Raw) => raw.get key) external.get
/-- Supported groups are discovered, then visited in a valid dependency-first
fixture order. Production Scheme uses the existing checked condensation scheduler. -/
def build (quota spare : Nat) (expanded : Bool) (graph : Supported (edge expanded)) : Except String Raw := do
  let mut state := Vector.replicate 12 0
  let mut done : List Key := []
  for key in graph.keys do
    if key ∉ done then
      let members := graph.members key
      let group ← Functional.FeedbackCache.closeGroup (parts quota spare expanded state) id
        (Vector.replicate 12 0) members (Vector.replicate 12 0) 32
      state := members.foldl (fun raw node => raw.set node.val (group.result.closed.raw.get node) node.isLt) state
      done := done ++ members
  return state
/-- Joint admission includes current support, every endpoint and the unchanged monitor. -/
def approved (expanded allowed : Bool) (limit : Nat) (raw : Raw) : Bool :=
  let endpoints : List Key := [3,4,5,6] ++ if expanded then [7,8] else []
  allowed && (9 :: endpoints).all (fun key => decide (raw.get key = raw.get 2)) &&
    decide (raw.get 10 = endpoints.length * raw.get 2 ∧ raw.get 10 ≤ limit)
/-- Actual graph values are typed independently from raw carrier positions. -/
abbrev Values := fun _ : Key => Nat
/-- All declarations in this source are base providers, used to exercise membership
batch semantics independently of the cyclic equation fixtures above. -/
def baseSource : Functional.GeneralizedGraph.Declaration Key Values :=
  ⟨support false, fun _ => none, fun key => if key.val = 7 then some (.ok 99) else some (.ok 3)⟩
/-- Executable controls cover dynamic support, exact groups, dirty readers,
whole closure/residuals, provider erasure, fresh defaults and current approval. -/
def check : Except String Unit := do
  let some old := discoverSupported (support false) (edge false) | throw "compact discovery refused"
  let some next := discoverSupported (support true) (edge true) | throw "expanded discovery refused"
  unless (old.members 2).map Fin.val == [2,3,4] && (old.members 5).map Fin.val == [5,6] &&
      old.members 7 == [] && (next.members 2).map Fin.val == [2,3,4,5,6,7,8] do
    throw "active membership mismatch"
  unless (List.finRange 12).map (next.dirty (supportRevisionSeed old next (fun _ => false))) ==
      [false,false,true,true,true,true,true,true,true,true,true,false] do throw "insertion invalidation mismatch"
  unless (List.finRange 12).map (old.dirty (supportRevisionSeed next old (fun _ => false))) ==
      [false,false,true,true,true,true,true,false,false,true,true,false] do throw "deletion invalidation mismatch"
  unless (discoverSupported ((support true).filter (fun key => key.val != 8)) (edge true)).isNone do
    throw "dangling removal accepted"
  let some empty := discoverSupported ([] : List Key) (fun _ _ => false) | throw "empty support refused"
  let some singleton := discoverSupported ([0] : List Key) (fun _ _ => false) | throw "isolated support refused"
  unless empty.graph.members 0 == singleton.graph.members 0 &&
      singleton.dirty (supportRevisionSeed empty singleton (fun _ => false)) 0 do
    throw "isolated insertion was confused with an inactive universe singleton"
  let initial ← build 3 4 false old
  let expanded ← build 3 4 true next
  let revised ← build 3 5 true next
  let removed ← build 2 4 false old
  unless initial.toList == [3,4,3,3,3,3,3,0,0,3,12,2] && expanded.toList == [3,4,4,4,4,4,4,4,4,4,24,2] &&
      revised.toList == [3,5,5,5,5,5,5,5,5,5,30,2] && removed.toList == [2,4,2,2,2,2,2,0,0,2,8,2] do
    throw "actual component closure mismatch"
  unless approved true true 30 revised && !approved true true 12 revised && !approved false false 8 removed do
    throw "current admission mismatch"
  let .ok added := Functional.GeneralizedGraph.SupportRevision.create baseSource (support true) [] [] |
    throw "source support admission refused"
  unless (added.apply.base 7).isNone do throw "latent unsupported base resurrected"
  let .ok erased := Functional.GeneralizedGraph.SupportRevision.create added.apply (support false) [] [] |
    throw "deletion admission refused"
  unless (erased.apply.base 7).isNone && (erased.apply.code 7).isNone do throw "removed provider retained"
  let .ok restored := Functional.GeneralizedGraph.SupportRevision.create erased.apply (support true) [] [⟨7,some (.ok 4)⟩] |
    throw "fresh definition admission refused"
  match restored.apply.base 7 with
  | some (.ok 4) => pure ()
  | _ => throw "fresh explicit input missing"
#eval match check with
  | .ok () => IO.println "COMPONENT-MEMBERSHIP-OK"
  | .error message => throw (IO.userError message)
#print axioms Functional.GeneralizedGraph.SupportRevision.erased
#print axioms Functional.GeneralizedGraph.SupportRevision.fresh_defaults
#print axioms Functional.GeneralizedGraph.SupportRevision.survivor_frame
#print axioms discoverSupported_keys
#print axioms discoverSupported_dangling
#print axioms Supported.mem_members_declared
#print axioms Supported.inactive_members
#print axioms added_component_dirty
#print axioms Supported.reader_dirty
#print axioms componentGroup_equation
#print axioms Functional.FeedbackCache.admitCache_approved
end LeanPoo.Examples.ComponentMembership
