import LeanPoo.Functional.GraphRevision
import LeanPoo.Prototype.ComponentClosure

/-! Simultaneous SCC changes and shared-input migration in one service revision.
This exercises generalized-prototype future work, not unrestricted recursion. -/
namespace LeanPoo.Examples.ServiceRevisions
open Functional.StrongComponents Prototype Prototype.Generalized
/-- Same positions as native: quota/spare/shared, six endpoints, monitor, settlement, stable. -/
abbrev Key := Fin 12
/-- Comparable non-record carrier, with functions introduced only by lens compilation. -/
abbrev Raw := Vector Nat 12
/-- Full declared footprints for both final topologies, including unchanged monitor. -/
def reads (migrated : Bool) (key : Key) : List Key :=
  match key.val with
  | 2 => if migrated then [1,6] else [0,4]
  | 3 => if migrated then [2] else [2,4]
  | 4 => if migrated then [2] else [3]
  | 5 => if migrated then [2,6] else [0,6]
  | 6 => [5]
  | 7 => if migrated then [2,8] else [2]
  | 8 => if migrated then [2,7] else [2]
  | 9 => [2]
  | 10 => [3,4,5,6,7,8]
  | 11 => [11]
  | _ => []
/-- Graph discovery uses declared reads, never resulting service values. -/
def edge (migrated : Bool) (key dep : Key) : Bool := decide (dep ∈ reads migrated key)
/-- Functional vector updates preserve all unrelated component positions. -/
def focus (key : Key) : MonoLens Raw Nat :=
  MonoLens.ofGetSet (fun raw => raw.get key) (fun value raw => raw.set key.val value key.isLt)
/-- Custom storage laws hold for all vectors; native operational checks are finite. -/
theorem focus_laws (key : Key) :
    LensLaws (fun raw : Raw => raw.get key) (fun value raw => raw.set key.val value key.isLt) := by
  constructor
  · intro raw; simp [Vector.get]
  · intro raw value
    change (raw.set key.val value key.isLt)[key.val] = value
    exact Vector.getElem_set_self key.isLt
  · intro raw first second; simp
/-- Each first-order equation matches the native Computation recipe exactly. -/
def equation (quota spare : Nat) (migrated : Bool) (key : Key) (read : Key → Nat) : Nat :=
  match key.val with
  | 0 => quota
  | 1 => spare
  | 2 => if migrated then min (read 1) (1 + read 6) else min (read 0) (1 + read 4)
  | 3 => if migrated then read 2 else min (read 2) (1 + read 4)
  | 4 => if migrated then read 2 else read 3
  | 5 => if migrated then min (read 2) (1 + read 6) else min (read 0) (1 + read 6)
  | 6 => read 5
  | 7 => if migrated then min (read 2) (1 + read 8) else read 2
  | 8 => if migrated then min (read 2) (1 + read 7) else read 2
  | 9 => read 2
  | 10 => read 3 + read 4 + read 5 + read 6 + read 7 + read 8
  | _ => min 2 (1 + read 11)
/-- A reusable complete-equation family feeds the SAME lens closure as native. -/
def parts (quota spare : Nat) (migrated : Bool) (external : Raw) :=
  componentParts focus (equation quota spare migrated) (fun key (raw : Raw) => raw.get key) external.get
/-- Construct discovered groups; all first representatives happen to be in valid
source order for these fixtures. Native uses the existing checked DAG scheduler. -/
def build (quota spare : Nat) (migrated : Bool) (graph : Checked (edge migrated)) : Except String Raw := do
  let mut state := Vector.replicate 12 0
  let mut done : List Key := []
  for key in List.finRange 12 do
    if key ∉ done then
      let members := graph.members key
      let group ← Functional.FeedbackCache.closeGroup (parts quota spare migrated state) id
        (Vector.replicate 12 0) members (Vector.replicate 12 0) 32
      state := members.foldl (fun raw node => raw.set node.val (group.result.closed.raw.get node) node.isLt) state
      done := done ++ members
  return state
/-- Current cross-service approval includes every endpoint and the unchanged monitor. -/
def approved (allowed : Bool) (limit : Nat) (raw : Raw) : Bool :=
  allowed && ([3,4,5,6,7,8,9] : List Key).all (fun key => decide (raw.get key = raw.get 2)) &&
    decide (raw.get 10 = 6 * raw.get 2 ∧ raw.get 10 ≤ limit)
/-- Typed graph values match the native natural-valued component recipes. -/
abbrev Values := fun _ : Key => Nat
/-- Gather only declared inputs with the existing finite Computation constructors. -/
def collect : List Key → Functional.Computation Unit Key
    (fun _ _ => Except (Functional.ComputationError Key) Nat)
    (fun _ => Except (Functional.ComputationError Key) (List (Key × Nat)))
  | [] => .pure (fun _ => .ok [])
  | key :: rest => .both (.need key fun _ value => value) (collect rest) fun _ value tail => do
      return (key, ← value) :: (← tail)
/-- Copy one declared predecessor; missing providers retain the existing error path. -/
def copied (dep : Key) : Functional.GeneralizedGraph.Code Key Values dep := .need dep fun _ value => value
/-- Combine explicit cap/feedback reads through the existing typed Computation. -/
def advanced (cap dep : Key) : Functional.GeneralizedGraph.Code Key Values dep :=
  .both (copied cap) (copied dep) fun _ capValue depValue => do
    return min (← capValue) (1 + (← depValue))
/-- The actual resolver uses explicit reads, with no default for missing providers. -/
def program (migrated : Bool) (key : Key) : Functional.GeneralizedGraph.Code Key Values key :=
  match key.val with
  | 2 => if migrated then advanced 1 6 else advanced 0 4
  | 3 => if migrated then copied 2 else advanced 2 4
  | 4 => if migrated then copied 2 else copied 3
  | 5 => if migrated then advanced 2 6 else advanced 0 6
  | 6 => copied 5
  | 7 => if migrated then advanced 2 8 else copied 2
  | 8 => if migrated then advanced 2 7 else copied 2
  | 9 => copied 2
  | 10 => .map (collect [3,4,5,6,7,8]) fun _ entries => entries.map (fun values => (values.map Prod.snd).sum)
  | 11 => .map (copied 11) fun _ value => value.map (fun n => min 2 (1+n))
  | _ => .pure (fun _ => .ok 0)
/-- Persistent initial source separates code from base quota inputs, as in Scheme. -/
def source (quota spare : Nat) : Functional.GeneralizedGraph.Declaration Key Values :=
  ⟨List.finRange 12,fun key => if key.val < 2 then none else some (program false key),
    fun key => if key.val = 0 then some (.ok quota) else if key.val = 1 then some (.ok spare) else none⟩
/-- Same immutable multi-service batch: all seven recipes and one quota input. -/
def revise (spec : Functional.GeneralizedGraph.Declaration Key Values) (migrated : Bool) (spare : Nat) :=
  Functional.GeneralizedGraph.Revision.create spec
    (([2,3,4,5,6,7,8] : List Key).map (fun key => ⟨key,some (program migrated key)⟩))
    [⟨1,some (.ok spare)⟩]
/-- Executable certificates are obtained at runtime, avoiding an invented static
partition or serialized native witness. Generic theorems apply to accepted results. -/
def check : Except String Unit := do
  let some old := discover (edge false) | throw "original discovery refused"
  let some next := discover (edge true) | throw "migrated discovery refused"
  unless (old.members 2).map Fin.val == [2,3,4] && (next.members 2).map Fin.val == [2,5,6] &&
      (old.members 7).map Fin.val == [7] && (next.members 7).map Fin.val == [7,8] do
    throw "simultaneous grouping mismatch"
  let dirty := (List.finRange 12).map (next.dirty (revisionSeed old next (fun _ => false)))
  unless dirty == [false,false,true,true,true,true,true,true,true,true,true,false] do
    throw "migration propagation mismatch"
  unless (List.finRange 12).map (next.dirty (fun key => decide (key.val = 0))) ==
      [true,false,false,false,false,false,false,false,false,false,false,false] do
    throw "obsolete quota still invalidates detached services"
  unless (List.finRange 12).map (next.dirty (fun key => decide (key.val = 1))) ==
      [false,true,true,true,true,true,true,true,true,true,true,false] do
    throw "new quota does not invalidate migrated services"
  let reverseDirty := (List.finRange 12).map (old.dirty (revisionSeed next old (fun _ => false)))
  unless reverseDirty == dirty do throw "reverse regrouping mismatch"
  let initial ← build 3 4 false old
  let migrated ← build 3 4 true next
  let equalOld ← build 3 3 false old
  let equalNext ← build 3 3 true next
  let revised ← build 3 5 true next
  let back ← build 2 5 false old
  unless initial.toList == [3,4,3,3,3,3,3,3,3,3,18,2] &&
      migrated.toList == [3,4,4,4,4,4,4,4,4,4,24,2] && equalOld == equalNext &&
      revised.toList == [3,5,5,5,5,5,5,5,5,5,30,2] && back.toList == [2,5,2,2,2,2,2,2,2,2,12,2] do
    throw "whole group construction mismatch"
  let .ok revision := revise (source 3 4) true 5 | throw "batch admission refused"
  let finalSource := revision.apply
  unless (List.finRange 12).all (fun key => finalSource.reads key == reads true key) do
    throw "batch footprint mismatch"
  let state : Functional.GeneralizedGraph.State Key Values := fun key => some (.ok (revised.get key))
  unless (List.finRange 12).all (fun key => match finalSource.resolve key state with
      | some (.ok value) => value == revised.get key
      | _ => false) do
    throw "batch actual resolver mismatch"
  match Functional.GeneralizedGraph.Revision.create (source 3 4)
      [⟨2,some (program true 2)⟩,⟨2,some (program false 2)⟩] [] with
  | .ok _ => throw "duplicate batch accepted"
  | .error _ => pure ()
  unless approved true 30 revised && !approved true 18 revised && !approved false 30 revised do
    throw "current joint admission mismatch"
#eval match check with
  | .ok () => IO.println "SERVICE-REVISIONS-OK"
  | .error message => throw (IO.userError message)
#print axioms Functional.GeneralizedGraph.Revision.apply_code_at
#print axioms Functional.GeneralizedGraph.Revision.apply_base_at
#print axioms Functional.GeneralizedGraph.Revision.apply_resolve_frame
#print axioms Checked.clean_if_no_seed
#print axioms Checked.dirty_union
#print axioms migration_reader_dirty
#print axioms simultaneous_revision_dirty
#print axioms componentGroup_equation
#print axioms Functional.FeedbackCache.admitCache_approved
end LeanPoo.Examples.ServiceRevisions
