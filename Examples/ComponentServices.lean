import LeanPoo.Functional.StrongComponents

/-! Future generalized prototypes: automatic groups, shared quota, cross-service
settlement and topology revisions reuse actual lens feedback closure. -/
namespace LeanPoo.Examples.ComponentServices
open Functional.StrongComponents Prototype Prototype.Generalized
/-- Same five named positions as native: quota, left, right, settlement, stable. -/
abbrev Key := Fin 5
/-- Non-record first-order raw storage with decidable whole-state equality. -/
abbrev Raw := Vector Nat 5
/-- Declared reads are independent of observed values. Right's edge toggles the SCC. -/
def edge (cyclic : Bool) (a b : Key) : Bool :=
  match a.val with
  | 1 => decide (b.val = 0 ∨ b.val = 2)
  | 2 => decide (b.val = 0) || (cyclic && decide (b.val = 1))
  | 3 => decide (b.val = 1 ∨ b.val = 2)
  | 4 => decide (b.val = 4)
  | _ => false
/-- Both concrete topologies pass executable certification without supplied groups. -/
def graph (cyclic : Bool) : Checked (edge cyclic) :=
  (discover (edge cyclic)).get (by cases cyclic <;> decide)
/-- Persistent vector focus uses the existing generalized lens compiler. -/
def focus (key : Key) : MonoLens Raw Nat :=
  MonoLens.ofGetSet (fun raw => raw.get key) (fun value raw => raw.set key.val value key.isLt)
/-- All three custom focus laws hold on the whole carrier, not only sampled states. -/
theorem focus_laws (key : Key) :
    LensLaws (fun raw : Raw => raw.get key) (fun value raw => raw.set key.val value key.isLt) := by
  constructor
  · intro raw; simp [Vector.get]
  · intro raw value
    change (raw.set key.val value key.isLt)[key.val] = value
    exact Vector.getElem_set_self key.isLt
  · intro raw first second; simp
/-- A complete equation reads same-stage cooked self internally, and the exact
already closed predecessor values externally. Quota is a source parameter. -/
def equation (quota : Nat) (cyclic : Bool) (key : Key) (read : Key → Nat) : Nat :=
  match key.val with
  | 0 => quota
  | 1 => min (read 0) (1 + read 2)
  | 2 => if cyclic then min (read 0) (1 + read 1) else read 0
  | 3 => read 1 + read 2
  | _ => min 2 (1 + read 4)
/-- Assemble the automatically discovered SCC using existing heterogeneous fragments. -/
def parts (quota : Nat) (cyclic : Bool) (input : List Key × Raw) : List (Fragment Raw Raw) :=
  input.1.map fun key => ⟨Nat,Unit,focus key,fun _ self _ =>
    equation quota cyclic key (fun dep => if dep ∈ input.1 then self.get.get dep else input.2.get dep),()⟩
/-- Each dirty group uses bounded whole-raw search AND every component residual. -/
def close (quota : Nat) (cyclic : Bool) (members : List Key) (external : Raw) :=
  Functional.FeedbackCache.closeGroup (parts quota cyclic) id (Vector.replicate 5 0)
    (members, external) (Vector.replicate 5 0) 32
/-- The example supplies a dependency-first representative visit order; groups
are discovered automatically and duplicate members are skipped. Production native
condensation uses the existing checked DAG scheduler instead of this fixture order. -/
def build (quota : Nat) (cyclic : Bool) : Except String Raw := do
  let mut state := Vector.replicate 5 0
  let mut done : List Key := []
  for key in ([0,2,1,3,4] : List Key) do
    if key ∉ done then
      let members := (graph cyclic).members key
      let group ← close quota cyclic members state
      state := members.foldl (fun raw node => raw.set node.val (group.result.closed.raw.get node) node.isLt) state
      done := done ++ members
  return state
/-- Joint service approval checks the current candidate, independently of reuse. -/
def approved (allowed : Bool) (limit : Nat) (state : Raw) : Bool :=
  allowed && decide (state.get 3 = state.get 1 + state.get 2 ∧ state.get 3 ≤ limit)
/-- Exact executable group membership on the shared cyclic graph. -/
example : (graph true).members 1 = [1,2] := by decide
/-- Removing one edge splits both formerly cyclic members into singleton groups. -/
example : (graph false).members 1 = [1] ∧ (graph false).members 2 = [2] := by decide
/-- Merge/split propagation reaches settlement, but not quota or the independent loop. -/
example : List.map ((graph false).dirty (revisionSeed (graph true) (graph false) (fun _ => false)))
    (List.finRange 5) = [false,true,true,true,false] := by decide
/-- Reverse topology revision also dirties the merged group and its reader. -/
example : List.map ((graph true).dirty (revisionSeed (graph false) (graph true) (fun _ => false)))
    (List.finRange 5) = [false,true,true,true,false] := by decide
/-- Shared quota propagates across both services and final settlement only. -/
example : List.map ((graph true).dirty (fun key => decide (key.val = 0))) (List.finRange 5) =
    [true,true,true,true,false] := by decide
/-- Concrete construction uses the same equations/cap/budget as the native example. -/
def check : Except String Unit := do
  let initial ← build 3 true
  let split ← build 3 false
  let merged ← build 3 true
  let revised ← build 4 true
  unless initial.toList == [3,3,3,6,2] && split == initial && merged == initial &&
      revised.toList == [4,4,4,8,2] do throw "component closure mismatch"
  unless approved true 8 revised && !approved true 7 revised && !approved false 8 revised do
    throw "current joint approval mismatch"
#eval match check with
  | .ok () => IO.println "COMPONENT-SERVICES-OK"
  | .error message => throw (IO.userError message)
#print axioms Checked.mem_members
#print axioms Checked.no_quotient_cycle
#print axioms membership_change_dirty
#print axioms footprint_change_dirty
#print axioms Checked.same_dirty
#print axioms Checked.clean_no_seed
#print axioms Functional.FeedbackCache.Group.fixed
#print axioms Functional.FeedbackCache.admitCache_approved
end LeanPoo.Examples.ComponentServices
