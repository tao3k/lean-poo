import LeanPoo.Examples.ComponentRounds
import LeanPoo.Functional.SharedPublication

/-! Shared and local approval dependencies across independent component endpoints.
Actual typed source closure remains separate from abstract serialized head choice. -/
namespace LeanPoo.Examples.SharedApprovals
open Functional.GeneralizedGraph Functional.StrongComponents
open LeanPoo.Examples.ComponentRounds
/-- Three registered policies: shared, endpoint A local, endpoint B local. -/
abbrev Policy := Fin 3
/-- Local fixture revisions are abstract witnesses, never native runtime inputs. -/
def old : Policy → Nat := fun _ => 0
/-- A single coordinated shared-policy edit affects BOTH observed vectors. -/
def sharedEdit : Policy → Nat := fun key => if key.val = 0 then 1 else 0
/-- A local-only edit affects only the endpoint that declares that policy. -/
def localEdit : Policy → Nat := fun key => if key.val = 1 then 1 else 0
/-- Native endpoints share one policy object and register distinct local objects. -/
def dependencies (endpoint : Fin 2) : List Policy := if endpoint.val = 0 then [0,1] else [0,2]
/-- Independent current heads can diverge while sharing approval revisions. -/
def heads : Fin 2 → Nat := fun _ => 0
/-- Construct actual SCC closures, then exercise shared invalidation, local framing
and restaging on independent heads with the serialized model. -/
def check : Except String Unit := do
  let .ok a := SupportRevision.joinAt (0 : Nat) 0 source (contributions .merge) | throw "endpoint A refused"
  let .ok b := SupportRevision.joinAt (0 : Nat) 0 source
    (contributions .merge [⟨1,some (.ok 5)⟩]) | throw "endpoint B refused"
  let rawA ← execute a.apply
  let rawB ← execute b.apply
  unless rawA.get 10 == 24 && rawB.get 10 == 30 do throw "shared service closure mismatch"
  let stagedA := Functional.ComponentPublication.observed (dependencies 0) old
  let stagedB := Functional.ComponentPublication.observed (dependencies 1) old
  let liveA := Functional.ComponentPublication.observed (dependencies 0) sharedEdit
  let liveB := Functional.ComponentPublication.observed (dependencies 1) sharedEdit
  let heldA := Functional.ComponentPublication.installEntry heads (0 : Fin 2) 0 1 stagedA liveA true
  let heldB := Functional.ComponentPublication.installEntry heldA (1 : Fin 2) 0 2 stagedB liveB true
  unless (List.finRange 2).all (fun key => heldB key == heads key) do throw "shared invalidation changed a head"
  let nextA := Functional.ComponentPublication.installEntry heldB (0 : Fin 2) 0 1 liveA liveA
    (approved a.apply true true 30 rawA)
  unless nextA 0 == 1 && nextA 1 == 0 do throw "endpoint A installed into sibling"
  let nextB := Functional.ComponentPublication.installEntry nextA (1 : Fin 2) 0 2 liveB liveB
    (approved b.apply true true 30 rawB)
  unless nextB 0 == 1 && nextB 1 == 2 do throw "fresh sibling snapshot incorrectly became stale"
  let unaffectedB := Functional.ComponentPublication.observed (dependencies 1) localEdit
  unless stagedB == unaffectedB && stagedA != Functional.ComponentPublication.observed (dependencies 0) localEdit do
    throw "local invalidation leaked to independent dependency vector"
  let .ok split := SupportRevision.joinAt (1 : Nat) (nextB 0) a.apply (contributions .replace) |
    throw "local topology restaging refused"
  let splitRaw ← execute split.apply
  unless splitRaw.get 10 == 16 do throw "endpoint A restaged closure mismatch"
#eval match check with
  | .ok () => IO.println "SHARED-APPROVALS-OK"
  | .error message => throw (IO.userError message)
#print axioms Functional.ComponentPublication.entry_frame
#print axioms Functional.ComponentPublication.entry_stale
#print axioms Functional.ComponentPublication.observed_frame
#print axioms Functional.ComponentPublication.shared_observer_stale
#print axioms Functional.ComponentPublication.observed_changed
#print axioms Functional.ComponentExecution.resolved_correct
end LeanPoo.Examples.SharedApprovals
