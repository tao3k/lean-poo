import LeanPoo.Functional.ConstructionCache
import LeanPoo.Functional.ConstructionWorkflow

/-! Construction controls distinguish absent, failed and successful slots,
duplicate schedule visits, and genuine builder skipping. Future work. -/
namespace LeanPoo.Tests.ConstructionCache
open Functional Functional.GeneralizedGraph Functional.ConstructionCache

abbrev Field : Bool → Type
  | false => Nat
  | true => String

def heterogeneous : Declaration Bool Field where
  keys := [true,false]
  base := fun key => match key with | false => some (.ok 17) | true => none
  code := fun key => match key with
    | false => none
    | true => some (.need false fun _ value => value.map (fun n => "count:" ++ toString n))

def typed : Except String Unit := do
  let scheduled ← heterogeneous.schedule.mapError (fun _ => "heterogeneous schedule")
  let cold ← (start scheduled (Builder.guarded heterogeneous (fun _ => true))).mapError (fun _ => "heterogeneous cold")
  unless (cold.closed.raw false).bind Except.toOption == some 17 &&
      (cold.closed.raw true).bind Except.toOption == some "count:17" && cold.evaluated.length == 2 do
    throw "dependent materialized values"
  let repeated := {scheduled with order := scheduled.order ++ scheduled.order}
  let duplicate ← (start repeated (Builder.guarded heterogeneous (fun _ => true))).mapError (fun _ => "duplicate cold")
  unless duplicate.evaluated.length == 2 do throw "a completed node was reevaluated"
  let hot ← (refresh scheduled cold (fun _ => false) (by intro key _ self; rfl)
    (Builder.guarded heterogeneous (fun _ => false))).mapError (fun _ => "hot typed builder invoked")
  unless hot.evaluated.isEmpty && hot.reused.length == 2 &&
      (hot.closed.raw true).bind Except.toOption == some "count:17" do throw "typed cache reuse"
  unless (start scheduled (Builder.guarded heterogeneous (fun _ => false))).toOption.isNone do
    throw "cold refusing builder was bypassed"

/-- A valid closed graph may contain business failures. Those results and real
absences are materialized and retained, independently of later MOP admission. -/
def outcomes : Except String Unit := do
  let spec := (ConstructionWorkflow.graph {input := 30}).define "invoice" (.failure "stable-source")
  let scheduled ← spec.schedule.mapError (fun _ => "failure schedule")
  let cold ← (start scheduled (Builder.guarded spec (fun _ => true))).mapError (fun _ => "failure cold")
  let hot ← (refresh scheduled cold (fun _ => false) (by intro key _ self; rfl)
    (Builder.guarded spec (fun _ => false))).mapError (fun _ => "failed/absent slots were rebuilt")
  unless hot.evaluated.isEmpty && hot.reused.length == 15 do throw "failed graph did not skip every node"
  for key in ["invoice","release","total"] do
    match hot.closed.raw key with
    | some (.error (.source "stable-source")) => pure ()
    | _ => throw "source error lost in reuse"
  for key in ["discount","blocked","permit","outside"] do
    unless (hot.closed.raw key).isNone do throw "absence became a present cached failure"
  -- A malformed order must refuse instead of publishing a partial dictionary.
  let backwards := {scheduled with order := scheduled.order.reverse}
  unless (start backwards (Builder.guarded spec (fun _ => true))).toOption.isNone do throw "unready dependency accepted"
  let missing := {scheduled with order := []}
  unless (start missing (Builder.guarded spec (fun _ => true))).toOption.isNone do throw "incomplete materialization accepted"

/-- A root revision keeps the complete footprint and checked ranks while the
materializer rebuilds its shared downstream cone. -/
def preparation : Except String Unit := do
  let spec := ConstructionWorkflow.graph {input := 30}
  let prior ← spec.schedule.mapError (fun _ => "preparation schedule")
  let old ← (start prior (Builder.guarded spec (fun _ => true))).mapError (fun _ => "preparation cold")
  let retained := old.retain prior.order
  unless retained.evaluated.isEmpty && retained.reused.length == 15 do throw "retain accounting"
  let next := spec.setBase "input" (some (.ok 60))
  let reused := prior.rebase (spec := next)
    (by intro key; rfl) (by intro key; exact prior.known key)
  unless reused.order == prior.order do throw "schedule copied differently"
  let hot ← (refresh reused old (fun key => key == "input") (by
    intro key clean self
    have different : "input" ≠ key := by
      intro same
      subst key
      simp only [beq_self_eq_true] at clean
      contradiction
    exact spec.setBase_resolve_frame "input" key _ different self)
    (Builder.guarded next (["input","freight","cover","reserve","tax","risk","settlement","invoice","audit","release","total"].contains ·))).mapError (fun _ => "retained schedule construction")
  unless hot.evaluated.length == 11 && hot.reused.length == 4 &&
      (hot.closed.raw "total").bind Except.toOption == some 58 do throw "shared root result"

def run : IO Unit := do
  let _ ← IO.ofExcept typed
  let _ ← IO.ofExcept outcomes
  let _ ← IO.ofExcept preparation
  IO.println "CONSTRUCTION-CACHE-CONTROLS-OK dependent-values duplicate-visit-skipping cold-refusal stable-errors real-absence incomplete-order-refusal"
#eval run
#print axioms Functional.ConstructionCache.Partial.step_done
#print axioms Functional.ConstructionCache.Cache.reference
#print axioms Functional.GeneralizedGraph.Scheduled.rebase
#print axioms Functional.ConstructionCache.Cache.retain_closed
end LeanPoo.Tests.ConstructionCache
