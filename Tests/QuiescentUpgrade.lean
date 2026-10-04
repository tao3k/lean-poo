import LeanPoo.Object.Upgrade

namespace LeanPoo.Tests.QuiescentUpgrade
open Object Upgrade

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def initial (mode : ResolutionMode) : IO (Memoized String (fun _ => Nat)) := do
  let empty : Schema String (fun _ => Nat) :=
    { graph := { nodes := [] }, declaration := fun _ => none }
  let declaration := (Declaration.empty : Declaration String (fun _ => Nat))
    |>.withValue "count" 2
    |>.withSlot "derived" (.self fun self => (self "count").map (· + 1))
  match LeanPoo.mix empty "Base" [] declaration with
  | .error error => throw (IO.userError s!"{repr error}")
  | .ok plan => return plan.memoizeUsing mode

private def change (n : Nat) (old : Memoized String (fun _ => Nat)) :=
  old.reviseDeclaration "Base" fun d => d.withValue "count" n

private def sequential (mode : ResolutionMode) : IO Unit := do
  let runtime ← Runtime.new (← initial mode)
  let old ← runtime.withSnapshot fun version object => do
    ensure (version == 0) "initial version"
    return object
  let .ok old := old | throw (IO.userError "initial admission")
  let .ok session ← runtime.pause | throw (IO.userError "pause")
  ensure ((← runtime.pause).toOption.isNone) "duplicate pause"
  let blocked ← runtime.withSnapshot fun _ _ => (throw (IO.userError "must not enter") : IO Unit)
  ensure (match blocked with | .error .paused => true | _ => false) "closed admission"
  let failed ← session.commit (fun _ => (.error "conversion failed" : Except String _))
  ensure (match failed with | .error (.update _) => true | _ => false) "failed conversion"
  ensure ((← runtime.status).version == 0 && (← runtime.status).pending.isSome) "failure rollback"
  ensure ((← session.cancel).toOption.isSome) "cancel"
  let resumed ← runtime.withSnapshot fun version object => pure (version, object.read "derived")
  ensure (resumed.toOption == some (0, some 3)) "canceled failure preserved object"
  let .ok replacement ← runtime.pause | throw (IO.userError "replacement request")
  let stale ← session.commit (fun _ => (.error "stale updater evaluated" : Except String _))
  ensure (match stale with | .error (.control .stale) => true | _ => false) "canceled ticket reuse"
  let upgraded ← replacement.commit (change 5)
  ensure (upgraded.toOption == some 1) "version advance"
  ensure ((← replacement.cancel).toOption.isNone) "committed ticket reuse"
  let fresh ← runtime.withSnapshot fun version object =>
    pure (version, object.read "derived", object.mode == mode)
  ensure (fresh.toOption == some (1, some 6, true)) "new operation version"
  ensure (old.read "derived" == some 3) "unforced stack-held old target"
  let threw ← try
      let _ ← runtime.withSnapshot fun _ _ =>
        (throw (IO.userError "operation failed") : IO Unit)
      pure false
    catch _ => pure true
  ensure threw "operation exception must propagate"
  ensure ((← runtime.status).active == 0) "exception leaked admission"
  let .ok last ← runtime.pause | throw (IO.userError "last pause")
  ensure ((← last.commit (change 8)).toOption == some 2) "post-exception upgrade"

/-- Two real tasks remain in old-version callbacks while admission closes.
Each is released by a promise; no sleeps or timing assumptions are involved. -/
private def concurrent : IO Unit := do
  let runtime ← Runtime.new (← initial .indexed)
  let entered1 ← IO.Promise.new (α := Unit)
  let entered2 ← IO.Promise.new (α := Unit)
  let release1 ← IO.Promise.new (α := Unit)
  let release2 ← IO.Promise.new (α := Unit)
  let reader := fun (entered release : IO.Promise Unit) =>
    runtime.withSnapshot fun version object => do
      entered.resolve ()
      ensure release.result?.get.isSome "reader released promise dropped"
      return (version, object.read "derived")
  let task1 ← IO.asTask (reader entered1 release1) (prio := .dedicated)
  let task2 ← IO.asTask (reader entered2 release2) (prio := .dedicated)
  try
    ensure entered1.result?.get.isSome "first admission promise dropped"
    ensure entered2.result?.get.isSome "second admission promise dropped"
    let .ok session ← runtime.pause | throw (IO.userError "concurrent pause")
    let busy2 ← session.commit (fun _ => (.error "busy updater evaluated" : Except String _))
    ensure (match busy2 with | .error (.control (.busy 2)) => true | _ => false) "two active readers"
    release1.resolve ()
    let result1 ← IO.ofExcept task1.get
    ensure (result1.toOption == some (0, some 3)) "first old reader"
    let busy1 ← session.commit (change 5)
    ensure (match busy1 with | .error (.control (.busy 1)) => true | _ => false) "one active reader"
    release2.resolve ()
    let result2 ← IO.ofExcept task2.get
    ensure (result2.toOption == some (0, some 3)) "second old reader"
    ensure ((← session.commit (change 5)).toOption == some 1) "drained commit"
    let fresh ← runtime.withSnapshot fun version object => pure (version, object.read "derived")
    ensure (fresh.toOption == some (1, some 6)) "new reader after drain"
  finally
    release1.resolve ()
    release2.resolve ()

#eval (do
  for mode in [ResolutionMode.onDemand, .compiled, .indexed] do sequential mode
  concurrent
  IO.println "QUIESCENT-UPGRADE-OK" : IO Unit)
#print axioms Control.commit_quiescent
#print axioms Control.commit_authorized
#print axioms Control.enter_paused
end LeanPoo.Tests.QuiescentUpgrade
