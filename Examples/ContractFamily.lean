import LeanPoo.Functional.ContractFamily
import LeanPoo.Functional.ServiceMetadata

/-! Heterogeneous reserve/cancel contracts across cross-service revisions.
Generalized-prototype future work; wrapper state is always the actual caller state. -/
namespace LeanPoo.Examples.ContractFamily
open Functional Functional.ServiceBundle Functional.ContractFamily Functional.DeclarativeMetadata

structure Current where
  capacity : Int
  invoice : String
  revision : Nat

abbrev Atoms : Service → Type | .reserve => ServiceMetadata.Atom | _ => Unit
abbrev Inputs : Service → Type | .reserve => Int | .cancel => String | .quote => Unit

def cancellation (invoice : String) : Contract Unit (String × Bool) (ConstructionWorkflow.Action (List String)) where
  input := ⟨"consent",fun args => args.2 = true,fun _ => inferInstance⟩
  output := ⟨"successful-cancellation",fun result => result.isOk = true,fun _ => inferInstance⟩
  meaning := fun _ args result => match result with | .ok events => events = [args.1,invoice] | .error _ => False
  decide := by intro atom args result; cases result <;> exact inferInstance
  rule := .atom ()

/-- Prototype specialization preserves exactly the original metadata semantics. -/
def specializedReservation (capacity : Int) :=
  (ServiceMetadata.reservation 0).withMeaning (ServiceMetadata.reservation capacity).meaning
    (ServiceMetadata.reservation capacity).decide

theorem specialized_reservation_eq (capacity : Int) :
    specializedReservation capacity = ServiceMetadata.reservation capacity := rfl

def specializedCancellation (invoice : String) :=
  (cancellation "").withMeaning (cancellation invoice).meaning (cancellation invoice).decide

theorem specialized_cancellation_eq (invoice : String) :
    specializedCancellation invoice = cancellation invoice := rfl

def source : Source Service (List Service) Current Atoms Args Result String where
  Context := Inputs
  keys := fun selected _ => selected
  project := fun key _ current => match key with
    | .reserve => current.capacity
    | .cancel => current.invoice
    | .quote => ()
  construct := fun key inputs => match key with
    | .reserve => .ok (ServiceMetadata.reservation inputs)
    | .cancel => .ok (cancellation inputs)
    | .quote => .error "no quote contract"

instance : (key : Service) → DecidableEq (source.Context key) := fun key => match key with
  | .quote => inferInstanceAs (DecidableEq Unit)
  | .reserve => inferInstanceAs (DecidableEq Int)
  | .cancel => inferInstanceAs (DecidableEq String)

def execute : (key : Service) → Current → Args key → Except String (Result key × Current)
  | .reserve, current, units => .ok (.ok (current.capacity-units,decide ((units : Int) ≤ current.capacity)), {current with revision := current.revision+1})
  | .cancel, current, args => .ok ((if args.2 then .ok [args.1,current.invoice] else .error "consent"), {current with revision := current.revision+1})
  | .quote, current, _ => .ok (.ok current.capacity,current)

def badExecute : (key : Service) → Current → Args key → Except String (Result key × Current)
  | .reserve, current, _ => .ok (.ok (99,true),current)
  | key, current, args => execute key current args

abbrev Prepared (selected : List Service) (current : Current) := Family source execute selected current

def withFamily {runner : (key : Service) → Current → Args key → Except String (Result key × Current)}
    {selected : List Service} {current : Current}
    (outcome : Except (PreparationError Service String) (Family source runner selected current))
    (next : Family source runner selected current → Except String Unit) : Except String Unit :=
  match outcome with | .error error => .error (reprStr error) | .ok family => next family

/-- One closed shared pair feeds the existing heterogeneous source. -/
def shared : SharedProjection Service (List Service) Current (Int × String) (Int × String) Inputs where
  input := fun _ current => (current.capacity,current.invoice)
  prepare := id
  project := fun key prepared => match key with
    | .reserve => prepared.1
    | .cancel => prepared.2
    | .quote => ()

def sharedSource := shared.toSource source.keys source.construct

/-- Invoice changes invalidate common preparation but not reservation semantics. -/
theorem shared_reserve_unchanged (capacity : Int) (invoice₁ invoice₂ : String) :
    sharedSource.project .reserve [] ⟨capacity,invoice₁,1⟩ =
      sharedSource.project .reserve [] ⟨capacity,invoice₂,2⟩ := rfl

theorem shared_cancellation_current (capacity : Int) (invoice : String) :
    sharedSource.project .cancel [] ⟨capacity,invoice,2⟩ = invoice := rfl

#eval do
  let input : Int × String := (10,"invoice:1")
  let cold := shared.refresh input none
  let retained := shared.refresh input (some ⟨input,cold.1⟩)
  let revised := shared.refresh (10,"invoice:2") (some ⟨input,retained.1⟩)
  unless cold.2 == 1 && retained.2 == 0 && revised.2 == 1 do
    throw (IO.userError "shared preparation count")
  unless shared.project .reserve revised.1.value == 10 && shared.project .cancel revised.1.value == "invoice:2" do
    throw (IO.userError "shared heterogeneous inputs")
  IO.println "SHARED-CONTRACTS-OK cold=1 retained=0 joint=1 heterogeneous-current"

theorem direct_shared_coherent (key : Service) (input : Int × String) :
    (match key with | .reserve => input.1 | .cancel => input.2 | .quote => ()) =
      shared.project key (shared.prepare input) := by cases key <;> rfl

#eval do
  let cheap : PreparationCosts := ⟨3,1,1,1⟩
  let indexed : PreparationCosts := ⟨3,1,20,1⟩
  let guarded : PreparationCosts := ⟨3,1,1,3⟩
  unless cheap.choose 2 == PreparationCosts.Strategy.direct && indexed.choose 2 == PreparationCosts.Strategy.shared && guarded.choose 2 == PreparationCosts.Strategy.shared do
    throw (IO.userError "preparation strategy or selector accounting")
  let prices : PreparationCosts.PublicationCosts := ⟨8,12,1,20,4⟩
  unless prices.total (cheap.selected 2) 2 2 3 3 ≤ prices.total (cheap.shared 2) 2 2 3 3 do
    throw (IO.userError "publication stage cost")
  let templates : PreparationCosts.TemplateCosts := ⟨24,2,20⟩
  unless templates.setup + templates.specialize > templates.rebuild &&
      templates.setup + 2 * templates.specialize ≤ 2 * templates.rebuild do
    throw (IO.userError "one-time template setup must be amortized")
  IO.println "CONTRACT-STRATEGY-OK direct/shared/selector-budget invariant-template setup-amortization"

def check : Except String Unit :=
  let initial : Current := ⟨10,"invoice:1",1⟩
  let revised : Current := ⟨10,"invoice:2",2⟩
  let selected := [Service.reserve,.cancel]
  withFamily (prepare source execute selected initial (fun _ => true)) fun cold =>
  withFamily (refresh source execute selected initial (some cold) (some ⟨rfl⟩) (fun _ => true)) fun retained =>
  withFamily (refresh source execute selected revised (some retained) (some ⟨rfl⟩) (fun _ => true)) fun changed => do
    unless cold.built == selected && cold.bound == selected do throw "cold preparation"
    unless retained.built.isEmpty && retained.bound.isEmpty && retained.reused == selected do throw "unchanged work"
    unless changed.built == [.cancel] && changed.bound == [.cancel] && changed.reused == [.reserve] do throw "selective contract construction"
    match changed.cells.get? .reserve, changed.cells.get? .cancel with
    | some reserve, some cancel =>
      let (result,state) ← (reserve.bound revised 2).mapError (fun _ => "retained reserve")
      unless result.toOption == some (8,true) && state.revision == 3 do throw "wrapper captured old state"
      let (events,_) ← (cancel.bound revised ("customer",true)).mapError (fun _ => "revised cancellation")
      unless events.toOption == some ["customer","invoice:2"] do throw "contract captured stale invoice"
    | _,_ => throw "incomplete family"
    withFamily (refresh source badExecute selected revised (some changed) none (fun _ => true)) fun rebound => do
      unless rebound.built.isEmpty && rebound.bound == selected do throw "executor change reused wrapper"
      match rebound.cells.get? .reserve with
      | some entry => match entry.bound revised 2 with
        | .error .logic => pure ()
        | _ => throw "rebound executor escaped conservation"
      | none => throw "missing rebound reserve"
      withFamily (refresh source execute [.reserve] revised (some changed) (some ⟨rfl⟩) (fun _ => true)) fun removed => do
        unless (removed.cells.get? .cancel).isNone do throw "removed contract still callable"
        let old : Snapshot source execute := ⟨selected,revised,changed⟩
        let refused := publish source execute old selected revised (fun _ => true) (fun _ => Except.error "joint-refusal")
        match refused.1 with
        | .error (.inr "joint-refusal") => pure ()
        | _ => throw "joint approval bypassed"
        match refresh source execute [Service.reserve,.reserve] revised (some changed) (some ⟨rfl⟩) (fun _ => true) with
        | .error (.duplicate .reserve) => pure ()
        | _ => throw "duplicate contract accepted"
        match refresh source execute selected revised (some changed) (some ⟨rfl⟩) (fun key => key != .reserve) with
        | .error (.missing .reserve) => pure ()
        | _ => throw "orphan retained contract accepted"

#eval match check with
  | .ok () => IO.println "CONTRACT-FAMILY-OK retained-wrapper current-state selective-invoice executor-rebind removal duplicate missing-service joint-refusal"
  | .error error => throw (IO.userError error)
#print axioms Functional.ContractFamily.Family.step_retained
#print axioms Functional.ContractFamily.Cell.retain_bound
#print axioms Functional.ContractFamily.Cell.rebind_contract
#print axioms Functional.ContractFamily.Family.step_missing
#print axioms Functional.ContractFamily.SharedProjection.refresh_project
#print axioms Functional.ContractFamily.SharedProjection.refresh_retained
#print axioms Functional.ContractFamily.SharedProjection.cached_source_project
#print axioms Functional.ContractFamily.SharedProjection.refresh_cost
#print axioms Functional.ContractFamily.SharedProjection.retain_origin
#print axioms specialized_reservation_eq
#print axioms specialized_cancellation_eq
#print axioms Functional.DeclarativeMetadata.Contract.withMeaning_input
#print axioms Functional.DeclarativeMetadata.Contract.withMeaning_rule
#print axioms Functional.ContractFamily.SharedProjection.direct_source_project
#print axioms Functional.ContractFamily.SharedProjection.direct_source_eq
#print axioms Functional.ContractFamily.PreparationCosts.direct_covered
#print axioms Functional.ContractFamily.PreparationCosts.selected_bound
#print axioms Functional.ContractFamily.PreparationCosts.publication_direct_bound
#print axioms Functional.ContractFamily.PreparationCosts.template_amortized
#print axioms Functional.ContractFamily.publish_refused
end LeanPoo.Examples.ContractFamily
