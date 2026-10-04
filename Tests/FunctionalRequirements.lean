import LeanPoo.Functional.Requirements

namespace LeanPoo.Tests.FunctionalRequirements
open Functional C4

universe u v w
variable {Context : Type u} {Key : Type v} {Value : Context → Key → Type w}

example (provider : Provider Context Key Value) (keys : List Key)
    (factories : Requirements.Factories Context Value keys)
    (ready : Requirements.prepare provider keys = .ok factories) :
    Requirements.Selected provider keys factories := (Requirements.prepare_ok_iff _ _ _).mp ready

example (order : VerifiedOrder graph root) (providers : String → Provider Context Key Value)
    (keys : List Key) (factories : Requirements.Factories Context Value keys)
    (ready : Requirements.prepare (assemble order providers) keys = .ok factories)
    (key : Key) (requested : key ∈ keys) :
    ∃ name, Ancestor graph name root ∧ ∃ factory, providers name key = some factory :=
  Requirements.prepare_origin order providers keys factories ready key requested

example (order : VerifiedOrder graph root) (providers : String → Provider Context Key Value)
    (rename : String → String) (injective : Function.Injective rename)
    (unique : (graph.nodes.map Node.name).Nodup)
    (mapped : String → Provider Context Key Value)
    (aligned : ∀ name, Ancestor graph name root → mapped (rename name) key = providers name key) :
    assemble (order.rename rename injective unique) mapped key = assemble order providers key :=
  assemble_rename order rename injective unique mapped aligned

private inductive Capability where
  | background | derivative | residual
  deriving BEq, DecidableEq, Repr

private structure SampleContext where
  minimum : Nat

private def SampleValue (context : SampleContext) : Capability → Type
  | .background => {n : Nat // context.minimum ≤ n}
  | .derivative => Bool
  | .residual => {n : Nat // context.minimum + 2 ≤ n}

private def provider (mask : Nat) : Provider SampleContext Capability SampleValue
  | .background => if mask % 2 == 1 then some (fun c => ⟨c.minimum + 1, by omega⟩) else none
  | .derivative => if mask / 2 % 2 == 1 then some (fun c => c.minimum % 2 == 0) else none
  | .residual => if mask / 4 % 2 == 1 then some (fun c => ⟨c.minimum + 3, by omega⟩) else none

private def allKeys : List Capability := [.background, .derivative, .residual]
private def requests (mask : Nat) : List Capability :=
  allKeys.filter fun key => match key with
    | .background => mask % 2 == 1
    | .derivative => mask / 2 % 2 == 1
    | .residual => mask / 4 % 2 == 1

private def expected (context : SampleContext) : (keys : List Capability) → Requirements.Results SampleValue context keys
  | [] => PUnit.unit
  | .background :: rest => (⟨context.minimum + 1, by omega⟩, expected context rest)
  | .derivative :: rest => (context.minimum % 2 == 0, expected context rest)
  | .residual :: rest => (⟨context.minimum + 3, by omega⟩, expected context rest)

private def equalResults (context : SampleContext) : (keys : List Capability) →
    Requirements.Results SampleValue context keys → Requirements.Results SampleValue context keys → Bool
  | [], _, _ => true
  | .background :: rest, (a, as), (b, bs) => a.val == b.val && equalResults context rest as bs
  | .derivative :: rest, (a, as), (b, bs) => (@BEq.beq Bool inferInstance a b) && equalResults context rest as bs
  | .residual :: rest, (a, as), (b, bs) => a.val == b.val && equalResults context rest as bs

/- Independent first-missing oracle, with reversed and repeated requests. -/
private def check (mask : Nat) (keys : List Capability) : Bool :=
  let firstMissing := keys.find? (fun key => (provider mask key).isNone)
  match Requirements.prepare (provider mask) keys, firstMissing with
  | .error actual, some missing => actual == missing
  | .ok retained, none => [5, 10].all fun minimum =>
      let context : SampleContext := ⟨minimum⟩
      equalResults context keys (Requirements.build retained context) (expected context keys)
  | _, _ => false

private def corpus : Bool := (List.range 8).all fun mask => (List.range 8).all fun requested =>
  let keys := requests requested
  [keys, keys.reverse, keys ++ keys].all (check mask)
#guard corpus
#eval IO.println "FUNCTIONAL-REQUIREMENTS-OK 192 preparations; heterogeneous results at two contexts"

/- A capability/context change must still change the witness type. -/
example (_old : SampleValue ⟨5⟩ .background) : True := by
  fail_if_success have _wrongContext : SampleValue ⟨10⟩ .background := _old
  fail_if_success have _wrongKey : SampleValue ⟨5⟩ .residual := _old
  trivial

private def graph : Graph := {nodes := [
  {name := "Source"}, {name := "Override", parentOrders := [["Source"]]}]}
private def providers : String → Provider SampleContext Capability SampleValue
  | "Source" => provider 7
  | "Override" => fun key => match key with
    | .residual => some fun c => ⟨c.minimum + 7, by omega⟩
    | _ => none
  | _ => fun _ => none
private def mapped : String → Provider SampleContext Capability SampleValue
  | "case/Source" => providers "Source"
  | "case/Override" => providers "Override"
  | _ => fun _ => none
private def misaligned : String → Provider SampleContext Capability SampleValue := fun _ => fun _ => none

private def run {g : Graph} {r : String}
    (family : String → Provider SampleContext Capability SampleValue) (order : VerifiedOrder g r) :
    Option (Nat × Bool × Nat) :=
  (Requirements.prepare (assemble order family) allKeys).toOption.map fun retained =>
    let results := Requirements.build (Value := SampleValue) (keys := allKeys) retained (⟨10⟩ : SampleContext)
    (results.1.val, results.2.1, results.2.2.1.val)

private def renamedCase : Bool :=
  match linearizeVerified graph "Override",
      linearizeVerified (graph.rename ("case/" ++ ·)) "case/Override" with
  | .ok old, .ok renamed =>
    run providers old == some (11, true, 17) &&
    run mapped renamed == run providers old &&
    (Requirements.prepare (assemble renamed misaligned) allKeys).toOption.isNone
  | _, _ => false
#guard renamedCase

#print axioms select_rename
#print axioms assemble_rename
#print axioms Requirements.prepare_ok_iff
#print axioms Requirements.Selected.available
#print axioms Requirements.prepare_origin
#print axioms Requirements.prepare_missing_head
end LeanPoo.Tests.FunctionalRequirements
