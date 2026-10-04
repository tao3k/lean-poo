import LeanPoo.Functional.Reindex

namespace LeanPoo.Tests.FunctionalReindex
open Functional

universe u v w x
variable {Context : Type u} {Outer : Type x} {Key : Type v}
variable {Value : Context → Key → Type w}

example (project : Outer → Context) (order : C4.VerifiedOrder graph root)
    (providers : String → Provider Context Key Value) :
    assemble order (fun name => reindexProvider project (providers name)) =
      reindexProvider project (assemble order providers) :=
  assemble_reindex project order providers

example (project : Outer → Context) (provider : Provider Context Key Value) (keys : List Key) :
    Requirements.prepare (reindexProvider project provider) keys =
      (Requirements.prepare provider keys).map (Requirements.reindex project) :=
  Requirements.prepare_reindex project provider keys

/- An existing proof-producing consumer is reused, and states only a claim at
the projected old context, not a claim about arbitrary new context fields. -/
example (project : Outer → Context) (Claim : Context → Prop) (known : ∀ c, Claim c) :
    Factory Outer (fun outer => PLift (Claim (project outer))) :=
  Factory.reindex project (Factory.fromProof known)

private inductive Capability where
  | background | flag | residual
  deriving BEq, DecidableEq
private structure Legacy where
  minimum : Nat
private structure Extended where
  legacy : Legacy
  extraMinimum : Nat
private def SampleValue (context : Legacy) : Capability → Type
  | .background => {n : Nat // context.minimum ≤ n}
  | .flag => Bool
  | .residual => {n : Nat // context.minimum + 2 ≤ n}
private def provider (mask : Nat) : Provider Legacy Capability SampleValue
  | .background => if mask % 2 == 1 then some (fun c => ⟨c.minimum + 1, by omega⟩) else none
  | .flag => if mask / 2 % 2 == 1 then some (fun c => c.minimum % 2 == 0) else none
  | .residual => if mask / 4 % 2 == 1 then some (fun c => ⟨c.minimum + 3, by omega⟩) else none
private def lists : List (List Capability) :=
  [[], [.background], [.flag], [.residual], [.background, .flag, .residual],
   [.residual, .flag, .background], [.residual, .background], [.residual, .residual]]
private def samples : List Extended := [⟨⟨5⟩, 99⟩, ⟨⟨10⟩, 0⟩]

private def encode (context : Legacy) : (keys : List Capability) →
    Requirements.Results SampleValue context keys → List Nat
  | [], _ => []
  | .background :: rest, (value, tail) => value.val :: encode context rest tail
  | .flag :: rest, (value, tail) => (Bool.toNat value) :: encode context rest tail
  | .residual :: rest, (value, tail) => value.val :: encode context rest tail
private def expected (context : Legacy) (keys : List Capability) : List Nat :=
  keys.map fun key => match key with
    | .background => context.minimum + 1
    | .flag => if context.minimum % 2 == 0 then 1 else 0
    | .residual => context.minimum + 3

private def check (mask : Nat) (keys : List Capability) : Bool :=
  let firstMissing := keys.find? fun key => (provider mask key).isNone
  match Requirements.prepare (provider mask) keys,
      Requirements.prepare (reindexProvider Extended.legacy (provider mask)) keys,
      firstMissing with
  | .error a, .error b, some missing => a == missing && b == missing
  | .ok old, .ok adapted, none => samples.all fun outer =>
      let fromOld := encode outer.legacy keys (Requirements.build old outer.legacy)
      let fromAdapted := encode outer.legacy keys
        (Requirements.projectedResults Extended.legacy keys outer (Requirements.build adapted outer))
      let afterPreparation := encode outer.legacy keys
        (Requirements.projectedResults Extended.legacy keys outer
          (Requirements.build (Requirements.reindex Extended.legacy old) outer))
      fromOld == expected outer.legacy keys && fromAdapted == fromOld && afterPreparation == fromOld
  | _, _, _ => false
#guard (List.range 8).all fun mask => lists.all (check mask)

private def prove (c : Legacy) : PLift (c.minimum ≤ c.minimum + 1) := ⟨by omega⟩
private def inherited := Factory.reindex Extended.legacy prove
example (outer : Extended) : outer.legacy.minimum ≤ outer.legacy.minimum + 1 := (inherited outer).down
example (_proof : PLift (5 ≤ 6)) : True := by
  fail_if_success have _ : PLift (99 ≤ 6) := _proof
  trivial
example (_old : SampleValue ⟨5⟩ .background) : True := by
  fail_if_success have _ : SampleValue ⟨99⟩ .background := _old
  trivial

#print axioms select_reindex
#print axioms assemble_reindex
#print axioms Requirements.prepare_reindex
#print axioms Requirements.results_reindex_type
#print axioms Requirements.build_reindex
#eval IO.println "FUNCTIONAL-REINDEX-OK 64 preparations, two projected contexts, first errors and dependent evidence"
end LeanPoo.Tests.FunctionalReindex
