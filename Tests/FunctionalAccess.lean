import LeanPoo.Functional.Access

namespace LeanPoo.Tests.FunctionalAccess
open Functional

universe u v w
variable {Context : Type u} {Key : Type v} {Value : Context → Key → Type w}

example [DecidableEq Key] (provider : Provider Context Key Value)
    (left : Requirements.Factories Context Value leftKeys)
    (right : Requirements.Factories Context Value rightKeys)
    (leftReady : Requirements.prepare provider leftKeys = .ok left)
    (rightReady : Requirements.prepare provider rightKeys = .ok right)
    (key : Key) (a : key ∈ leftKeys) (b : key ∈ rightKeys) :
    Requirements.factoryAt (keys := leftKeys) left key a =
      Requirements.factoryAt (keys := rightKeys) right key b :=
  Requirements.factoryAt_stable provider left right leftReady rightReady key a b

example [DecidableEq Key] (order : C4.VerifiedOrder graph root)
    (providers : String → Provider Context Key Value) (keys : List Key)
    (retained : Requirements.Factories Context Value keys)
    (ready : Requirements.prepare (assemble order providers) keys = .ok retained)
    (key : Key) (member : key ∈ keys) :
    ∃ name, C4.Ancestor graph name root ∧
      providers name key = some (Requirements.factoryAt (keys := keys) retained key member) :=
  Requirements.factoryAt_origin order providers keys retained ready key member

example (Claim : Context → Prop) (prove : ∀ context, Claim context) (context : Context) :
    (Factory.fromProof prove context).down = prove context := Factory.fromProof_down prove context

private inductive Capability where
  | background | derivative | residual
  deriving DecidableEq
private structure SampleContext where
  minimum : Nat
private def SampleValue (context : SampleContext) : Capability → Type
  | .background => Nat
  | .derivative => Bool
  | .residual => {n : Nat // context.minimum + 2 ≤ n}

private def provider : Provider SampleContext Capability SampleValue
  | .background => some (fun c => c.minimum + 1)
  | .derivative => some (fun c => c.minimum % 2 == 0)
  | .residual => some (fun c => ⟨c.minimum + 3, by omega⟩)

private abbrev initial : List Capability := [.background, .residual]
private abbrev expanded : List Capability := [.background, .derivative, .residual]
private abbrev reordered : List Capability := [.residual, .background, .derivative]
private abbrev repeated : List Capability := [.residual, .background, .residual]

-- ACCESS-POSITIONAL-BEGIN
private def positionalBefore (retained : Requirements.Factories SampleContext SampleValue initial) :
    Factory SampleContext (fun c => SampleValue c .residual) := retained.2.1
private def positionalAfter (retained : Requirements.Factories SampleContext SampleValue expanded) :
    Factory SampleContext (fun c => SampleValue c .residual) := retained.2.2.1
-- ACCESS-POSITIONAL-END

-- ACCESS-NAMED-BEGIN
private def namedRead {keys : List Capability}
    (retained : Requirements.Factories SampleContext SampleValue keys) (member : .residual ∈ keys) :
    Factory SampleContext (fun c => SampleValue c .residual) :=
  Requirements.factoryAt (keys := keys) retained .residual member
-- ACCESS-NAMED-END

example (_retained : Requirements.Factories SampleContext SampleValue expanded) : True := by
  fail_if_success have _oldPosition : Factory SampleContext (fun c => SampleValue c .residual) := _retained.2.1
  trivial

private def check (keys : List Capability) (member : .residual ∈ keys) : Bool :=
  match Requirements.prepare provider keys with
  | .error _ => false
  | .ok retained => [5, 10].all fun minimum =>
      ((namedRead retained member) ⟨minimum⟩).val == minimum + 3
#guard check initial (by simp [initial])
#guard check expanded (by simp [expanded])
#guard check reordered (by simp [reordered])
#guard check repeated (by simp [repeated])

private def sameProjection : Bool :=
  match Requirements.prepare provider initial, Requirements.prepare provider expanded with
  | .ok a, .ok b =>
    (positionalBefore a ⟨10⟩).val == 13 && (positionalAfter b ⟨10⟩).val == 13
  | _, _ => false
#guard sameProjection

/- Existing analytic theorems may return Prop directly. PLift adapts their
sort while preserving the exact context-indexed proposition and proof. -/
private def claim (context : SampleContext) := context.minimum ≤ context.minimum + 3
private theorem prove (context : SampleContext) : claim context := by unfold claim; omega
private def proofFactory := Factory.fromProof prove
example (context : SampleContext) : claim context := (proofFactory context).down
example (_old : PLift (claim ⟨5⟩)) : True := by
  fail_if_success have _wrongContext : PLift (claim ⟨10⟩) := _old
  trivial

#print axioms Requirements.factoryAt_selected
#print axioms Requirements.factoryAt_stable
#print axioms Requirements.factoryAt_origin
#print axioms Factory.fromProof_down
#eval IO.println "FUNCTIONAL-ACCESS-OK expanded/reordered/repeated keys at two contexts; exact proof adapter"
end LeanPoo.Tests.FunctionalAccess
