import LeanPoo.Functional.SharedViews

namespace LeanPoo.Tests.FunctionalSharedViews
open Functional Requirements
private abbrev Value (_ : Nat) (_ : Nat) := Nat
private abbrev source : List Nat := [0, 1, 2]
private def expected (c : Nat) : Results Value c source := (c, c+3, c+99, PUnit.unit)
private def ready : Certified source (fun c values => values = expected c) :=
  ⟨(fun c => c, fun c => c+3, fun c => c+99, PUnit.unit), fun _ => rfl⟩
private partial def unreachable (c : Nat) : Nat := unreachable c
private def expose (_ : Nat) (key value : Nat) : Nat := if key == 2 then unreachable value else value
private abbrev leftKeys : List Nat := [0]
private abbrev rightKeys : List Nat := [1, 0, 1]
private theorem leftIncluded : ∀ k ∈ leftKeys, k ∈ source := by simp [leftKeys, source]
private theorem rightIncluded : ∀ k ∈ rightKeys, k ∈ source := by simp [rightKeys, source]
private def Left (c : Nat) (values : Results Value c leftKeys) : Prop := values.1 = c
private def Right (c : Nat) (values : Results Value c rightKeys) : Prop :=
  values.1 = c+3 ∧ values.2.1 = c ∧ values.2.2.1 = c+3
private theorem leftProof (c : Nat) (values : Results Value c source) (same : values = expected c) :
    Left c (observeResults expose (projectResults values leftKeys leftIncluded)) := by subst values; rfl
private theorem rightProof (c : Nat) (values : Results Value c source) (same : values = expected c) :
    Right c (observeResults expose (projectResults values rightKeys rightIncluded)) := by
  subst values; exact ⟨rfl, rfl, rfl⟩
private def left (label : String) (c : Nat) (data : Snapshot ready c) : {pair : Nat × String // pair.1 = c} :=
  data.consumeView leftKeys leftIncluded expose Left leftProof
    (fun context values proof => (⟨(values.1, label), proof⟩ : {pair : Nat × String // pair.1 = context}))
private def right (c : Nat) (data : Snapshot ready c) : Nat × Bool :=
  data.consumeView rightKeys rightIncluded expose Right rightProof
    (fun _ values _ => (values.1 + values.2.1 + values.2.2.1, values.1 == values.2.2.1))

#eval do
  let mut reads := 0
  let mut hits := 0
  for trace in [[0,0,1,1,0], [4,5,4,5], [12,12,12], []] do
    let mut slot := ContextSlot.empty ready
    let mut previous : Option Nat := none
    let requests : List (Nat × Nat) := List.zipIdx (show List Nat from trace)
    for request in requests do
      let (context, index) : Nat × Nat := request
      let label := s!"request-{index}"
      let ((first, second), next, hit) := slot.consumePair (left label) right context
      unless first.val == (context, label) && second == (3*context+6, true) &&
          hit == (previous == some context) do throw (IO.userError "fanout value/context/cache control failed")
      let retained := next.read context
      unless retained.2.2 && retained.1.val.2.2.1 == context+99 do
        throw (IO.userError "fanout lost the broad hidden dependencies")
      slot := next
      previous := some context
      reads := reads+1
      if hit then hits := hits+1
  unless reads == 12 && hits == 4 do throw (IO.userError "fanout coverage drift")
  IO.println s!"FUNCTIONAL-SHARED-VIEWS-OK reads={reads} hits={hits} unreachableObservers=24"

example : True := by
  fail_if_success have wrong : Snapshot ready 3 := ((ContextSlot.empty ready).read 0).1
  trivial

#print axioms Snapshot.consumeView_value
#print axioms ContextSlot.consumeSnapshot_state
#print axioms ContextSlot.consumeSnapshot_value
#print axioms ContextSlot.consumePair_state
#print axioms ContextSlot.consumePair_values
end LeanPoo.Tests.FunctionalSharedViews
