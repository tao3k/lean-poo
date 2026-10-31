import Examples.Support.ComponentRounds

/-! Competing requests reuse the shared actual-source component workflow fixture. -/
namespace LeanPoo.Examples.ComponentRounds
open Functional.GeneralizedGraph Functional.StrongComponents
/-- Competing staged requests reuse actual component sources/closure while the
serialized publication rule selects which fully approved candidate may install.
Snapshot labels are local fixtures; runtime freshness is a separate premise. -/
def requestsCheck : Except String Unit := do
  let .ok first := SupportRevision.joinAt (0 : Nat) 0 source (contributions .merge) |
    throw "first staged request refused"
  let .ok second := SupportRevision.joinAt (0 : Nat) 0 source
    (contributions .merge [⟨1,some (.ok 5)⟩]) | throw "second staged request refused"
  let firstRaw ← execute first.apply
  let secondRaw ← execute second.apply
  unless firstRaw.get 10 == 24 && secondRaw.get 10 == 30 do throw "candidate construction mismatch"
  let winner := Functional.ComponentPublication.install (0 : Nat) 0 2 (approved second.apply true true 30 secondRaw)
  let late := Functional.ComponentPublication.install (0 : Nat) winner.head 1
    (approved first.apply true true 30 firstRaw)
  unless winner.accepted && winner.head == 2 && !late.accepted && late.head == winner.head do
    throw "late candidate overwrote accepted rival"
  let denied := Functional.ComponentPublication.install (0 : Nat) 0 1
    (approved first.apply true false 30 firstRaw)
  unless !denied.accepted && denied.head == 0 do throw "joint refusal advanced publication"
  let retry := Functional.ComponentPublication.install (0 : Nat) denied.head 1
    (approved first.apply true true 30 firstRaw)
  unless retry.accepted && retry.head == 1 do throw "fresh current-policy retry failed"
  unless refused (SupportRevision.joinAt (0 : Nat) winner.head second.apply (contributions .merge)) do
    throw "stale staging accepted after rival"
  let .ok split := SupportRevision.joinAt (2 : Nat) winner.head second.apply (contributions .replace) |
    throw "retry on current topology refused"
  let splitRaw ← execute split.apply
  unless splitRaw.get 10 == 20 do throw "current topology retry closure mismatch"
  let installed := Functional.ComponentPublication.install (2 : Nat) winner.head 3
    (approved split.apply true true 30 splitRaw)
  unless installed.accepted && installed.head == 3 do throw "current topology retry not installed"
#eval match requestsCheck with
  | .ok () => IO.println "COMPONENT-REQUESTS-OK"
  | .error message => throw (IO.userError message)
#print axioms Functional.ComponentPublication.stale
#print axioms Functional.ComponentPublication.refused
#print axioms Functional.ComponentPublication.accepted
#print axioms Functional.ComponentPublication.competing
#print axioms Functional.ComponentPublication.retry
end LeanPoo.Examples.ComponentRounds
