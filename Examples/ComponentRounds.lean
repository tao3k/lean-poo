import Examples.Support.ComponentRounds

/-! Executable controls use the shared finite component workflow fixture. -/
namespace LeanPoo.Examples.ComponentRounds
open Functional.GeneralizedGraph Functional.StrongComponents
/-- Six actual rounds exercise shared migration, repeated endpoint recreation,
interleaved SCC merge/split, erased providers and stale snapshot rejection. -/
def check : Except String Unit := do
  let .ok r1 := SupportRevision.joinAt (0 : Nat) 0 source (contributions .merge) | throw "merge refused"
  let .ok r2 := SupportRevision.joinAt (1 : Nat) 1 r1.apply (contributions .replace) | throw "split refused"
  let .ok r3 := SupportRevision.joinAt (2 : Nat) 2 r2.apply (contributions .restore) | throw "restore refused"
  let some g1 := discoverSupported r1.keys (fun key dep => decide (dep ∈ r1.apply.reads key)) | throw "merged graph refused"
  let some g2 := discoverSupported r2.keys (fun key dep => decide (dep ∈ r2.apply.reads key)) | throw "replaced graph refused"
  let some g3 := discoverSupported r3.keys (fun key dep => decide (dep ∈ r3.apply.reads key)) | throw "restored graph refused"
  unless (g1.members 2).length == 7 && (g2.members 2).map Fin.val == [2,3,7] &&
      (g2.members 5).map Fin.val == [5,8] && (g3.members 2).map Fin.val == [2,3,4] &&
      (g3.members 5).map Fin.val == [5,6] do throw "interleaved groups mismatch"
  unless (List.finRange 12).map (g2.dirty (supportRevisionSeed g1 g2 (fun _ => false))) ==
      [false,false,true,true,false,true,false,true,true,true,true,false] do throw "split invalidation mismatch"
  unless (List.finRange 12).map (g3.dirty (supportRevisionSeed g2 g3 (fun _ => false))) ==
      [false,false,true,true,true,true,true,false,false,true,true,false] do throw "restore invalidation mismatch"
  let old ← execute source
  let merged ← execute r1.apply
  let replaced ← execute r2.apply
  let restored ← execute r3.apply
  unless old.get 10 == 12 && merged.get 10 == 24 && replaced.get 10 == 16 && restored == old do
    throw "actual round closure mismatch"
  unless refused (SupportRevision.joinAt (0 : Nat) 3 r3.apply (contributions .merge)) do
    throw "old staged request accepted after support/value round trip"
  let .ok r4 := SupportRevision.joinAt (3 : Nat) 3 r3.apply
    (contributions .merge [⟨1,some (.ok 5)⟩]) | throw "second merge refused"
  let .ok r5 := SupportRevision.joinAt (4 : Nat) 4 r4.apply (contributions .replace) | throw "second split refused"
  let .ok r6 := SupportRevision.joinAt (5 : Nat) 5 r5.apply
    (contributions .restore [⟨0,some (.ok 2)⟩]) | throw "second restore refused"
  let next ← execute r4.apply
  let split ← execute r5.apply
  let final ← execute r6.apply
  unless next.get 10 == 30 && split.get 10 == 20 && final.get 10 == 8 && final.get 2 == 2 do
    throw "repeated migration closure mismatch"
  unless (r6.apply.code 7).isNone && (r6.apply.base 7).isNone &&
      (r6.apply.code 8).isNone && (r6.apply.base 8).isNone do throw "removed providers reappeared"
#eval match check with
  | .ok () => IO.println "COMPONENT-ROUNDS-OK"
  | .error message => throw (IO.userError message)
#print axioms SupportRevision.joinAt_stale
#print axioms SupportRevision.joinAt_accepted
#print axioms SupportRevision.join_erased
#print axioms Functional.ComponentExecution.resolved_correct
#print axioms Functional.ComponentExecution.focus_laws
end LeanPoo.Examples.ComponentRounds
