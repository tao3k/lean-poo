import LeanPoo.Functional.ComputationBatch
import LeanPoo.Functional.AnalyzedCache

namespace LeanPoo.Tests.FunctionalComputationBatch
open Functional
private inductive Key where
  | amount | forbidden
  deriving BEq, DecidableEq, Repr
private abbrev Value (_ : Nat) (_ : Key) := Nat
private def provider (present : Bool) : Provider Nat Key Value
  | .amount => if present then some (fun context => context+1) else none
  | .forbidden => none
private def step (offset : Nat) : Computation Nat Key Value (fun c => {n : Nat // n ≤ c+4}) :=
  .validate (.need .amount (fun _ n => n)) fun context n =>
    if valid : n+offset ≤ context+4 then .ok ⟨n+offset, valid⟩ else .error s!"offset {offset}"
private def batch (offsets : List Nat) := Computation.traverse offsets step
private def normalize {context : Nat} :
    Except (ComputationError Key) (List {n : Nat // n ≤ context+4}) → Except (ComputationError Key) (List Nat)
  | .ok values => .ok (values.map Subtype.val)
  | .error error => .error error
private def equal : Except (ComputationError Key) (List Nat) → Except (ComputationError Key) (List Nat) → Bool
  | .ok a, .ok b => a == b
  | .error a, .error b => a == b
  | _, _ => false

#eval do
  let mut cases := 0
  for present in [false, true] do
    for context in List.range 6 do
      for offsets in [[], [0], [3, 1, 3], [4, 7, 0], [1, 5], [7, 2]] do
        let code := batch offsets
        let expected : Except (ComputationError Key) (List Nat) := if offsets.isEmpty then Except.ok []
          else if !present then .error (.missing Key.amount)
          else match offsets.find? (fun n => 3 < n) with
            | some first => .error (.source s!"offset {first}")
            | none => .ok (offsets.map (context+1+·))
        unless equal (normalize (code.evaluate (provider present) context)) expected do
          throw (IO.userError "batch validation disagrees with independent control")
        unless code.analyze.required == offsets.map (fun _ => Key.amount) &&
            code.analyze.values == offsets.map (fun _ => Key.amount) && !code.analyze.unknown do
          throw (IO.userError "validation lost full conservative footprint")
        let cache := Computation.Cache.empty code (provider present) (fun _ _ => True) (by
          intro c; cases code.evaluate (provider present) c <;> trivial)
        let (_, warm, cold) := cache.read context
        let (hot, _, reused) := warm.read context
        unless !cold && reused && equal (normalize hot.val) expected do
          throw (IO.userError "cached validation changed a success/error observation")
        cases := cases+1
  IO.println s!"FUNCTIONAL-COMPUTATION-BATCH-OK cases={cases} cachedSuccessAndErrors={cases}"

private partial def unreachable (_ : Nat) : Nat := unreachable 0
private def stopped : Computation Nat Key Value (fun _ => List Nat) :=
  Computation.sequence [.validate (.pure (fun _ => 0)) (fun _ _ => .error "stop"),
    .pure unreachable]
#eval do
  match stopped.evaluate (provider true) 0 with
  | .error (.source "stop") => pure ()
  | _ => throw (IO.userError "validation applied unreachable batch suffix")

#print axioms Computation.sequence_evaluate
#print axioms Computation.sequence_analyze
#print axioms Computation.sequence_error_iff
#print axioms Computation.validate_child_error
#print axioms Computation.validate_rejected
#print axioms Computation.evaluate_congr
#print axioms Computation.evaluate_capabilitySafe
end LeanPoo.Tests.FunctionalComputationBatch
