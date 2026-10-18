import LeanPoo.Functional.MethodDeclarations

/-! Two-axis declarations, inherited policy edits and negative assumptions share
one existing generic. These finite equations model generalized-prototype future
work; they do not verify Gerbil expansion, runtime Type normalization or GC. -/
namespace LeanPoo.Examples.TypedMethodDeclarations
open Object Functional.DeclarativeMetadata Functional.DispatchExtension
/-- The admitted instance/argument row keeps both dispatch axes and current data. -/
structure Row where
  tier : String
  units : Nat
  rate : Nat
/-- The existing sparse generic combines selected contributions without another index. -/
def seed : Multimethod Row (Row → Nat) Nat :=
  { arity := 2
    precedence := fun row => [[row.tier, "Account"], [if row.units > 10 then "Large" else "Small"]]
    combine := fun methods row => methods.foldl (fun sum body => sum + body row) 0 }
/-- The baseline forbids a separate shape without executing a method. -/
def watches : List (Watch Row) := [.shape [["Blocked"], ["Small"]]]
/-- Shared inherited declaration uses the existing universal second-axis match. -/
def inherited : List (Declaration Row (Row → Nat)) :=
  [.replace "base" [.prototype "Account", .any] (fun row => row.rate * row.units)]
/-- A value-sensitive local declaration rechecks its predicate for each current row. -/
def localMethods : List (Declaration Row (Row → Nat)) :=
  [.guarded "audit" [.prototype "Premium", .prototype "Large"] (fun row => row.units > 20) (fun _ => 7)]
/-- Construct, certify, invoke and keep the complete cache successor in one workflow. -/
def run : Except String (List Nat) := do
  let certified ← (check seed watches).mapError (fun _ => "baseline")
  let revision ← (assembleDeclared seed watches certified localMethods inherited).mapError (fun _ => "declaration")
  let first ← (invokeDeclared revision ⟨"Premium", 12, 3⟩).mapError (fun _ => "first")
  let second ← (first.certificate.invoke ⟨"Premium", 24, 4⟩).mapError (fun _ => "second")
  return [first.result, second.result, second.snapshot.cache.values.size]
/- Same cached shape, new arguments: the earlier false guard cannot be cached. -/
#guard run.toOption == some [36, 103, 1]
/-- Whole-candidate erasure can restore a negative assumption within one batch. -/
def canceled : Except String Bool := do
  let certified ← (check seed watches).mapError (fun _ => "baseline")
  let temporary : List (Declaration Row (Row → Nat)) :=
    [.replace "temporary" [.prototype "Blocked", .prototype "Small"] (fun _ => 99),
     .remove "remove" [.prototype "Blocked", .prototype "Small"]]
  let _ ← (assembleDeclared seed watches certified temporary inherited).mapError (fun _ => "declaration")
  return true
#guard canceled.toOption == some true
/-- Registration errors and negative conflicts remain separate refusal constructors. -/
def refusal (badArity : Bool) : Except String String := do
  let certified ← (check seed watches).mapError (fun _ => "baseline")
  let source : List (Declaration Row (Row → Nat)) :=
    [.replace "forbidden" (if badArity then [] else [.prototype "Blocked", .prototype "Small"]) (fun _ => 99)]
  match assembleDeclared seed watches certified source inherited with
  | .ok _ => return "unexpected"
  | .error (.registration _ _) => return "registration"
  | .error (.introduced _ _ _) => return "negative"
#guard [ (refusal true).toOption, (refusal false).toOption ] == [some "registration", some "negative"]
#print axioms assembleDeclared_ok_iff
#print axioms assembleDeclared_coalesce
#print axioms assembleDeclared_cacheSound
#print axioms invokeDeclared_absent
#print axioms declaredPublication_refused
end LeanPoo.Examples.TypedMethodDeclarations
