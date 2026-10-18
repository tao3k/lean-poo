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

/-! Prefix specialization and bounded inference use the same declaration builder.
Function-row carrier admission remains the premise of the finite dispatcher. -/
namespace LeanPoo.Examples.TypedMethodDeclarations
open Functional.PrototypeTypes Functional.DeclarativeMetadata Functional.DispatchExtension
open Functional.Parameters Object

/-- The first parameter is fixed UInt; the remaining finite choice is Super. -/
def selectedType (choice : Bool) : Ty := if choice then .atom .uint else .atom .integer
/-- The original inequalities include Self <: Super and the Integer call query. -/
def originalBounds : List (Expr × Expr) :=
  [(.var 0, .var 1), (.ground (.atom .integer), .var 1)]
/-- Prefix and residual environments use the same admitted type vocabulary. -/
def selectedEnvironment (choice : Bool) : Nat → Ty :=
  prefixEnvironment [.atom .uint] (fun _ => selectedType choice)
/-- The finite checker tests ORIGINAL bounds after prefix/residual substitution. -/
def eligible (choice : Bool) := satisfies 8 originalBounds (selectedEnvironment choice)
/-- Parameter metadata is validated by the existing positional protocol. -/
def typeParameters : Template String Ty := ⟨["Self", "Super"], fun _ => none⟩
/-- Bind the ground prefix, then the inferred suffix, then install and invoke the
existing certified generic. Every failure prevents a returned artifact. -/
def buildSelected (choice : Bool) : Except String Nat := do
  let staged ← (checkedSpecialize ".parameters" typeParameters [.atom .uint]).mapError (fun _ => "prefix")
  let answer ← (specializeDeclared ".parameters" staged [selectedType choice] (fun bound => do
    if !bound.remaining.isEmpty then throw "residual parameters"
    let certified ← (check seed watches).mapError (fun _ => "baseline")
    let revision ← (assembleDeclared seed watches certified localMethods inherited).mapError (fun _ => "declaration")
    let called ← (invokeDeclared revision ⟨"Premium", 12, 3⟩).mapError (fun _ => "invoke")
    return called.result)).mapError (fun _ => "specialize/declaration")
  return answer
/-- A complete finite search chooses Super=Integer before building the declaration. -/
def inferredService := inferDeclared 2 eligible [true, false] buildSelected
-- The executable control includes real positional binding, installation and call.
#guard match inferredService with
  | .ok (.unique false, some 36) => true
  | _ => false
/-- Returned declarations have both the exact chosen assignment and successful build. -/
theorem inferredService_valid (accepted : inferredService = .ok (.unique choice, some answer)) :
    choice ∈ [true, false] ∧ eligible choice = true ∧ buildSelected choice = .ok answer :=
  inferDeclared_unique _ _ _ _ accepted
/-- Any accepted residual assignment proves the original Self/Super bound. -/
theorem selected_subtype (choice : Bool) (accepted : eligible choice = true) :
    Subtype (.atom .uint) (selectedType choice) := by
  have sound := satisfies_sound 8 originalBounds (selectedEnvironment choice) accepted
    (a := .var 0) (b := .var 1) (by simp [originalBounds])
  simpa [substitute, selectedEnvironment, prefixEnvironment] using sound
/-- Unfinished enumeration has a search-phase refusal and no declaration artifact. -/
example : inferDeclared 1 eligible [true, false] buildSelected = .error (.inl .exhausted) :=
  inferDeclared_exhausted _ _ _ _ (by decide)
-- A nonunique universe never calls a deliberately refusing declaration builder.
#guard match inferDeclared 2 (fun _ : Bool => true) [true, false]
    (fun _ => (.error "must skip" : Except String Nat)) with
  | .ok (.ambiguous _, none) => true
  | _ => false
#print axioms prefixEnvironment_fixed
#print axioms prefixEnvironment_tail
#print axioms inferred_prefix_constraints
#print axioms inferDeclared_unique
#print axioms inferDeclared_ambiguous
#print axioms inferDeclared_none
#print axioms inferDeclared_exhausted
#print axioms inferDeclared_build_error
#print axioms specializeDeclared_invalid
#print axioms specializeDeclared_remaining
/-- The same descriptor identity can still become stale through a direct revision. -/
def boundTypes : List (BoundParameter String Nat) := [⟨"Self", 1, 4⟩, ⟨"Super", 2, 7⟩]
/-- A completed typed receiver exposes exactly the admitted descriptor identities. -/
def boundFields (name : String) : Option Nat := if name = "Self" then some 1 else some 2
-- Equality of descriptor IDs alone cannot approve a changed definition.
#guard match admitDeclaredBindings boundTypes boundFields (fun id => if id = 1 then 4 else 7) (36 : Nat) with
  | .ok 36 => true
  | _ => false
#guard match admitDeclaredBindings boundTypes boundFields (fun id => if id = 1 then 5 else 7) (36 : Nat) with
  | .error .bounds => true
  | _ => false
#print axioms bindingsCurrent_sound
#print axioms bindingsCurrent_refuses
#print axioms admitDeclaredBindings_stable
end LeanPoo.Examples.TypedMethodDeclarations
