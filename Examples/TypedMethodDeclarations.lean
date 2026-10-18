import LeanPoo.Functional.MethodDeclarations
import LeanPoo.Functional.FunctionSignature

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

open Functional.FunctionSignature
/-- The companion service schema has optional/rest/keyword Types and a returned
Function. All Type-bearing positions use the existing explicit environment. -/
def reportSchema : TypedSignature String Expr :=
  { outputs := [.var 0, .function [.var 0] [.var 1]]
    inputs := [.var 1]
    optional := [.var 1]
    keywords := [("scale", .ground (.atom .uint))]
    rest := some (.var 1) }
/-- Complete finite inference substitutes the original prefix and residual choice
before producing the descriptor used by declaration construction. -/
def buildReport (choice : Bool) : Except String (TypedSignature String Ty) :=
  .ok (reportSchema.mapTypes (substitute (selectedEnvironment choice)))
/-- The same complete bounded search now returns the richer declared signature. -/
def inferredReport := inferDeclared 2 eligible [true, false] buildReport
-- Check every input category and both outputs, including the nested callback.
#guard match inferredReport with
  | .ok (.unique false, some signature) =>
    signature.inputs.length == 1 && signature.optional.length == 1 &&
    signature.keywords.length == 1 && signature.rest.isSome && signature.outputs.length == 2
  | _ => false
/-- Rich artifacts retain the existing unique-build and original constraint law. -/
theorem inferredReport_valid (accepted : inferredReport = .ok (.unique choice, some signature)) :
    buildReport choice = .ok signature ∧ Subtype (.atom .uint) (selectedType choice) := by
  obtain ⟨_, valid, built⟩ := inferDeclared_unique _ _ _ _ accepted
  exact ⟨built, selected_subtype choice valid⟩
/-- Ground binding cannot alter the host's first structural case selection. -/
example (clauses : List (TypedSignature String Expr)) (choice : Bool) (call : Call String Nat) :
    select ((clauses.map (TypedSignature.mapTypes (substitute (selectedEnvironment choice)))).map
      TypedSignature.shape) call = select (clauses.map TypedSignature.shape) call :=
  specialize_selection _ _ _
/-- Equal structural shapes permit pointwise Function variance over every supplied
position; the numeric example narrows both returned values and broadens all inputs. -/
def reportSource : TypedSignature String Ty :=
  { outputs := [.atom .uint, .atom .uint]
    inputs := [.atom .integer], optional := [.atom .integer]
    keywords := [("scale", .atom .integer)], rest := some (.atom .integer) }
/-- Target has the exact same call language and less precise numeric outputs. -/
def reportTarget : TypedSignature String Ty :=
  { outputs := [.atom .integer, .atom .integer]
    inputs := [.atom .uint], optional := [.atom .uint]
    keywords := [("scale", .atom .uint)], rest := some (.atom .uint) }
#guard replaces 8 reportSource reportTarget
-- Reversing this replacement violates variance rather than widening call syntax.
#guard !(replaces 8 reportTarget reportSource)
/-- Output checks preserve every normalized value; owner is a distinct component. -/
def outputCheck (_type : Nat) (value : Nat) : Except String Nat := .ok (value + 1)
#guard match finishValues [1, 2] [4, 5] (7 : Nat) "arity" outputCheck with
  | .ok ([5, 6], 7) => true
  | _ => false
#guard match finishValues [1, 2] [4] (7 : Nat) "arity" outputCheck with
  | .error "arity" => true
  | _ => false
#guard match finishValues ([] : List Nat) [] (7 : Nat) "arity" outputCheck with
  | .ok ([], 7) => true
  | _ => false
#print axioms TypedSignature.mapTypes_shape
#print axioms TypedSignature.mapTypes_compose
#print axioms specialize_selection
#print axioms replaces_sound
#print axioms finishValues_success
#print axioms finishValues_wrong_count
#print axioms invokeValues_type_error
#print axioms invokeValues_body_error
#print axioms invokeValues_wrong_count
#print axioms inferredReport_valid


/-- The shared catalog keeps the existing report shape, but scale is Self too. -/
def sharedReportSchema : TypedSignature String Expr :=
  { reportSchema with keywords := [("scale", .var 0)] }
/-- One and two supplied Self values choose different recovery output counts. -/
def recoverySchemas : List (TypedSignature String Expr) :=
  [{ outputs := [.var 1], inputs := [.var 0] },
   { outputs := [.var 1, .var 1], inputs := [.var 0, .var 0] }]
/-- Explicit Object field paths select two signatures sharing the SAME environment. -/
def sharedCatalog : List (List String × List (TypedSignature String Expr)) :=
  [([".report"], [sharedReportSchema]), ([".recover"], recoverySchemas)]
/-- Type observations include optional/rest positions, a literal keyword and
expected higher-order/multiple outputs; no manual query supplies Integer <: Super. -/
def sharedCalls : List (List String × Call String Ty × Option (List Ty)) :=
  [([".report"], ⟨[.atom .integer, .atom .integer, .atom .integer], [("scale", .atom .uint)]⟩,
       some [.atom .uint, .function [.atom .uint] [.atom .integer]]),
   ([".recover"], ⟨[.atom .uint, .atom .uint], []⟩, some [.atom .integer, .atom .integer])]
/-- The decoded finite example maps shape refusal to bounds. Parser/unsupported
path failures are separate host checks, whose specific causes are retained. -/
def collectedCalls : Except Functional.PrototypeTypes.Failure (List (Expr × Expr)) :=
  match jointConstraints sharedCatalog sharedCalls with
  | none => .error .bounds
  | some queries => .ok queries
-- Exactly ten supplied input/expected output obligations survive collection.
#guard match collectedCalls with | .ok queries => queries.length == 10 | _ => false
#guard match outputConstraints [.var 0] (some [.atom .uint]) with
  | some [(.var 0, .ground (.atom .uint))] => true
  | _ => false
#guard match jointConstraints sharedCatalog [([".recover"], ⟨[], []⟩, some [])] with
  | none => true
  | _ => false
/-- A successful whole builder specializes parameters and installs/invokes BOTH
certified generics. Returning the pair is later than either local success. -/
def buildShared (choice : Bool) : Except String (Nat × Nat) := do
  let report ← buildSelected choice
  let certified ← (check seed watches).mapError (fun _ => "recovery baseline")
  let recovery : List (Declaration Row (Row → Nat)) :=
    [.replace "recover" [.prototype "Premium", .prototype "Large"] (fun row => row.units + 100)]
  let installed ← (assembleDeclared seed watches certified recovery []).mapError (fun _ => "recovery declaration")
  let called ← (invokeDeclared installed ⟨"Premium", report, 1⟩).mapError (fun _ => "recovery invocation")
  return (report, called.result)
/-- One completed environment supplies all artifact construction; the finite
candidate list has only the two explicitly admitted Super choices. -/
def buildSharedEnvironment (env : Nat → Ty) : Except String (Nat × Nat) :=
  match env 1 with
  | .atom .uint => buildShared true
  | .atom .integer => buildShared false
  | _ => .error "unsupported environment"
/-- Self <: Super is the original bound; all call constraints are extracted. -/
def inferShared := inferDeclaredCalls 8 2 [(.var 0, .var 1)] collectedCalls
  [selectedEnvironment true, selectedEnvironment false] buildSharedEnvironment
#guard match inferShared with
  | .ok (.unique _, some (36, 136)) => true
  | _ => false
/-- Every accepted bound and call-derived inequality holds under the same chosen
assignment used by the actual complete two-generic builder. -/
theorem inferShared_constraints (queries env artifact)
    (collected : collectedCalls = .ok queries)
    (accepted : inferShared = .ok (.unique env, some artifact))
    (query : Expr × Expr) (member : query ∈ [(.var 0, .var 1)] ++ queries) :
    Subtype (substitute env query.1) (substitute env query.2) := by
  unfold inferShared at accepted
  rw [collected] at accepted
  exact inferDeclaredCalls_constraints _ _ _ _ _ _ _ _ accepted query member
-- Extraction refusal and incomplete search cannot expose either local artifact.
#guard match inferDeclaredCalls 8 2 [] (.error .bounds)
    [selectedEnvironment false] buildSharedEnvironment with
  | .error (.inl .bounds) => true
  | _ => false
#guard match inferDeclaredCalls 8 1 [] collectedCalls
    [selectedEnvironment true, selectedEnvironment false] buildSharedEnvironment with
  | .error (.inl .exhausted) => true
  | _ => false
#print axioms inputConstraints_length
#print axioms inputConstraints_shape_error
#print axioms outputConstraints_length
#print axioms callConstraints_first
#print axioms jointConstraints_cons
#print axioms jointConstraints_tail_error
#print axioms inferDeclaredCalls_refused
#print axioms inferDeclaredCalls_provenance
#print axioms inferDeclaredCalls_constraints
#print axioms inferDeclaredCalls_inconsistent
#print axioms inferDeclaredCalls_exhausted
#print axioms inferShared_constraints


/-- Symbolic labels stand for compared normalized syntax; descriptor IDs stand
for exact host identities. The full Type-bearing call schema is modeled above. -/
def catalogRequirements : List (String × String) :=
  [(".report", "report-schema"), (".recover", "recover-schema")]
/-- Each factory stamp retains its field/expression and direct descriptor revision. -/
def catalogOrigins (path : String) : Option (BoundParameter (String × String) Nat) :=
  if path = ".report" then some ⟨(".report", "report-schema"), 11, 3⟩
  else if path = ".recover" then some ⟨(".recover", "recover-schema"), 12, 4⟩ else none
/-- Reflection supplies current descriptor identities at the admitted field paths. -/
def catalogFields (path : String) : Option Nat :=
  if path = ".report" then some 11 else if path = ".recover" then some 12 else none
/-- Direct revision changes are observable independently of descriptor identity. -/
def catalogRevision (descriptor : Nat) : Nat := if descriptor = 11 then 3 else 4
/-- The complete source includes syntax and bound parameter metadata, captured
before any builder. This symbolic frame is not a hash-based admission shortcut. -/
def declaredFrame : String × List String := ("shared-schema", ["Self", "Super"])
/-- The actual two-generic builder's artifact is admitted only after all source
and named signature checks. This is the same order as declaration publication. -/
def buildCheckedShared (env : Nat → Ty) : Except String (Nat × Nat) := do
  let artifact ← buildSharedEnvironment env
  (admitDeclaredInterface declaredFrame declaredFrame catalogRequirements catalogOrigins catalogFields catalogRevision artifact).mapError
      (fun _ => "interface admission")
#guard match inferDeclaredCalls 8 2 [(.var 0, .var 1)] collectedCalls
    [selectedEnvironment true, selectedEnvironment false] buildCheckedShared with
  | .ok (.unique _, some (36, 136)) => true
  | _ => false
-- A valid report cannot hide a missing unobserved recovery sibling.
#guard match admitDeclaredCatalog catalogRequirements
    (fun path => if path = ".recover" then none else catalogOrigins path)
    catalogFields catalogRevision (36, 136) with
  | .error .bounds => true
  | _ => false
-- Pointer equality does not authorize a directly revised Function descriptor.
#guard match admitDeclaredCatalog catalogRequirements catalogOrigins catalogFields (fun _ => 99) (36, 136) with
  | .error .bounds => true
  | _ => false
-- A builder cannot replace the captured parameter/source frame with a subset.
#guard match admitDeclaredInterface declaredFrame ("shared-schema", ["Self"])
    catalogRequirements catalogOrigins catalogFields catalogRevision (36, 136) with
  | .error .bounds => true
  | _ => false
-- A stale group executes nothing; a change after successful work exposes no owner.
#guard match invokeDeclaredSource 3 4 (fun _ => (.error "must not execute" : Except String (Nat × Nat × Nat))) with
  | .error (.inl .bounds) => true
  | _ => false
#guard match invokeDeclaredSource 3 3 (fun _ => (.ok (7, 12, 4) : Except String (Nat × Nat × Nat))) with
  | .error (.inl .bounds) => true
  | _ => false
#guard match invokeDeclaredSource 3 3 (fun _ => (.ok (7, 12, 3) : Except String (Nat × Nat × Nat))) with
  | .ok (7, 12) => true
  | _ => false
#print axioms catalogCurrent_sound
#print axioms admitDeclaredCatalog_sound
#print axioms admitDeclaredSource_stable
#print axioms admitDeclaredInterface_sound
#print axioms invokeDeclaredSource_stale
#print axioms invokeDeclaredSource_error
#print axioms invokeDeclaredSource_changed
#print axioms invokeDeclaredSource_sound

/-- The selected catalog retains named field layout and its own call queries.
This is a finite projection of Object/Row normalization, not a host AST parser. -/
structure CandidateCatalog where
  fields : List (List String × List (TypedSignature String Expr))
  queries : List (Expr × Expr)
/-- Candidate zero has the wrong kind; two lacks a required sibling. Candidate
one supplies both rich signatures after complete parameter substitution. -/
def candidateCatalog (choice : Nat) : Except Functional.PrototypeTypes.Failure CandidateCatalog := do
  if choice = 0 then .error .bounds else
  if choice = 3 then .error .unsupported else
  let fields := if choice = 1 ∨ choice = 4 then sharedCatalog else sharedCatalog.take 1
  let ground := fields.map fun (path, clauses) =>
    (path, clauses.map (TypedSignature.mapTypes (fun expr => .ground (substitute (selectedEnvironment false) expr))))
  match jointConstraints ground sharedCalls with
  | none => .error .bounds
  | some queries => .ok ⟨ground, queries⟩
/-- One assignment owns the entire projected layout and all sibling inequalities.
The existing complete catalog/source admission remains in the final builder. -/
def candidateCatalogValid (_choice : Nat) (catalog : CandidateCatalog) : Bool :=
  satisfies 8 (originalBounds ++ catalog.queries) (selectedEnvironment false)
/-- Reuse the actual two-generic builder; no partial method is published by search. -/
def buildCandidateCatalog (_entry : Nat × CandidateCatalog) : Except String (Nat × Nat) :=
  buildCheckedShared (selectedEnvironment false)
#guard match inferDeclaredCandidates 3 candidateCatalog candidateCatalogValid [0, 1, 2] buildCandidateCatalog with
  | .ok (.unique (1, layout), some (36, 136)) => layout.fields.length == 2 && layout.queries.length == 10
  | _ => false
-- Distinct admitted assignments cannot be hidden by the first successful one.
#guard match inferDeclaredCandidates 2 candidateCatalog candidateCatalogValid [1, 4] buildCandidateCatalog with
  | .ok (.ambiguous [_, _], none) => true
  | _ => false
-- Unsupported syntax AFTER a valid candidate aborts without returning its artifact.
#guard match inferDeclaredCandidates 2 candidateCatalog candidateCatalogValid [1, 3] buildCandidateCatalog with
  | .error (.inl .unsupported) => true
  | _ => false
-- A valid prefix cannot bypass exhaustion, while an empty successful scan is none.
#guard match inferDeclaredCandidates 1 candidateCatalog candidateCatalogValid [1, 2] buildCandidateCatalog with
  | .error (.inl .exhausted) => true
  | _ => false
#guard match inferDeclaredCandidates 2 candidateCatalog candidateCatalogValid [0, 2] buildCandidateCatalog with
  | .ok (.none, none) => true
  | _ => false
/-- All original parameter bounds and candidate-derived sibling constraints have
actual subtype derivations under the same prefixed environment as the builder. -/
theorem candidateCatalog_constraints (entry artifact)
    (published : inferDeclaredCandidates 3 candidateCatalog candidateCatalogValid [0, 1, 2]
      buildCandidateCatalog = .ok (.unique entry, some artifact))
    (query : Expr × Expr) (member : query ∈ originalBounds ++ entry.2.queries) :
    Subtype (substitute (selectedEnvironment false) query.1)
      (substitute (selectedEnvironment false) query.2) := by
  obtain ⟨_, _, checked, _⟩ := inferDeclaredCandidates_sound _ _ _ _ _ _ _ published
  exact satisfies_sound 8 _ _ checked member
#print axioms candidateCatalog_constraints
#print axioms Functional.PrototypeTypes.collectCandidates_sound
#print axioms Functional.PrototypeTypes.collectCandidates_complete
#print axioms inferDeclaredCandidates_sound
#print axioms inferDeclaredCandidates_refused

end LeanPoo.Examples.TypedMethodDeclarations
