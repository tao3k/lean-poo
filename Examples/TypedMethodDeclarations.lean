import LeanPoo.Functional.MethodDeclarations
import LeanPoo.Functional.OptionalValidation
import LeanPoo.Functional.RawArguments
import LeanPoo.Functional.ClassValidation

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
/-- A guarded full catalog retains source order and hidden groups. The successor
state may carry newly forced caches; the final admitter still reads that state. -/
def heldCatalog : List (String × Nat) := [(".report", 7), (".recover", 8), ("hidden-audit", 9)]
/-- Success/error equality is universal over both callbacks, rather than a test
of a particular successful declaration. Stability must follow from the host guard. -/
example (force : List (String × Nat) → Except String Nat)
    (reflect : Nat → List (String × Nat))
    (admit : Nat → List (String × Nat) → Except String Nat)
    (stable : ∀ state, force heldCatalog = .ok state → reflect state = heldCatalog) :
    admitReflected heldCatalog force admit = admitReflectedAgain heldCatalog force reflect admit :=
  admitReflected_eq _ _ _ _ stable
/-- Refusal during typed forcing cannot run the final catalog admission. -/
example : admitReflected heldCatalog (fun _ => (.error "metadata-edit" : Except String Nat))
    (fun _ _ => (.error "must-not-run" : Except String Nat)) = .error "metadata-edit" := by rfl
#print axioms admitReflected_eq
#print axioms admitReflected_refuses
#print axioms reflected_catalog_work
/-- Root and named interfaces still run the exact source check before using
captured normalization, with arbitrary admission/refusal semantics afterwards. -/
example (captured observed : String × List String)
    (project : (String × List String) → List (String × Nat))
    (admit : List (String × Nat) → Except Functional.PrototypeTypes.Failure Nat) :
    (admitDeclaredSource captured observed ()).bind (fun _ => admit (project captured)) =
    (admitDeclaredSource captured observed ()).bind (fun _ => admit (project observed)) :=
  admitDeclaredSource_project _ _ _ _
#print axioms admitDeclaredSource_project
#print axioms declared_catalog_work

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

/-- A callback's finite schema preserves the already fixed Value parameter;
source choice true uses one broad rest clause rather than two fixed clauses. -/
def coveredCallbackSchema (wide : Bool) : List (TypedSignature String Expr) :=
  if wide then [{ outputs := [.var 0], inputs := [.ground (.atom .integer)], rest := some (.ground (.atom .integer)) }]
  else [{ outputs := [.var 0], inputs := [.var 0] }]
/-- Reuse the original prefix environment and complete Type substitution. -/
def coveredCallback (wide : Bool) : List (TypedSignature String Ty) :=
  (coveredCallbackSchema wide).map (TypedSignature.mapTypes (substitute (selectedEnvironment false)))
/-- Both one- and two-argument caller regions require exact UInt results. -/
def requiredCallback : List (TypedSignature String Ty) :=
  [{ outputs := [.atom .uint], inputs := [.atom .uint] },
   { outputs := [.atom .uint], inputs := [.atom .uint, .atom .uint] }]
/-- The builder retains the selected callback metadata beside the existing
complete two-generic artifact. Type search itself cannot execute this builder. -/
def buildCoveredCallback (wide : Bool) : Except String (List (TypedSignature String Ty) × (Nat × Nat)) := do
  let artifact ← buildCheckedShared (selectedEnvironment false)
  return (coveredCallback wide, artifact)
/-- Complete inference chooses coverage under the same prefix used in publication. -/
def inferredCoverage := inferDeclared 2
  (fun wide => replacesLanguage 8 (coveredCallback wide) requiredCallback)
  [false, true] buildCoveredCallback
#guard match inferredCoverage with
  | .ok (.unique true, some (catalog, (36, 136))) => catalog.length == 1
  | _ => false
-- Every caller row is covered by a selected descriptor with all variance laws.
-- This is universal, not a claim derived from testing arities one and two.
theorem inferredCoverage_sound (wide artifact)
    (published : inferredCoverage = .ok (.unique wide, some artifact))
    (count keys expected) (selected : selectTyped requiredCallback (shapeRow count keys) = some expected) :
    ∃ actual, selectTyped (coveredCallback wide) (shapeRow count keys) = some actual ∧
      RelList Subtype actual.outputs expected.outputs ∧
      (∀ index < count, inputSubtype (expected.inputAt index) (actual.inputAt index)) ∧
      (∀ key ∈ keys, inputSubtype (Functional.RowTypes.lookup expected.keywords key)
        (Functional.RowTypes.lookup actual.keywords key)) := by
  obtain ⟨_, valid, _⟩ := inferDeclared_unique _ _ _ _ published
  exact replacesLanguage_sound 8 _ _ valid count keys expected selected
/-- Infinite target tail regions still have finite exact coverage certificates. -/
def unboundedCallback : List (TypedSignature String Ty) :=
  [{ outputs := [.atom .integer], inputs := [.atom .uint] },
   { outputs := [.atom .integer], inputs := [.atom .uint, .atom .uint], rest := some (.atom .uint) }]
#guard replacesLanguage 8 (coveredCallback true) unboundedCallback
#guard !replacesLanguage 8 (coveredCallback false) unboundedCallback
-- A shadowed later compatible clause cannot repair an earlier output mismatch.
#guard !replacesLanguage 8
  ({ outputs := [.atom .bool], inputs := [.atom .integer], rest := some (.atom .integer) } :: coveredCallback true)
  unboundedCallback
/-- Keyword presence selects different first clauses, including an optional key. -/
def keywordCover : List (TypedSignature String Ty) :=
  [{ outputs := [.atom .uint], inputs := [.atom .integer],
      keywords := [("mode", .atom .integer)], requiredKeywords := ["mode"] },
   { outputs := [.atom .uint], inputs := [.atom .integer],
      keywords := [("mode", .atom .integer), ("extra", .atom .bool)] }]
/-- The target permits mode omission; its supplied key Type is narrower. -/
def keywordRequired : List (TypedSignature String Ty) :=
  [{ outputs := [.atom .integer], inputs := [.atom .uint], keywords := [("mode", .atom .uint)] }]
#guard replacesLanguage 8 keywordCover keywordRequired
#guard !replacesLanguage 8 (keywordCover.take 1) keywordRequired
-- Budget refusal precedes artifact construction even if a visited choice is valid.
#guard match inferDeclared 1 (fun wide => replacesLanguage 8 (coveredCallback wide) requiredCallback)
    [true, false] buildCoveredCallback with
  | .error (.inl .exhausted) => true
  | _ => false
#print axioms accepts_shapeRow
#print axioms select_representative
#print axioms coversCalls_sound
#print axioms coversCalls_complete
#print axioms inputAt_representative
#print axioms coversTypedCalls_sound
#print axioms replacesLanguage_sound
#print axioms inferredCoverage_sound

/-- The specialized UInt callback accepts ordinary UInt positions and an omitted
scale keyword. The inherited prefix substitution is unchanged. -/
def keywordCallback (requiredKey : Bool) : List (TypedSignature String Ty) :=
  [{ outputs := [.atom .uint], inputs := [.atom .integer], keywords := [("scale", .atom .uint)],
     requiredKeywords := if requiredKey then ["scale"] else [] }]
/-- A plain caller's scalar fields exclude outer keyword/escape tokens. -/
def positionalCallback : List (TypedSignature String Ty) :=
  [{ outputs := [.atom .integer], inputs := [.atom .uint] }]
/-- Unique inference selects a keyword callback that does not demand a new key,
then enters the existing complete two-generic declaration builder. -/
def inferredKeywordCallback := inferDeclared 2
  (fun requiredKey => replacesPositionalTarget 8 (keywordCallback requiredKey) positionalCallback)
  [true, false] (fun requiredKey => do
    let artifact ← buildCheckedShared (selectedEnvironment false)
    return (keywordCallback requiredKey, artifact))
#guard match inferredKeywordCallback with
  | .ok (.unique false, some (_, (36, 136))) => true
  | _ => false
-- Exposed Any/Union tokens are unsafe; container payloads do not change carriers.
#guard !keywordStable 8 .top
#guard !keywordStable 8 (.union [.atom .uint, .top])
#guard keywordStable 8 (.pair .top .top)
#guard keywordStable 8 (.union [.atom .uint, .atom .bool])
#guard !replacesPositionalTarget 8 (keywordCallback false)
  [{ outputs := [.atom .integer], inputs := [.top] }]
/-- Raw transport candidates differ by one mandatory original argument. Both
have Any rest, but only one covers target calls omitting the optional keyword. -/
def rawCallback (tooMany : Bool) : List (TypedSignature String Ty) :=
  [{ outputs := [.atom .uint], inputs := if tooMany then [.top, .top] else [.top], rest := some .top }]
/-- Keyword target positions/keys are decoded before first-clause selection. -/
def scaledCallback : List (TypedSignature String Ty) :=
  [{ outputs := [.atom .integer], inputs := [.atom .uint], keywords := [("scale", .atom .uint)] }]
/-- The same finite inference/declaration admission uses raw-minimum coverage. -/
def inferredRawCallback := inferDeclared 2
  (fun tooMany => replacesKeywordTarget 8 (rawCallback tooMany) scaledCallback)
  [true, false] (fun tooMany => do
    let artifact ← buildCheckedShared (selectedEnvironment false)
    return (rawCallback tooMany, artifact))
#guard match inferredRawCallback with
  | .ok (.unique false, some (_, (36, 136))) => true
  | _ => false
/-- A published raw callback covers every raw spelling, without a target wrapper
which would otherwise mask cross-mode differences. -/
theorem inferredRawCallback_sound (tooMany artifact)
    (published : inferredRawCallback = .ok (.unique tooMany, some artifact))
    (tokens : List (ArgumentToken String Int)) (row)
    (decoded : decodeKeyword tokens = some row) (expected)
    (selected : selectTyped scaledCallback
      (shapeRow row.positional.length (row.keywords.map Prod.fst)) = some expected) :
    selectTyped (rawCallback tooMany) (Call.mk tokens []) = (rawCallback tooMany).head? ∧
    RelList Subtype (.atom .uint :: []) expected.outputs := by
  obtain ⟨_, valid, _⟩ := inferDeclared_unique _ _ _ _ published
  obtain ⟨actual, found, outputs, _⟩ := replacesKeywordTarget_sound 8 (rawCallback tooMany) scaledCallback
    valid tokens row decoded expected selected
  have member := selectTyped_member (rawCallback tooMany) (Call.mk tokens []) actual found
  simp only [rawCallback, List.mem_singleton] at member
  subst actual
  exact ⟨found, outputs⟩
/-- Escaped positional keyword values and literal key markers remain exact data. -/
def escapedRow : List (ArgumentToken String Int) :=
  [.keyEscape, .keyword "scale", .restEscape, .keyword "scale", .keyEscape]
#guard decodeKeyword escapedRow == some ⟨[.keyword "scale", .keyword "scale", .keyEscape], []⟩
#guard decodeKeyword ([.keyword "scale", .value 2, .keyword "scale", .value 3] : List (ArgumentToken String Int)) == none
#guard decodeKeyword ([.keyEscape] : List (ArgumentToken String Int)) == none
-- Canonical encoders may add #!rest; actual empty callers need no raw tokens.
#guard !replacesKeywordTarget 8 (rawCallback false)
  [{ outputs := [.atom .integer], inputs := [], keywords := [("scale", .atom .uint)] }]
#guard !replacesKeywordTarget 8
  [{ outputs := [.atom .uint], inputs := [], rest := some (.atom .uint) }] scaledCallback
-- The empty first case does not shadow nonempty raw rows; the later case is valid.
#guard replacesKeywordTarget 8
  ({ outputs := [.atom .uint], inputs := [] } :: rawCallback false) scaledCallback
-- A same-arity first case with an incompatible Type still cannot fall through.
#guard !replacesKeywordTarget 8
  ({ outputs := [.atom .uint], inputs := [.atom .bool] } :: rawCallback false) scaledCallback
#guard !replacesKeywordTarget 8 [{ outputs := [], inputs := [], rest := some .top }] scaledCallback
#print axioms rawCounts_complete
#print axioms decode_maximum
#print axioms decode_direct
#print axioms decode_minimum
#print axioms replacesKeywordTarget_sound
#print axioms replacesPositionalTarget_stable
#print axioms replacesPositionalTarget_sound
#print axioms inferredRawCallback_sound

/-- Callback schema reuses the existing Value prefix: one typed fixed case and
one optional raw case, with no unbounded Any rest in either descriptor. -/
def prefixCallbackSchema (badResult : Bool) : List (TypedSignature String Expr) :=
  [{ outputs := [if badResult then .ground (.atom .bool) else .var 0], inputs := [.var 0] },
   { outputs := [.var 0], inputs := [.ground .top, .ground .top],
     optional := [.ground .top, .ground .top, .ground .top] }]
/-- Complete original prefix substitution precedes the shared coverage judgment. -/
def prefixCallback (badResult : Bool) : List (TypedSignature String Ty) :=
  (prefixCallbackSchema badResult).map (TypedSignature.mapTypes (substitute (selectedEnvironment false)))
/-- Unique inference rejects the bad first result, then invokes the existing
whole two-generic builder under the same original environment. -/
def inferredPrefixCallback := inferDeclared 2
  (fun badResult => replacesKeywordTarget 8 (prefixCallback badResult) scaledCallback)
  [true, false] (fun badResult => do
    let artifact ← buildCheckedShared (selectedEnvironment false)
    return (prefixCallback badResult, artifact))
#guard match inferredPrefixCallback with
  | .ok (.unique false, some (catalog, (36, 136))) => catalog.length == 2
  | _ => false
/-- Every raw spelling accepted by the target uses its actual first source case,
with direct input variance or Any at all supplied raw positions. -/
theorem inferredPrefixCallback_sound (badResult artifact)
    (published : inferredPrefixCallback = .ok (.unique badResult, some artifact))
    (tokens : List (ArgumentToken String Int)) (row)
    (decoded : decodeKeyword tokens = some row) (expected)
    (selected : selectTyped scaledCallback
      (shapeRow row.positional.length (row.keywords.map Prod.fst)) = some expected) :
    ∃ actual, selectTyped (prefixCallback badResult) (Call.mk tokens []) = some actual ∧
      RelList Subtype actual.outputs expected.outputs ∧
      ((row.keywords = [] ∧ row.positional = tokens ∧
        ∀ index < tokens.length, inputSubtype (expected.inputAt index) (actual.inputAt index)) ∨
       (∀ index < tokens.length, actual.inputAt index = some .top)) := by
  obtain ⟨_, valid, _⟩ := inferDeclared_unique _ _ _ _ published
  exact replacesKeywordTarget_sound 8 _ _ valid tokens row decoded expected selected
-- Unused optional Types do not become supplied obligations.
#guard replacesKeywordTarget 8
  [{ outputs := [.atom .uint], inputs := [], optional := [.top, .top, .top, .top, .top, .atom .bool] }] scaledCallback
#guard !replacesKeywordTarget 8
  [{ outputs := [.atom .uint], inputs := [], optional := [.top, .atom .bool, .top, .top, .top] }] scaledCallback
-- Five raw tokens are possible: key/value, escaped positional, trailing rest.
#guard decodeKeyword ([.keyword "scale", .value 2, .keyEscape, .value 7, .restEscape] : List (ArgumentToken String Int)) ==
  some ⟨[.value 7], [("scale", .value 2)]⟩
#guard !replacesKeywordTarget 8
  [{ outputs := [.atom .uint], inputs := [.top], optional := [.top, .top, .top] }] scaledCallback
-- Several fixed cases can jointly cover all raw lengths, in their original order.
#guard replacesKeywordTarget 8
  ([1, 2, 3, 4, 5].map (fun count =>
    ({ outputs := [.atom .uint], inputs := List.replicate count .top } : TypedSignature String Ty))) scaledCallback
-- Source raw length two occurs in two target decoded regions; results must meet both.
#guard !replacesKeywordTarget 8 [{ outputs := [.atom .uint], inputs := [], rest := some .top }]
  [{ outputs := [.atom .uint], inputs := [.atom .uint], keywords := [("scale", .atom .uint)] },
   { outputs := [.atom .bool], inputs := [.atom .uint, .atom .uint], keywords := [("scale", .atom .uint)] }]
-- The representative tail must check protocol tokens, not assume a direct row.
#guard !replacesKeywordTarget 8
  [{ outputs := [.atom .uint], inputs := [.atom .uint], rest := some (.atom .uint) }]
  [{ outputs := [.atom .integer], inputs := [.atom .uint], rest := some (.atom .uint),
     keywords := [("scale", .atom .uint)] }]
#print axioms replacesKeywordTarget_modes
#print axioms rawAnyPositions_sound
#print axioms replacesKeywordTarget_cell
#print axioms inferredPrefixCallback_sound

/-- The five-token endpoint's two payload slots remain Integer. Marker slots
reuse finite Enum/Exactly membership; changing a payload to Bool refuses. -/
def valueEndpoint (badPayload : Bool) : Nat → ArgumentToken String Ty → Bool
  | 0, .keyword "scale" | 0, .keyEscape | 2, .keyword "scale" | 2, .keyEscape => true
  | 1, .value ty => check 8 ty (if badPayload then .atom .bool else
      substitute (selectedEnvironment false) (.var 1))
  | 3, .value ty => check 8 ty (.atom .integer)
  | 4, .restEscape => true
  | _, _ => false
/-- First-selected length-one and length-five cases precede the optional 2..4
case. Its flat numeric/finite-marker Union validates without changing values. -/
def valueRawAdmission (badPayload : Bool) (size index : Nat) (origin : ArgumentToken String Ty) : Bool :=
  if size = 1 then match index, origin with
    | 0, .value ty => check 8 ty (.atom .uint)
    | _, _ => false
  else if size = 5 then valueEndpoint badPayload index origin
  else match origin with
    | .value ty => check 8 ty (.atom .integer)
    | .keyword key => decide (key = "scale")
    | .keyEscape | .restEscape => true
/-- All lengths and supplied-key masks of the bounded callback are checked,
including each non-minimum raw row, not just a chosen canonical encoding. -/
def valueCoverage (badPayload : Bool) : Bool :=
  ([[], [("scale", Ty.atom .uint)]] : List (List (String × Ty))).all (fun keys =>
    (List.range 6).all (fun size => rawCovers (valueRawAdmission badPayload size) 3
      [.atom .uint] keys 0 size))
/-- The admitted callback reuses the original specialized two-generic builder;
no artifact is constructed until complete unique finite inference succeeds. -/
def inferredValueCallback := inferDeclared 2 valueCoverage [true, false]
  (fun badPayload => do
    let artifact ← buildCheckedShared (selectedEnvironment false)
    return (badPayload, artifact))
#guard valueCoverage false
#guard !valueCoverage true
#guard match inferredValueCallback with
  | .ok (.unique false, some (false, (36, 136))) => true
  | _ => false
-- Escapes cannot be replaced by Keyword alone, and Enum cannot invent a label.
#guard !keywordMarker (ArgumentToken.keyEscape : ArgumentToken String Ty)
#guard !enumMarker [.keyword "scale", .keyEscape] (.keyword "other")
#guard enumMarker [.restEscape] (ArgumentToken.restEscape : ArgumentToken String Unit)
-- Actual ordered shape dispatch selects the precise five-token endpoint.
#guard select ([{ required := 1 }, { required := 5 }, { required := 2, optional := 2 }] : List (Signature String))
  (shapeRow 5 []) == some { required := 5 }
-- A bounded admission budget never turns an unfinished traversal into success.
#guard !rawCovers (valueRawAdmission false 5) 0 [.atom .uint] [("scale", .atom .uint)] 0 5
#guard match inferDeclared 1 valueCoverage [true, false] (fun _ => (Except.ok () : Except String Unit)) with
  | .error (.inl .exhausted) => true
  | _ => false
/-- Publication carries the origin-specific law for every successful spelling in
this entire bounded language. The trace is the explicit decoder-origin premise;
rawCovers_sound is independent of these particular examples and payload Types. -/
theorem inferredValueCallback_sound (badPayload artifact)
    (published : inferredValueCallback = .ok (.unique badPayload, some artifact))
    (keys : List (String × Ty)) (inside : keys ∈ [[], [("scale", .atom .uint)]])
    (tokens : List (ArgumentToken String Ty)) (bound : tokens.length < 6)
    (trace : RawSpelling [.atom .uint] keys tokens) :
    rawSlots (valueRawAdmission badPayload tokens.length) 0 tokens = true := by
  obtain ⟨_, valid, _⟩ := inferDeclared_unique 2 valueCoverage [true, false] _ published
  have region := List.all_eq_true.mp (List.all_eq_true.mp valid keys inside) tokens.length
    (List.mem_range.mpr bound)
  exact rawCovers_sound _ 3 trace region
/-- The integer payload inclusion used by the endpoint is semantic derivability,
not the mere fact that some sample callback accepted a number. -/
theorem valueEndpoint_payload (ty : Ty)
    (accepted : valueEndpoint false 1 (.value ty) = true) : Subtype ty (.atom .integer) := by
  simp only [valueEndpoint, substitute, selectedEnvironment, prefixEnvironment, selectedType] at accepted
  simp at accepted
  exact check_sound 8 ty (.atom .integer) accepted
#print axioms rawCovers_sound
#print axioms rawSlots_sound
#print axioms stationaryRaw_sound
#print axioms inferredValueCallback_sound
#print axioms valueEndpoint_payload

/-- A finite quotient keeps the raw prefix separate from the repeated tail.
Origins carry their raw slot, so a Boolean key payload never weakens slot zero. -/
def restOriginAdmission (badTail : Bool) (_state : Nat) (indexed : Nat × ArgumentToken String Ty) : Bool :=
  match indexed with
  | (index, .value ty) => check 8 ty (.atom .integer) ||
      (decide (0 < index) && !badTail && check 8 ty (.atom .bool))
  | (_, .keyword key) => decide (key = "enabled")
  | (_, .keyEscape) | (_, .restEscape) => true
/-- This abstract graph overapproximates successful target traces. Tail loops
retain indexed payloads and escapes; endings, not visited cycles, seed closure. -/
def correlatedGraph : List (RawTransition Nat (Nat × ArgumentToken String Ty)) :=
  [⟨0, 1, [(0, .value (.atom .uint))]⟩,
   ⟨0, 1, [(0, .keyword "enabled"), (1, .value (.atom .bool))]⟩,
   ⟨0, 1, [(0, .keyEscape), (1, .value (.atom .uint))]⟩,
   ⟨0, 1, [(0, .restEscape), (1, .value (.atom .uint))]⟩,
   ⟨1, 1, [(1, .value (.atom .uint))]⟩,
   ⟨1, 1, [(1, .keyword "enabled"), (1, .value (.atom .bool))]⟩,
   ⟨1, 2, [(1, .restEscape)]⟩]
/-- Shared complete inference precedes the existing specialized declaration build. -/
def inferredCorrelatedCallback := inferDeclared 2
  (fun badTail => rawGraphCheck 2 correlatedGraph [2] 0 true (restOriginAdmission badTail))
  [true, false] (fun badTail => do
    let artifact ← buildCheckedShared (selectedEnvironment false)
    return (badTail, artifact))
#guard rawGraphCheck 2 correlatedGraph [2] 0 true (restOriginAdmission false)
#guard !rawGraphCheck 2 correlatedGraph [2] 0 true (restOriginAdmission true)
-- A provisional set containing just the ending is not a closed certificate.
#guard !rawGraphCheck 0 correlatedGraph [2] 0 true (restOriginAdmission false)
#guard !rawGraphCheck 2 correlatedGraph [2] 0 false (restOriginAdmission false)
-- Moving Bool into the first slot cannot borrow its permitted tail evidence.
#guard !rawGraphCheck 2 (⟨0, 1, [(0, .value (.atom .bool))]⟩ :: correlatedGraph)
  [2] 0 true (restOriginAdmission false)
#guard match inferredCorrelatedCallback with
  | .ok (.unique false, some (false, (36, 136))) => true
  | _ => false
-- Literal removal is exact: only the numeric Enum arm is ordinary data.
#guard ordinaryLiterals ([.keyword "other", .keyEscape, .restEscape, .value (7 : Int)] :
  List (ArgumentToken String Int)) == [.value 7]
-- A long physical tail still has a raw cell beyond the shortest decoded row.
#guard rawCounter 13 12 ∈ rawTailCounts 13 2 0
/-- Every accepting graph trace of a published callback, of arbitrary length,
retains indexed origin admission. Actual decoder/product construction completeness
and host validator interpretation remain explicit correspondence premises. -/
theorem inferredCorrelatedCallback_sound (badTail artifact)
    (published : inferredCorrelatedCallback = .ok (.unique badTail, some artifact))
    (trace : List (RawTransition Nat (Nat × ArgumentToken String Ty)))
    (path : RawGraphPath correlatedGraph 0 2 trace) :
    trace.all (fun edge => edge.origins.all (restOriginAdmission badTail edge.source)) = true := by
  obtain ⟨_, valid, _⟩ := inferDeclared_unique 2 _ [true, false] _ published
  exact (rawGraphCheck_sound 2 correlatedGraph [2] 0 true (restOriginAdmission badTail)
    valid path (by simp)).2
#print axioms ordinaryLiterals_mem
#print axioms protocol_singleton_not_data
#print axioms rawCounter_product
#print axioms rawTailCounts_complete
#print axioms inputAt_rawCounter
#print axioms rawGraphCheck_sound
#print axioms rawGraph_empty
#print axioms inferredCorrelatedCallback_sound

/-- Same inherited service fields as the Scheme factory. Self is prefix-bound
UInt, while the finite choice determines Super in the nested callback input. -/
def recordReadLayout (choice : Bool) :
    Functional.ClassValidation.RecordType String Ty :=
  ⟨[("run", ⟨.function [.atom .uint] [selectedType choice], false⟩),
    ("limit", ⟨.atom .uint, false⟩), ("bias", ⟨.atom .uint, false⟩),
    ("extra", ⟨.function [.atom .uint] [selectedType choice], true⟩)], false⟩
/-- The public read view reorders fields and hides internal limits/optional hooks. -/
def recordReadView : Functional.ClassValidation.RecordType String Ty :=
  ⟨[("bias", ⟨.atom .integer, true⟩),
    ("run", ⟨.function [.atom .uint] [.atom .integer], false⟩)], false⟩
/-- One complete shared search precedes the original specialization/declaration builder. -/
def inferredRecordView := inferDeclared 2
  (fun choice => Functional.ClassValidation.recordCheck (Functional.PrototypeTypes.check 8) (fun _ => false)
    (recordReadLayout choice) recordReadView) [true, false] buildSelected
#guard match inferredRecordView with
  | .ok (.unique false, some 36) => true
  | _ => false
-- A missing optional field is safe only when no hidden source value can exist.
#guard Functional.ClassValidation.recordCheck (Functional.PrototypeTypes.check 8) (fun _ => false)
  (⟨[], true⟩ : Functional.ClassValidation.RecordType String Ty)
  ⟨[("missing", ⟨.atom .bool, true⟩)], true⟩
#guard !(Functional.ClassValidation.recordCheck (Functional.PrototypeTypes.check 8) (fun _ => false)
  (⟨[], false⟩ : Functional.ClassValidation.RecordType String Ty)
  ⟨[("missing", ⟨.atom .bool, true⟩)], false⟩)
-- Optional source metadata cannot satisfy a required target, even with equal Types.
#guard !(Functional.ClassValidation.recordCheck (Functional.PrototypeTypes.check 8) (fun _ => false)
  (⟨[("n", ⟨.atom .uint, true⟩)], true⟩ : Functional.ClassValidation.RecordType String Ty)
  ⟨[("n", ⟨.atom .uint, false⟩)], false⟩)
/-- Publication implies every source observation admits the reordered read view,
conditional on the existing scalar/container/Function interpretation laws. This
says nothing about validator effect order, mutation or Gerbil code generation. -/
theorem inferredRecordView_sound (choice artifact)
    (published : inferredRecordView = .ok (.unique choice, some artifact))
    (model : Interpretation Value) (observe : String → Option Value)
    (valid : Functional.RowTypes.RecordAdmits model.accepts (recordReadLayout choice) observe) :
    Functional.RowTypes.RecordAdmits model.accepts recordReadView observe := by
  obtain ⟨_, accepted, _⟩ := inferDeclared_unique 2 _ [true, false] _ published
  exact Functional.RowTypes.recordCheck_sound (Functional.PrototypeTypes.check 8) (fun _ => false) model.accepts
    (fun a b checked => Functional.PrototypeTypes.replacement model (check_sound 8 a b checked))
    (by intro field impossible; contradiction)
    _ _ accepted observe valid
#print axioms Functional.RowTypes.recordCheck_sound
#print axioms Functional.RowTypes.recordFieldCheck_missing
#print axioms Functional.RowTypes.inferred_record_sound
#print axioms inferredRecordView_sound

/-- Same callback metadata as the Scheme alias service after Value=UInt is bound.
Only the order of option bindings differs; required keys remain an empty payload. -/
def callbackOptions : List (SignatureOption String Atom) :=
  [.optional [.uint], .keywords [("scale", .uint)], .rest (some .uint)]
/-- Explicit empty metadata and reordered bindings describe one effective schema. -/
def callbackAliasOptions : List (SignatureOption String Atom) :=
  [.rest (some .uint), .requiredKeywords [], .keywords [("scale", .uint)], .optional [.uint]]
/-- Canonical fields retain the original callback language and one result Type. -/
def callbackOptionSchema := projectSignatureOptions [.uint] [.uint] callbackOptions
/-- Finite candidates deduplicate effective signatures before original inference. -/
def callbackOptionCandidates :=
  [callbackOptionSchema, projectSignatureOptions [.uint] [.uint] callbackAliasOptions].eraseDups
/-- The existing prefix/residual declaration builder receives one complete schema. -/
def inferredOptionService := inferDeclared 1 (fun _ => true) callbackOptionCandidates
  (fun signature => do
    let artifact ← buildSelected false
    return (signature, artifact))
#guard match inferredOptionService with
  | .ok (.unique _, some (_, 36)) => true
  | _ => false
#guard accepts callbackOptionSchema.shape (⟨[2, 3, 4, 5], [("scale", 2)]⟩ : Call String Nat)
#guard readSignatureOptions [.uint] [.uint] ([.optional [], .optional [.uint]] : List (SignatureOption String Atom)) == none
/-- Omitted/default metadata normalize equally, but optional UInt is not omitted. -/
example : normalizeSignatureOptions [.uint] [.uint] ([] : List (SignatureOption String Atom)) =
    normalizeSignatureOptions [.uint] [.uint] [.rest none, .requiredKeywords [], .keywords [], .optional []] := rfl
/-- Prefix binding of actual Type expressions commutes with the shared metadata
projection. The existing substitution owns variance and bound validation. -/
example (options : List (SignatureOption String Expr)) (outputs inputs : List Expr) :
    projectSignatureOptions (outputs.map (substitute (selectedEnvironment false)))
      (inputs.map (substitute (selectedEnvironment false)))
      (options.map (mapSignatureOption (substitute (selectedEnvironment false)))) =
    (projectSignatureOptions outputs inputs options).mapTypes (substitute (selectedEnvironment false)) :=
  projectSignatureOptions_map _ _ _ _
/-- Publication certifies one actual canonical candidate and the complete original
builder result. Equal metadata is not permission to reuse a revised host owner. -/
theorem inferredOptionService_signature (signature published artifact)
    (success : inferredOptionService = .ok (.unique signature, some (published, artifact))) :
    signature = callbackOptionSchema ∧ published = signature ∧ buildSelected false = .ok artifact := by
  obtain ⟨member, _, built⟩ := inferDeclared_unique 1 _ callbackOptionCandidates _ success
  have singleton : callbackOptionCandidates = [callbackOptionSchema] := by decide
  rw [singleton] at member
  have chosen := List.mem_singleton.mp member
  refine ⟨chosen, ?_⟩
  cases called : buildSelected false with
  | error cause =>
    rw [called] at built
    change Except.error cause = Except.ok (published, artifact) at built
    contradiction
  | ok value =>
    rw [called] at built
    change Except.ok (signature, value) = Except.ok (published, artifact) at built
    have same := Except.ok.inj built
    cases same
    exact ⟨rfl, rfl⟩
#print axioms readSignatureOptions_perm
#print axioms normalizeSignatureOptions_sound
#print axioms normalizeSignatureOptions_idempotent
#print axioms projectSignatureOptions_map
#print axioms infer_signature_aliases
#print axioms inferredOptionService_signature

/-- The Scheme route fixes invariant Key and Self before searching the Super
candidate. Finite candidates never introduce an unconstrained fallback Type. -/
def optionalRouteEnvironment (choice : Bool) : Nat → Ty :=
  prefixEnvironment [.atom .uint, .atom .uint] (fun _ => selectedType choice)
/-- The same child Function occurs in Map entries and in the Maybe/OrFalse
fallback. Sentinel kinds remain distinct under ordinary Type substitution. -/
def optionalRouteExpression : Expr :=
  let callback := Expr.function [.var 1] [.var 2]
  let routes := Expr.map (.var 0) (.orFalse callback)
  .function [.pair routes (.maybe (.orFalse callback))] [routes]
/-- The observed callable interface has UInt outputs and Integer inputs throughout. -/
def optionalRouteExpected : Ty :=
  let callback := Ty.function [.atom .uint] [.atom .integer]
  let routes := Ty.map (.atom .uint) (.orFalse callback)
  .function [.pair routes (.maybe (.orFalse callback))] [routes]
/-- Original Self <: Super and the complete caller interface are checked together;
Function input contravariance and Map key invariance use the existing checker. -/
def optionalRouteEligible (choice : Bool) : Bool :=
  satisfies 12 [(.var 1, .var 2)] (optionalRouteEnvironment choice) &&
    check 12 (substitute (optionalRouteEnvironment choice) optionalRouteExpression) optionalRouteExpected
/-- Only a complete unique solution enters the original specialization/declaration
builder. The complete callback artifact remains separate from inferred Type data. -/
def inferredOptionalRoute := inferDeclared 2 optionalRouteEligible [true, false] buildSelected
#guard optionalRouteEligible false
#guard !optionalRouteEligible true
#guard match inferredOptionalRoute with
  | .ok (.unique false, some 36) => true
  | _ => false
#guard !keywordStable 8 (.orFalse .top)
#guard keywordStable 8 (.orFalse (.atom .uint))
#guard !(check 8 (.maybe (.atom .uint)) (.orFalse (.atom .integer)))
#guard !(check 8 (.map (.orFalse (.atom .uint)) (.atom .uint))
  (.map (.orFalse (.atom .integer)) (.atom .integer)))
/-- Optional substitution retains its constructor; no void/false interchange or
collapse of nested sentinels can change a candidate's runtime domain. -/
example (env : Nat → Ty) (body : Expr) :
    substitute env (.maybe (.orFalse body)) = .maybe (.orFalse (substitute env body)) := by
  simp [substitute]
/-- Published routes carry a real replacement derivation and the original complete
builder result. No claim about Gambit execution follows from this finite checker. -/
theorem inferredOptionalRoute_sound (choice artifact)
    (published : inferredOptionalRoute = .ok (.unique choice, some artifact)) :
    Subtype (substitute (optionalRouteEnvironment choice) optionalRouteExpression) optionalRouteExpected ∧
      buildSelected choice = .ok artifact := by
  obtain ⟨_, eligible, built⟩ := inferDeclared_unique 2 optionalRouteEligible [true, false] buildSelected published
  have both : satisfies 12 [(.var 1, .var 2)] (optionalRouteEnvironment choice) = true ∧
      check 12 (substitute (optionalRouteEnvironment choice) optionalRouteExpression) optionalRouteExpected = true :=
    by simpa only [optionalRouteEligible, Bool.and_eq_true] using eligible
  have related := both.2
  exact ⟨check_sound _ _ _ related, built⟩
/-- The original interpretation must provide sentinel/Function behavior. Under
those premises, a published optional route preserves all admitted observations. -/
theorem inferredOptionalRoute_preserves (choice artifact) (model : Interpretation Value)
    (published : inferredOptionalRoute = .ok (.unique choice, some artifact))
    (value : Value) (valid : model.accepts
      (substitute (optionalRouteEnvironment choice) optionalRouteExpression) value) :
    model.accepts optionalRouteExpected value :=
  Functional.PrototypeTypes.replacement model (inferredOptionalRoute_sound choice artifact published).1 value valid
#print axioms inferredOptionalRoute_sound
#print axioms inferredOptionalRoute_preserves
#print axioms Functional.OptionalValidation.replacement
#print axioms Functional.OptionalValidation.normalized_member

end LeanPoo.Examples.TypedMethodDeclarations
