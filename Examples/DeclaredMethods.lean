import LeanPoo.Functional.MethodDeclarations
import LeanPoo.Functional.NonlocalDeclarations
import LeanPoo.Functional.FunctionSignature

/-! Matching pure declaration-to-generic controls. Native macro expansion, actual
C3 sharing and descriptor mutation are exercised separately in Gerbil. -/
namespace LeanPoo.Examples.DeclaredMethods
open Object.MethodCombination
open Functional.DeclarativeMetadata
open Functional.FunctionSignature
/-- The complete receiver carries current data and invocation arguments together. -/
abbrev Row := Nat × Nat
/-- Logged execution observes qualifier order without assuming effect rollback. -/
abbrev Run := StateT (List String) (Except String)
/-- Add one event to the invocation trace before continuing. -/
def record (name : String) : Run Unit := modify (· ++ [name])
/-- The common base primary uses the actual instance and its current arguments. -/
def base : List (Fragment String Row Run Nat) :=
  [.slot "label" "shared", .method ".charge" [.primary (fun _ row => do
    record "base"; return row.1 * row.2)]]
/-- Separate declaration forms contribute to the same slot in source order. -/
def billing : List (Fragment String Row Run Nat) :=
  [.method ".charge" [.before (fun _ => record "billing-before")],
   .method ".charge" [.primary (fun next _ => do record "billing-primary"; return 3 + (← next ()))],
   .method ".charge" [.after (fun _ => record "billing-after")],
   .method ".charge" [.around (fun next _ => do
     record "around-enter"; let result ← next (); record "around-exit"; return 2 * result)]]
/-- The other branch adds side methods; shared ancestors occur once in C3 input. -/
def risk : List (Fragment String Row Run Nat) :=
  [.method ".charge" [.before (fun _ => record "risk-before")],
   .method ".charge" [.after (fun _ => record "risk-after")]]
/-- Ordinary slot specifications collect the already resolved ancestor stream. -/
def methods : Methods Row Run Nat :=
  ((fragmentSpecification ".charge" (billing ++ risk ++ base)).eval () (fun _ => none)).getD {}
/-- A type-selected generic keeps the complete original receiver for every method. -/
def charge (row : Row) : Run Nat := declaredGeneric (fun _ => ()) (fun _ => some methods) {}
  (fun _ => throw "no primary method") row
/-- Interleaved record/method declarations preserve the standard qualifier order. -/
example : (charge (10,2)).run [] = .ok (46,
    ["around-enter","billing-before","risk-before","billing-primary","base",
     "risk-after","billing-after","around-exit"]) := rfl
/-- A second receiver uses current data; no previous method result is reused. -/
example : ((charge (20,2)).run []).map Prod.fst = .ok 86 := rfl
/-- Around short-circuiting suppresses the complete remaining combined workflow. -/
example : (effective ({methods with around := [fun _ _ => pure 7]})
    (fun _ => throw "no primary method") (10,2)).run [] = .ok (7,[]) := rfl
/-- A source failure stops primary successors and after methods. -/
example : (effective ({methods with around := [], primary := [fun _ _ => (throw "refused" : Run Nat)]})
    (fun _ => throw "no primary method") (10,2)).run [] = .error "refused" := rfl
/-- Missing-slot defaults provide raw groups, while an absent primary still refuses. -/
example : (declaredGeneric (fun (_ : Row) => ()) (fun _ => none) ({} : Methods Row Run Nat)
    (fun _ => throw "no primary method") (10,2)).run [] = .error "no primary method" := rfl
/-- Whole-form expansion contributes a new qualifier group above the shared C3
stream. The supplied owner order is a premise, as for the earlier family example. -/
def batchMethods (surcharge : Nat) (approved : Bool) : Except String (Methods Row Run Nat) := do
  let forms : List (Unit → Except String (List (Fragment String Row Run Nat))) :=
    [fun _ => .ok [.method ".charge" [
      .before (fun _ => record "batch-before"),
      .primary (fun next _ => do record "batch-primary"; return surcharge + (← next ())),
      .after (fun _ => record "batch-after")]],
     fun _ => .ok billing, fun _ => .ok risk, fun _ => .ok base]
  let fragments ← collectForms forms ()
  if !approved then throw "batch approval refused"
  return ((fragmentSpecification ".charge" fragments).eval () (fun _ => none)).getD {}
/-- Only complete approved declarations select a combined method invocation. -/
def batchCharge (surcharge : Nat) (approved : Bool) (row : Row) : Run Nat :=
  match batchMethods surcharge approved with
  | .error message => throw message
  | .ok selected => effective selected (fun _ => throw "no primary method") row
/-- The expanded group preserves before/primary/reversed-after and around order. -/
example : (batchCharge 5 true (10,2)).run [] = .ok (56,
    ["around-enter","batch-before","billing-before","risk-before","batch-primary",
     "billing-primary","base","risk-after","billing-after","batch-after","around-exit"]) := rfl
/-- Current approval refuses the whole family; retry uses the new captured surcharge. -/
example : [((batchCharge 5 false (10,2)).run []).map Prod.fst,
    ((batchCharge 7 true (20,2)).run []).map Prod.fst] =
    [.error "batch approval refused", .ok 100] := rfl
#print axioms collectForms_cons
#print axioms collectForms_finalize
#print axioms collectFragments_append
#print axioms collectFragments_coalesce
#print axioms fragmentSpecification_append
#print axioms declaredGeneric_standard
#print axioms declaredGeneric_fragments
/-- A keyword-valued positional argument is data, distinct from a declared key.
This finite fixture projects a receiver to its current rate; opaque host receiver
identity and core predicate/default execution remain Gerbil obligations. -/
abbrev CallValue := Sum String (Option Nat)
/-- Current reflection precedes the core-checked generic in the FUN workflow.
Given those admissions, forward the resolved dependent default and exact rest row
into summary, then bind its success to the existing standard combined charge. -/
def forwardedSummary (rate : Nat) (suppliedUnits : Option Nat) (visible : Bool) :
    Run (Nat × Call String CallValue) := do
  unless visible do throw "slot is hidden or undeclared"
  let units ← match suppliedUnits with
    | none => throw "argument contract refused"
    | some units => pure units
  let resolved : Call String CallValue :=
    ⟨[.inr (some units), .inr (some units)], [("label", .inr none)]⟩
  let frame := forwardResolved [.inr (some rate)] resolved [.inl "payload", .inr none]
  record "summary"
  let amount ← effective methods (fun _ => throw "no primary method") (rate, units)
  pure (amount, frame)
/-- The complete row retains false and keyword data while the shared base runs once. -/
example : (forwardedSummary 10 (some 2) true).run [] = .ok ((46,
    ⟨[.inr (some 10), .inr (some 2), .inr (some 2), .inl "payload", .inr none],
      [("label", .inr none)]⟩),
    ["summary", "around-enter", "billing-before", "risk-before", "billing-primary", "base",
      "risk-after", "billing-after", "around-exit"]) := rfl
/-- Combined refusal keeps metadata priority; restored current metadata permits retry. -/
example : [((forwardedSummary 10 none false).run []).map (fun value => value.1.1),
    ((forwardedSummary 10 none true).run []).map (fun value => value.1.1),
    ((forwardedSummary 20 (some 2) true).run []).map (fun value => value.1.1)] =
    [.error "slot is hidden or undeclared", .error "argument contract refused", .ok 86] := rfl
/-- A present false is not an absent table entry; source order selects the output. -/
example : restoreKeywords ["label", "mode"]
    (fun key => if key = "label" then some false else some true) =
    some [("label", false), ("mode", true)] := rfl
example : restoreKeywords ["mode", "label"]
    (fun key => if key = "label" then some false else some true) =
    some [("mode", true), ("label", false)] := rfl
#print axioms restoreKeywords_nil
#print axioms restoreKeywords_cons
#print axioms restoreKeywords_missing
#print axioms restoreKeywords_source
#print axioms forwardResolved_keywords
#print axioms forwardResolved_positional
#print axioms forwardResolved_length
#print axioms forwardResolved_compose
/-- One Reader invocation carries fresh data and approval into the same family. -/
abbrev SummaryContext := Nat × Bool
/-- Present false is a tag value; a missing tag declaration is represented outside
this result, by the supplied metadata lookup's outer Option. -/
abbrev TaggedSummary := Option String × (Nat × Call String CallValue)
/-- The existing logged interpreter is the carrier of each prototype layer. -/
abbrev SummaryAction := SummaryContext → Run TaggedSummary
/-- Homogeneous Reader extensions reuse the existing first-class Proto carrier. -/
abbrev SummaryPrototype := Prototype.Proto Unit SummaryAction SummaryAction
/-- Current approval precedes the inherited Reader action. -/
def approvalPrototype : SummaryPrototype :=
  fun _ inherited context => do
      unless context.2 do throw "current approval refused"
      record "approval"
      inherited context
/-- Supplied current policy changes the context before any generic invocation. -/
def offsetPrototype (offset : Option Nat) : SummaryPrototype :=
  fun _ inherited context => do
      record "offset"
      let amount ← match offset with
        | none => throw "slot is hidden or undeclared"
        | some amount => pure amount
      inherited (context.1 + amount, context.2)
/-- Observation follows successful completion of the inherited action. -/
def observationPrototype : SummaryPrototype :=
  fun _ inherited context => do
      let result ← inherited context
      record "observed"
      pure result
/-- Tag lookup follows method effects; present false differs from missing metadata. -/
def tagPrototype (tag : Option (Option String)) : SummaryPrototype :=
  fun _ inherited context => do
      let result ← inherited context
      record "tag"
      let value ← match tag with
        | none => throw "slot is hidden or undeclared"
        | some value => pure value
      pure (value, result.2)
/-- Four ordinary extensions build the same Reader chain as Gerbil. Current
metadata is supplied; host mutation/capture and prior refusal effects are tested there. -/
def summaryPrototypeLayers (offset : Option Nat) (tag : Option (Option String)) :
    List SummaryPrototype :=
  [approvalPrototype, offsetPrototype offset, observationPrototype, tagPrototype tag]
/-- Standard reduction assembles the existing typed forwarding workflow without
using the unsafe unrestricted fixed point. No body runs during pure assembly. -/
def prototypeSummary (offset : Option Nat) (tag : Option (Option String))
    (units : Option Nat) (visible : Bool) : SummaryAction :=
  Prototype.composeReduced (summaryPrototypeLayers offset tag) () (fun context => do
    let result ← forwardedSummary context.1 units visible
    pure (none, result))
/-- Prototype layers retain the complete generic frame and qualified-method order. -/
example : (prototypeSummary (some 1) (some none) (some 2) true (10, true)).run [] =
    .ok ((none, (50, ⟨[.inr (some 11), .inr (some 2), .inr (some 2),
      .inl "payload", .inr none], [("label", .inr none)]⟩)),
      ["approval", "offset", "summary", "around-enter", "billing-before", "risk-before",
       "billing-primary", "base", "risk-after", "billing-after", "around-exit", "tag", "observed"]) := rfl
/-- Fresh policy/context input drives retry through the same prototype program. -/
example : ((prototypeSummary (some 3) (some none) (some 2) true (20, true)).run []).map
    (fun result => result.1.2.1) = .ok 98 := rfl
/-- Approval, policy lookup, method visibility and post-result tag refusal remain
distinct boundary failures. This Except carrier does not assert rollback of effects. -/
example : [
    ((prototypeSummary (some 1) (some none) (some 2) true (10, false)).run []).map (fun _ => ()),
    ((prototypeSummary none (some none) (some 2) true (10, true)).run []).map (fun _ => ()),
    ((prototypeSummary (some 1) (some none) (some 2) false (10, true)).run []).map (fun _ => ()),
    ((prototypeSummary (some 1) none (some 2) true (10, true)).run []).map (fun _ => ())] =
    [.error "current approval refused", .error "slot is hidden or undeclared",
     .error "slot is hidden or undeclared", .error "slot is hidden or undeclared"] := rfl
#print axioms Prototype.composeReduced_eq
#print axioms Prototype.composeReduced_append
#print axioms Prototype.compose_captured_suffix
#print axioms Prototype.composeReduced_apply_cons
/-- Current combiner selection, raw lookup and procedure admission precede the
same Reader/forwarding/C3 body. These Boolean admissions model supplied outcomes;
Gerbil separately checks actual public metadata and procedure identity. -/
def configuredSummary (selected lookupValid admitted : Bool) (context : SummaryContext) :
    Run (Nat × Call String CallValue) :=
  combineDirect
    (do
      record "select-combiner"
      unless selected do throw "combiner lookup refused"
      pure (fun (_ : Unit) (current : SummaryContext) =>
        forwardedSummary current.1 (some 2) current.2))
    (do record "lookup-fragments"; unless lookupValid do throw "fragment lookup refused"; pure ())
    (fun _ => do record "admit-combiner"; unless admitted do throw "combiner is not a procedure") context
/-- Direct transport retains both results, complete row and exact qualified trace. -/
example : (configuredSummary true true true (10, true)).run [] = .ok ((46,
    ⟨[.inr (some 10), .inr (some 2), .inr (some 2), .inl "payload", .inr none],
     [("label", .inr none)]⟩),
    ["select-combiner", "lookup-fragments", "admit-combiner", "summary",
     "around-enter", "billing-before", "risk-before", "billing-primary", "base",
     "risk-after", "billing-after", "around-exit"]) := rfl
/-- Each boundary retains its own refusal; none falls through to another method. -/
example : [((configuredSummary false false false (10,true)).run []).map (fun _ => ()),
    ((configuredSummary true false false (10,true)).run []).map (fun _ => ()),
    ((configuredSummary true true false (10,true)).run []).map (fun _ => ()),
    ((configuredSummary true true true (10,false)).run []).map (fun _ => ())] =
    [.error "combiner lookup refused", .error "fragment lookup refused",
     .error "combiner is not a procedure", .error "slot is hidden or undeclared"] := rfl
/-- A repaired current admission uses fresh data through the same direct workflow. -/
example : ((configuredSummary true true true (20,true)).run []).map (fun result => result.1.1) =
    .ok 86 := rfl
/-- Illustrative source-operation prices preserve row cost and remove relay cost.
These numbers are not measured Gerbil bytes or execution times. -/
example : (capturedWork 7).charge 1 3 2 = (directWork 7).charge 1 3 2 + 5 := rfl
#print axioms combineDirect_eq
#print axioms combineDirect_lookup_error
#print axioms combination_charge_difference
#print axioms combination_charge_le
/-- Replay transport composes with current admission and the complete qualified
workflow; the callback can observe every false/keyword payload in its own row.
The pure carrier does not model mutation or Gerbil procedure identity. -/
def transportedSummary (fixed rest : List CallValue) (context : SummaryContext) :
    Run (Nat × List CallValue) :=
  combineDirect
    (pure (fun (_ : Unit) row => do
      let result ← configuredSummary true true true context
      pure (result.1, row)))
    (pure ()) (fun _ => pure ()) (assembleRow fixed rest)

/-- Receiver identity is projected to its current rate; the structured message
is projected to one opaque token. Each retry reads fresh context, while the
caller-owned message remains one value, rather than being parsed as keywords. -/
example : [
    ((transportedSummary [.inl "label", .inr none, .inl "rest", .inr (some 10), .inr (some 2), .inr (some 2)]
      [.inl "payload:false"] (10, true)).run []).map Prod.fst,
    ((transportedSummary [.inl "label", .inr none, .inl "rest", .inr (some 20), .inr (some 2), .inr (some 2)]
      [.inl "payload:false"] (20, true)).run []).map Prod.fst] =
    [.ok (46, [.inl "label", .inr none, .inl "rest", .inr (some 10), .inr (some 2), .inr (some 2), .inl "payload:false"]),
     .ok (86, [.inl "label", .inr none, .inl "rest", .inr (some 20), .inr (some 2), .inr (some 2), .inl "payload:false"])] := rfl

/-- Row assembly cannot turn a hidden current method into an accepted request. -/
example : ((transportedSummary [] [.inr none] (10, false)).run []) =
    .error "slot is hidden or undeclared" := rfl
/-- Illustrative budget: a cheaper transport can still lose to additional GC
or construction. These supplied units are not measured execution times. -/
example : rowAssemblyCharge 7 1 8 2 false < rowAssemblyCharge 7 1 8 2 true ∧
    ¬ (100 + rowAssemblyCharge 7 1 8 2 false + 20 ≤
       100 + rowAssemblyCharge 7 1 8 2 true + 0) ∧
    ¬ (120 + rowAssemblyCharge 7 1 8 2 false + 0 ≤
       100 + rowAssemblyCharge 7 1 8 2 true + 0) := by decide
/-- Fused Reader completion uses current admission, then the same complete
summary/charge program and a post-success review. Review may itself run another
request; the receiver and result of the outer request remain lexically local. -/
def reviewedSummary (rate : Nat) (visible : Bool) (review : Nat → Run Unit) :
    Run (Nat × Call String CallValue) :=
  fusedObservation
    (fun current => if visible then pure current else throw "slot is hidden or undeclared")
    (fun current => do
      let result ← forwardedSummary current (some 2) true
      review result.1
      pure result) rate

/-- A bounded nested review models a forecast at another rate. This is two
ordinary requests, without general recursion or a termination assumption. -/
def forecastReview (amount : Nat) : Run Unit := do
  record "review"
  if amount = 46 then
    let _ ← reviewedSummary 20 true (fun _ => record "nested-review")
    pure ()

/-- Nested completion keeps the outer result and both full qualifier traces. -/
example : ((reviewedSummary 10 true forecastReview).run []).map (fun result =>
    (result.1.1, result.2)) = .ok (46,
    ["summary", "around-enter", "billing-before", "risk-before", "billing-primary", "base",
     "risk-after", "billing-after", "around-exit", "review",
     "summary", "around-enter", "billing-before", "risk-before", "billing-primary", "base",
     "risk-after", "billing-after", "around-exit", "nested-review"]) := rfl

/-- Failed admission suppresses review; a new current context can be retried. -/
example : [((reviewedSummary 30 false forecastReview).run []).map (fun result => result.1.1),
    ((reviewedSummary 30 true forecastReview).run []).map (fun result => result.1.1)] =
    [.error "slot is hidden or undeclared", .ok 126] := rfl

/-- A failing review preserves the exact failure rather than returning the
already computed amount. External mutation rollback is not part of this model. -/
example : (reviewedSummary 40 true (fun _ => throw "review-refused")).run [] =
    .error "review-refused" := rfl

/-- Even a cheaper continuation can lose when independently supplied collector
history increases. The units here illustrate the theorem, not measured time. -/
example : observationCharge 1 100 10 2 0 < observationCharge 1 100 10 5 0 ∧
    ¬ observationCharge 1 100 10 2 400 ≤ observationCharge 1 100 10 5 0 := by decide

#print axioms observation_fusion
#print axioms fusedObservation_refused
#print axioms fusedObservation_current
#print axioms observationCharge_threshold
#print axioms assembleRow_eq
#print axioms combineDirect_assembled
#print axioms rowAssemblyCharge_difference
#print axioms rowAssemblyCharge_threshold
#print axioms rowAssemblyCharge_workflow
end LeanPoo.Examples.DeclaredMethods
