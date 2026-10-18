import LeanPoo.Functional.MethodDeclarations
import LeanPoo.Functional.NonlocalDeclarations

/-! Matching pure declaration-to-generic controls. Native macro expansion, actual
C3 sharing and descriptor mutation are exercised separately in Gerbil. -/
namespace LeanPoo.Examples.DeclaredMethods
open Object.MethodCombination
open Functional.DeclarativeMetadata
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
end LeanPoo.Examples.DeclaredMethods
