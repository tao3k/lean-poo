import LeanPoo.Functional.Parameters
import LeanPoo.Functional.SlotScope
import LeanPoo.Functional.AssociationBindings
import LeanPoo.Object.DeclarationOrder
import LeanPoo.Functional.InferenceReports
import LeanPoo.Functional.FunctionSignature
import LeanPoo.Functional.RecursiveTypes

/-! Checked positional prefixes compose with the existing delayed slot semantics.
The executable Gerbil fixture additionally tests actual C3, macro hygiene, generic
argument forwarding, Type admission, FUN effects and multiple values. -/
namespace LeanPoo.Examples.Parameters
open Functional.Parameters
abbrev Service := Template String Int

/-- Parameters remain absent until bound; unrelated data is retained exactly. -/
def service : Service := ⟨["capacity","tariff"],fun key => if key = "independent" then some 7 else none⟩

/-- Required input lookup preserves absence rather than treating it as zero. -/
def require (source : Service) (key : String) : Except String Int :=
  match source.fields key with | none => .error "missing parameter" | some value => .ok value

/-- The C3-resolved fee chain shares one final self and one base contribution. -/
def fee : LeanPoo.Prototype.Method Service Int :=
  LeanPoo.Prototype.Method.compose
    (fun self next => next () + (self.fields "tariff").getD 0)
    (LeanPoo.Prototype.Method.compose (fun _ next => next ()+1)
      (LeanPoo.Prototype.Method.compose (fun _ next => next ()+2) (fun _ _ => 5)))

/-- Admission precedes arithmetic/effects; discount uses canonical optional input. -/
def quote (source : Service) (units : Int) (discount : Option Int) : Except String Int := do
  let capacity ← require source "capacity"
  let tariff ← require source "tariff"
  unless capacity ≥ 0 && tariff ≥ 0 do throw "negative parameter"
  return units * (capacity*tariff + fee source (fun _ => 0)) - optional discount (fun _ => 0)

/-- Use the checked public specialization boundary, retaining its original failure. -/
def bind (source : Service) (values : List Int) : Except String Service :=
  match checkedSpecialize ".parameters" source values with
  | .ok next => .ok next
  | .error .declaration => .error "invalid declaration"
  | .error .excess => .error "too many arguments"

/-- Compare finite returned/error observations without equating opaque receivers. -/
def sameQuote (left right : Except String Int) : Bool :=
  match left,right with
  | .ok a,.ok b => a == b
  | .error a,.error b => a == b
  | _,_ => false

/-- Rejection has no partially specialized receiver available to a consumer. -/
def rejected (result : Except String Service) : Bool :=
  match result with | .error _ => true | .ok _ => false

/-- Full and staged construction agree, formulas use derived fields, and malformed
metadata/excess/negative inputs cannot produce an admitted quote. -/
def test : Except String Unit := do
  let staged ← bind service [10]
  unless staged.remaining == ["tariff"] && staged.fields "capacity" == some 10 &&
      staged.fields "tariff" == none && sameQuote (quote staged 2 none) (.error "missing parameter") do throw "partial closure"
  let complete ← bind staged [3]
  let direct ← bind service [10,3]
  unless complete.remaining.isEmpty && sameQuote (quote complete 2 none) (.ok 82) &&
      sameQuote (quote complete 2 (some 1)) (.ok 81) && sameQuote (quote direct 2 none) (quote complete 2 none) &&
      complete.fields "independent" == some 7 && service.fields "capacity" == none do throw "complete final self"
  let negative ← bind service [-1,3]
  unless sameQuote (quote negative 2 none) (.error "negative parameter") do throw "admission gate"
  unless rejected (bind service [1,2,3]) && rejected (bind complete [1]) do throw "excess closure"
  let invalid : Service := ⟨["capacity","capacity"],service.fields⟩
  unless rejected (bind invalid []) do throw "invalid empty specialization"
  unless bindings ["region"] ["capacity","tariff"] false == ["region"] &&
      bindings ["region"] ["capacity","tariff"] true == ["region","capacity","tariff"] do throw "lexical imports"

#print axioms Functional.Parameters.specialize_zero
#print axioms Functional.Parameters.specialize_excess
#print axioms Functional.Parameters.specialize_remaining
#print axioms Functional.Parameters.bind_append
#print axioms Functional.Parameters.specialize_append
#print axioms Functional.Parameters.bind_frame
#print axioms Functional.Parameters.invalid_declaration
#print axioms Functional.Parameters.valid_drop
#print axioms Functional.Parameters.checked_append
#print axioms Functional.Parameters.bindings_membership
#print axioms Functional.Parameters.inherited_alias
#print axioms Functional.Parameters.optional_supplied
#print axioms Functional.Parameters.optional_absent
#eval match test with
  | .ok () => IO.println "PARAMETERS-OK"
  | .error cause => throw (IO.userError cause)
/-- The source C4 order is child/left/right/base; field inventory is ancestor-first. -/
example : inheritedNames [[3], [1], [2], [0]] = [0, 2, 1, 3] := rfl
/-- Repeated local declarations do not move the first inherited field position. -/
example : inheritedNames [[3, 0], [1, 0], [2, 0], [0]] = [0, 2, 1, 3] := by decide

/-- Equal printed names may have different lexical binding identities. -/
def scopedIdentifiers : List (String × Nat) := [("value",1),("value",2),("value",1)]
example : uniqueBindings Prod.snd [] scopedIdentifiers = [("value",1),("value",2)] := by decide

/-- Current child visibility suppresses the older public label; methods remain public. -/
def declarations : List (String × Bool × Nat) :=
  [("label",true,11),(".summary",false,2),("label",false,7),(".charge",false,3)]
example : Prototype.DescriptorReflection.publicDeclaration "label" declarations = none := by decide
example : Prototype.DescriptorReflection.publicDeclaration ".summary" declarations = some 2 := by decide
example : Prototype.DescriptorReflection.publicDeclaration "label"
    (uniqueBindings Prod.fst [] declarations) = none := by decide

#print axioms Functional.Parameters.find_uniqueBindings
#print axioms Prototype.DescriptorReflection.publicDeclaration_unique
/-- A promoted dispatch shape has one retained payload; unrelated bindings keep
source order, and suffix eviction retains the existing capacity bound. -/
def shapeBindings : List (String × Bool) := [("billing", false), ("risk", true), ("shared", false)]
example : promoteBinding Prod.fst ("risk", false) shapeBindings =
    [("risk", false), ("billing", false), ("shared", false)] := by decide
example : ((promoteBinding Prod.fst ("risk", false) shapeBindings).take 2) =
    [("risk", false), ("billing", false)] := by decide
/-- First removal differs from remove-all for malformed duplicate-key tables. -/
example : eraseBinding Prod.fst "risk" [("risk", false), ("risk", true)] = [("risk", true)] := by decide
example : ([("risk", false), ("risk", true)].filter (fun entry => entry.1 != "risk")) = [] := by decide
#print axioms eraseBinding_filter
#print axioms promoteBinding_distinct
#print axioms boundedPromotion_distinct
#print axioms boundedPromotion_length
/-- Separate outer/copy/local owners make accidental receiver capture visible. -/
def scopedLookup (owner : Nat) (name : String) : Int :=
  if name = "rate" then if owner = 1 then 10 else if owner = 2 then 20 else 7 else 0
example : withSlotScope scopedLookup 1 (fun outer =>
    withSlotScope scopedLookup 3 (fun inner => (outer "rate", inner "rate"))) = (10, 7) := by decide
example : withSlotScope scopedLookup 2 (fun outer =>
    withSlotScope scopedLookup 3 (fun inner => (outer "rate", inner "rate"))) = (20, 7) := by decide
example : withSlotScope scopedLookup 1 (fun fields => fun (_ : Nat) => fields "rate") 2 = 10 := by decide
/-- Revision is explicit in this pure model; host mutable lookup has separate tests. -/
example : withSlotScope (fun owner name revision => scopedLookup owner name + revision) 1
    (fun fields => (fields "rate" 0, fields "rate" 20)) = (10, 30) := by decide
#print axioms withSlotScope_read
#print axioms withSlotScope_call
#print axioms withSlotScope_nested
#print axioms withSlotScope_capture
#print axioms withSlotScope_congr
#print axioms withSlotScope_revision
/-- Alias identity is already resolved here. The host expander must additionally
preserve lexical identity; source revisions remain explicit reader inputs. -/
def prefixedFields (key : String) (revision : Int) : Except String Int :=
  if key = "rate" then .ok (10 + revision) else .error "missing field"
/-- A retained field reader follows revisions; the initial snapshot stays fixed. -/
example : withSlotBindings prefixedFields [("account-rate", "rate")]
    (fun _ _ => .error "unbound") (fun fields =>
      let initial := fields "account-rate" 0
      (initial, fields "account-rate" 10)) = (.ok 10, .ok 20) := rfl
/-- Nested aliases shadow locally without changing a captured outer lookup. -/
example : withSlotBindings (fun key => if key = "rate" then (10 : Int) else 7)
    [("rate", "rate")] (fun _ => 0) (fun outer =>
      withSlotBindings (fun _ => (7 : Int)) [("rate", "rate")] outer
        (fun inner => (outer "rate", inner "rate"))) = (10, 7) := by decide
/-- Repeated names retain inner binding semantics; removing them indiscriminately
would instead select the first key and is not an equivalent lowering. -/
example : withSlotBindings (fun key => if key = "old" then (10 : Int) else 20)
    [("field", "old"), ("field", "new")] (fun _ => 0) (fun fields => fields "field") = 20 := by decide
/-- An unused missing field remains unselected, whereas actual use refuses. -/
example : withSlotBindings prefixedFields [("unused", "missing")]
    (fun _ _ => .error "unbound") (fun _ => (Except.ok 7 : Except String Int)) = .ok 7 := rfl
example : withSlotBindings prefixedFields [("used", "missing")]
    (fun _ _ => .error "unbound") (fun fields => fields "used" 0) = .error "missing field" := rfl
#print axioms withSlotBindings_nil
#print axioms withSlotBindings_cons
#print axioms withSlotBindings_recursive
#print axioms withSlotBindings_append
#print axioms withSlotBindings_shadow
#print axioms withSlotBindings_unused
/-- Prefix effects survive snapshot refusal; neither the suffix nor body runs. -/
example : ((snapshotSlotBindings
    (fun (_ : String → Int) key => do
      modify (· ++ [key])
      if key = "refused" then throw "snapshot refused" else pure 10)
    [("first", "rate"), ("second", "refused"), ("last", "unreachable")]
    (fun _ => 0) (fun fields => do modify (· ++ ["body"]); pure (fields "first"))) :
    ExceptT String (StateM (List String)) Int).run.run [] =
    (.error "snapshot refused", ["rate", "refused"]) := rfl
/-- A later snapshot may use an earlier binding; the body sees both snapshots. -/
example : snapshotSlotBindings
    (fun (fields : String → Int) key => (Except.ok (fields key + 1) : Except String Int))
    [("first", "rate"), ("second", "first")] (fun _ => 10)
    (fun fields => .ok (fields "first", fields "second")) = .ok (11, 12) := rfl
#print axioms snapshotSlotBindings_nil
#print axioms snapshotSlotBindings_cons
#print axioms snapshotSlotBindings_recursive
#print axioms snapshotSlotBindings_refused

section
open Functional.PrototypeTypes Functional.DeclarativeMetadata

/-- One composite packet retains Pair/Map/List children, optional sentinels,
tag order and nested Function variance while Value is partially specialized. -/
def metadataPacket : Expr := .tuple
  [.pair (.list (.var 0)) (.map (.ground (.atom .uint))
    (.function [.var 0] [.ground (.atom .integer)])),
   .orFalse (.maybe (.sum [0, 1]
    [.tuple [.function [.var 0] [.ground (.atom .integer)]],
     .list (.function [.var 0] [.ground (.atom .integer)])]))]
/-- Callback remains a residual variable; the original bound observes the whole
packet. Rich named-row admission is separately modeled by RowTypes.splice. -/
def metadataBounds : List (Expr × Expr) :=
  [(.var 1, .function [metadataPacket] [.var 0])]
/-- Original service signature retains both user outputs and its input position. -/
def metadataSignature : Expr := .function [.var 0, .var 1] [.var 0]
/-- A broader Integer input safely implements the remaining UInt callback bound. -/
def metadataCallback : Ty := .function [substitute (fun _ => .atom .uint) metadataPacket] [.atom .integer]
/-- Unique complete search alone builds the original signature at the combined
environment. No normalized private view is installed as the source declaration. -/
def metadataPublication := inferDeclared 1
  (fun callback => satisfies 24
    (metadataBounds.map (fun (a, b) => (specializeExpr [.atom .uint] a, specializeExpr [.atom .uint] b)))
    (fun _ => callback)) [metadataCallback]
  (fun callback => (Except.ok
    (substitute (prefixEnvironment [.atom .uint] (fun _ => callback)) metadataSignature) : Except String Ty))

#guard match metadataPublication with | .ok (.unique _, some _) => true | _ => false
example : substitute (fun _ => metadataCallback) (specializeExpr [.atom .uint] metadataSignature) =
    substitute (prefixEnvironment [.atom .uint] (fun _ => metadataCallback)) metadataSignature :=
  substitute_specializeExpr _ _ _

/-- Original constraint provenance and the exact original declaration survive
partial specialization, residual inference and one complete publication. -/
theorem metadataPublication_sound (callback artifact)
    (published : metadataPublication = .ok (.unique callback, some artifact)) :
    artifact = substitute (prefixEnvironment [.atom .uint] (fun _ => callback)) metadataSignature ∧
    ∀ a b, (a, b) ∈ metadataBounds →
      Subtype (substitute (prefixEnvironment [.atom .uint] (fun _ => callback)) a)
        (substitute (prefixEnvironment [.atom .uint] (fun _ => callback)) b) := by
  obtain ⟨_, accepted, built⟩ := inferDeclared_unique 1 _ [metadataCallback] _ published
  refine ⟨(Except.ok.inj built).symm, ?_⟩
  rw [satisfies_specializeExpr] at accepted
  intro a b inside
  exact satisfies_sound 24 metadataBounds _ accepted inside

/-- Illustrative structural charges surround the existing complete metadata
publication. Seven/five are abstract ledger units, not measured Gerbil costs.
The finite candidate/bound proofs and original artifact remain unchanged. -/
def metadataBudgetedPublication (budget : Nat) :=
  completeDeclaredWork 7 5 budget metadataPublication
    (fun result => (Except.ok result : Except (Sum Functional.PrototypeTypes.Failure String) _))

#guard match metadataBudgetedPublication 11 with | .error (.inl .exhausted) => true | _ => false
#guard match metadataBudgetedPublication 12 with | .ok ((.unique _, some _), 0) => true | _ => false
#guard match metadataBudgetedPublication 20 with | .ok ((.unique _, some _), 8) => true | _ => false

/-- Budgeted admission retains the SAME original declaration and every bound
from the independently established complete unique metadata search. -/
theorem metadataBudgetedPublication_sound (budget callback artifact remaining)
    (accepted : metadataBudgetedPublication budget = .ok ((.unique callback, some artifact), remaining)) :
    12 ≤ budget ∧ remaining = budget - 12 ∧
      artifact = substitute (prefixEnvironment [.atom .uint] (fun _ => callback)) metadataSignature ∧
      ∀ a b, (a, b) ∈ metadataBounds →
        Subtype (substitute (prefixEnvironment [.atom .uint] (fun _ => callback)) a)
          (substitute (prefixEnvironment [.atom .uint] (fun _ => callback)) b) := by
  obtain ⟨enough, balance, report, prepared, built⟩ :=
    completeDeclaredWork_sound 7 5 budget metadataPublication _ accepted
  have same : report = (.unique callback, some artifact) := Except.ok.inj built
  rw [same] at prepared
  obtain ⟨source, bounds⟩ := metadataPublication_sound callback artifact prepared
  exact ⟨enough, balance, source, bounds⟩

/-- A builder failure wins over the later quota check; successful retry needs
an independent quota and still returns the original artifact. -/
example : completeDeclaredWork 7 5 7 (.ok ())
    (fun _ => (Except.error (.inr "approval refused") : Except (Sum Functional.PrototypeTypes.Failure String) Ty)) =
      .error (.inr "approval refused") := rfl

/-- Runtime observation of an already admitted artifact carries a zero balance
unchanged. Actual Scheme closure independence is a separate executable check. -/
example : observeDeclaredWork
    (Except.ok (metadataCallback, 0) : Except String (Ty × Nat))
    (fun callback => .ok callback) = .ok (metadataCallback, 0) := rfl

#print axioms observeDeclaredWork_balance
#print axioms declarationStage_compose
#print axioms completeDeclaredWork_sound
#print axioms completeDeclaredWork_early_refusal
#print axioms completeDeclaredWork_late_refusal
#print axioms completeDeclaredWork_build_refusal
#print axioms completeDeclaredWork_more
#print axioms admitDeclaredSource_valid
#print axioms metadataBudgetedPublication_sound

/-- Specializing field Types before an admitted row extension preserves the
same extension and every literal label; no override or inferred row is inserted. -/
example (fixed : List Ty) (explicit extension result : Functional.RowTypes.Row String Expr)
    (accepted : Functional.RowTypes.splice explicit extension = .ok result) :
    Functional.RowTypes.splice
      (Functional.RowTypes.mapFields (specializeExpr fixed) explicit)
      (Functional.RowTypes.mapFields (specializeExpr fixed) extension) =
        .ok (Functional.RowTypes.mapFields (specializeExpr fixed) result) :=
  Functional.RowTypes.splice_mapFields _ _ _ _ accepted

#print axioms substitute_substituteExpr
#print axioms substituteExpr_identity
#print axioms substitute_specializeExpr
#print axioms satisfies_specializeExpr
#print axioms metadataPublication_sound
#print axioms Functional.RecursiveTypes.unfold_transform
#print axioms Functional.RowTypes.lookup_mapFields
#print axioms Functional.RowTypes.splice_mapFields
end
/-- One finite Self binding uses the existing parameter snapshot, not a new Type. -/
def signatureBindings : List (BoundParameter String Nat) := [⟨"Self", 7, 0⟩]

/-- A stale initial owner suppresses even an explicitly failing observer. -/
example : Functional.DeclarativeMetadata.prepareDeclaredSignature signatureBindings
    (fun _ => some 8) (fun _ => 0) (fun _ => .error "observer refused")
    (fun (_ : Nat) _ => some 7) (fun _ _ => 0) = .error (.inl .bounds) := rfl

/-- A successful observer that replaces Self cannot publish its certificate. -/
example : Functional.DeclarativeMetadata.prepareDeclaredSignature signatureBindings
    (fun _ => some 7) (fun _ => 0) (fun _ => (Except.ok 23 : Except String Nat))
    (fun _ _ => some 8) (fun _ _ => 0) = .error (.inl .bounds) := rfl

/-- Identity alone is insufficient when the descriptor's direct revision changes. -/
example : Functional.DeclarativeMetadata.prepareDeclaredSignature signatureBindings
    (fun _ => some 7) (fun _ => 0) (fun _ => (Except.ok 23 : Except String Nat))
    (fun _ _ => some 7) (fun _ _ => 1) = .error (.inl .bounds) := rfl

/-- The observer's own failure precedes the success-only stale-source recheck. -/
example : Functional.DeclarativeMetadata.prepareDeclaredSignature signatureBindings
    (fun _ => some 7) (fun _ => 0) (fun _ => .error "observer refused")
    (fun (_ : Nat) _ => some 8) (fun _ _ => 1) = .error (.inr "observer refused") := rfl

/-- Restoring the field identity allows a fresh request with the original revision. -/
example : Functional.DeclarativeMetadata.prepareDeclaredSignature signatureBindings
    (fun _ => some 7) (fun _ => 0) (fun _ => (Except.ok 23 : Except String Nat))
    (fun _ _ => some 7) (fun _ _ => 0) = .ok 23 := rfl

/-- Unique inference cannot hide a stale signature-preparation failure. -/
example : Functional.DeclarativeMetadata.inferDeclared 1 (fun (_ : Nat) => true) [7]
    (fun _ => Functional.DeclarativeMetadata.prepareDeclaredSignature signatureBindings
      (fun _ => some 7) (fun _ => 0) (fun _ => (Except.ok 23 : Except String Nat))
      (fun _ _ => some 8) (fun _ _ => 0)) = .error (.inr (.inl .bounds)) := rfl

#print axioms Functional.DeclarativeMetadata.prepareDeclaredSignature_sound
#print axioms Functional.DeclarativeMetadata.prepareDeclaredSignature_stale
#print axioms Functional.DeclarativeMetadata.prepareDeclaredSignature_error
#print axioms Functional.DeclarativeMetadata.prepareDeclaredSignature_changed
section QueryReports
open Functional.PrototypeTypes Functional.DeclarativeMetadata

/-- An ordered nested callback query retains its original syntax through report
publication; UInt output narrows a callback returning the inferred parameter. -/
def requestQueries : List (Expr × Expr) :=
  [(.function [.ground (.atom .uint)] [.ground (.atom .integer)],
    .function [.var 0] [.ground (.atom .integer)])]
/-- One finite prefix has already fixed other fields; this is its residual Self. -/
def requestEnvironment : Nat → Ty := fun _ => .atom .uint
/-- The declaration callback returns its artifact and a reused incompatible buffer. -/
def revisedRequest (_ : Nat → Ty) : Except String (Nat × List (Expr × Expr)) :=
  .ok (31, [(.ground (.atom .bool), .var 0)])

/-- The actual nested callback query succeeds under the supplied finite candidate.
Compute only this closed Boolean judgment, not an expanded symbolic search tree. -/
theorem requestSolved : inferBounded 1 (satisfies 4 ([] ++ requestQueries)) [requestEnvironment] =
    .ok (.unique requestEnvironment) := by
  have valid : satisfies 4 requestQueries requestEnvironment = true := by
    simp only [satisfies, requestQueries, List.all_cons, List.all_nil, substitute,
      List.map_cons, List.map_nil, requestEnvironment, Bool.and_true]
    decide
  simp [inferBounded, infer, valid]

/-- Even a callback that changes caller data cannot change the captured evidence. -/
example : inferDeclaredQueries 4 1 [] requestQueries [requestEnvironment] revisedRequest =
    .ok ((.unique requestEnvironment, some 31), requestQueries) :=
  inferDeclaredQueries_unique _ _ _ _ _ _ _ _ _ requestSolved rfl

/-- Fresh inference uses the changed request and refuses it as a complete no-solution;
the old report above remains a report about the original constraints. -/
example : inferDeclaredQueries 4 1 [] [(.ground (.atom .bool), .var 0)]
    [requestEnvironment] revisedRequest = .ok ((.none, none), [(.ground (.atom .bool), .var 0)]) := by
  have invalid : satisfies 4 [(.ground (.atom .bool), .var 0)] requestEnvironment = false := by
    simp only [satisfies, List.all_cons, List.all_nil, substitute, requestEnvironment, Bool.and_true]
    decide
  apply inferDeclaredQueries_none
  simp [inferBounded, infer, invalid]

/-- Incomplete search returns no artifact or successful report even if its first
candidate would satisfy the query; the existing exhaustion theorem supplies it. -/
example : inferDeclaredQueries 4 0 [] requestQueries [requestEnvironment] revisedRequest =
    .error (.inl .exhausted) := inferDeclaredQueries_exhausted _ _ _ _ _ _ (by decide)

/-- The caller's own declaration error is not replaced by diagnostic success. -/
example : inferDeclaredQueries 4 1 [] requestQueries [requestEnvironment]
    (fun _ => (Except.error "declaration refused" : Except String (Nat × Unit))) =
    .error (.inr "declaration refused") :=
  inferDeclaredQueries_error _ _ _ _ _ _ _ _ requestSolved rfl

/-- Accepted reports justify every ORIGINAL query under the selected assignment;
faithful Scheme copying and host Type interpretations remain explicit premises. -/
example (env artifact reported)
    (accepted : inferDeclaredQueries 4 1 [] requestQueries [requestEnvironment] revisedRequest =
      .ok ((.unique env, some artifact), reported)) :
    reported = requestQueries ∧
      ∀ a b, (a, b) ∈ reported → Subtype (substitute env a) (substitute env b) := by
  obtain ⟨captured, _, constraints, _⟩ := inferDeclaredQueries_sound _ _ _ _ _ _ _ _ _ accepted
  exact ⟨captured, fun a b inside => constraints a b (by simpa using inside)⟩

#print axioms inferDeclaredQueries_sound
#print axioms inferDeclaredQueries_unique
#print axioms inferDeclaredQueries_none
#print axioms inferDeclaredQueries_ambiguous
#print axioms inferDeclaredQueries_exhausted
#print axioms inferDeclaredQueries_error
end QueryReports
section CapturedSignatures
open Functional.FunctionSignature

/-- Finite Type identities model UInt output and Integer supplied positions;
required/optional/keyword/rest rows are all present in this declaration. -/
def ownedSignature : TypedSignature String Nat :=
  ⟨[1], [2], [2], [("gate", 1), ("quota", 1)], ["gate", "quota"], some 2⟩
/-- A later case has a wider result and requires only gate; its order is explicit. -/
def fallbackSignature : TypedSignature String Nat :=
  {ownedSignature with outputs := [3], requiredKeywords := ["gate"]}
/-- This call deliberately lacks quota while satisfying positional and gate shape. -/
def missingQuota : Call String Int := ⟨[4], [("gate", 3)]⟩
/-- The closed call supplies both original mandatory keys. -/
def completeQuota : Call String Int := ⟨[4], [("gate", 3), ("quota", 4)]⟩
/-- The finite leaf checker distinguishes unsigned output from wider Integer;
the general capture laws work with arbitrary supplied Type interpretations. -/
def checkCapturedValue (type : Nat) (value : Int) : Except String Int :=
  if type = 1 ∧ value < 0 then .error "unsigned output" else .ok value

/-- A reused caller definition may request another language; the existing captured
signature still has its own original missing-key refusal. -/
example : accepts ownedSignature.capture.shape missingQuota = false ∧
    accepts fallbackSignature.shape missingQuota = true := by decide

/-- Original required keys refuse before any supplied normalizer/body callback. -/
example (normalize : Signature String → Call String Int → Except String (Call String Int))
    (body : Call String Int → Except String Nat) :
    invoke [ownedSignature.capture.shape] missingQuota "shape" normalize body = .error "shape" :=
  invoke_capture_missing _ _ "quota" (by decide) (by decide) _ _ _

/-- Missing quota selects the second ORIGINAL case and retains its result/owner. -/
example : invokeValues ([ownedSignature, fallbackSignature].map TypedSignature.capture)
    missingQuota "shape" "count" (fun _ call => .ok call)
    (fun _ => .ok ([-1], 73)) checkCapturedValue = .ok ([-1], 73) := rfl

/-- Once the first clause matches, its result error never falls back to the wider
second clause. Constructor capture changes neither that cause nor the owner rule. -/
example : invokeValues ([ownedSignature, fallbackSignature].map TypedSignature.capture)
    completeQuota "shape" "count" (fun _ call => .ok call)
    (fun _ => .ok ([-1], 73)) checkCapturedValue = .error "unsigned output" := rfl

/-- Prefix substitution and capture commute in every Type position without
rewriting literal keyword names or changing ordered dispatch. -/
example (signature : TypedSignature String Functional.PrototypeTypes.Expr)
    (fixed : List Functional.PrototypeTypes.Ty) :
    signature.capture.mapTypes (Functional.PrototypeTypes.specializeExpr fixed) =
      (signature.mapTypes (Functional.PrototypeTypes.specializeExpr fixed)).capture :=
  TypedSignature.capture_mapTypes _ _

#print axioms TypedSignature.capture_eq
#print axioms TypedSignature.capture_mapTypes
#print axioms capture_selection
#print axioms accepts_missing_required
#print axioms invoke_capture_missing
#print axioms invokeValues_capture
end CapturedSignatures

section CapturedSchemes
open Functional.PrototypeTypes

/-- The source declares Self <: Super before any computed parameter getter. -/
def initialBounds : List (Expr × Expr) := [(.var 0, .var 1)]
/-- The getter's later buffer reuse weakens its live bound to Self <: Self. -/
def rewrittenBounds (_ : List (Expr × Expr)) : Except Functional.PrototypeTypes.Failure (List (Expr × Expr)) :=
  .ok [(.var 0, .var 0)]
/-- Integer output cannot replace the original UInt input bound. -/
def invalidBinding (name : Nat) : Ty := if name = 0 then .atom .integer else .atom .uint
/-- The ordinary UInt output / Integer input specialization remains valid. -/
def validBinding (name : Nat) : Ty := if name = 0 then .atom .uint else .atom .integer

example : inferCaptured Except.ok rewrittenBounds initialBounds 8 2
    [invalidBinding, validBinding] = .ok (.unique validBinding) := by
  have invalid : satisfies 8 initialBounds invalidBinding = false := by
    simp only [satisfies, initialBounds, List.all_cons, List.all_nil, substitute, invalidBinding]
    decide
  have valid : satisfies 8 initialBounds validBinding = true := by
    simp only [satisfies, initialBounds, List.all_cons, List.all_nil, substitute, validBinding]
    decide
  simp [inferCaptured, rewrittenBounds, Except.bind, inferBounded, infer, invalid, valid]

/-- Re-reading the weakened live buffer would instead accept both candidates. -/
example : inferBounded 2 (satisfies 8 [(.var 0, .var 0)]) [invalidBinding, validBinding] =
    .ok (.ambiguous [invalidBinding, validBinding]) := by
  have left : satisfies 8 [(.var 0, .var 0)] invalidBinding = true := by
    simp only [satisfies, List.all_cons, List.all_nil, substitute, invalidBinding]
    decide
  have right : satisfies 8 [(.var 0, .var 0)] validBinding = true := by
    simp only [satisfies, List.all_cons, List.all_nil, substitute, validBinding]
    decide
  simp [inferBounded, infer, left, right]

/-- Capture failure wins over a computed getter failure and cannot start search. -/
example : inferCaptured (fun (_ : Unit) => .error .exhausted)
    (fun _ => .error .bounds) () 8 2 [invalidBinding, validBinding] = .error .exhausted := rfl

/-- Complete search still refuses an insufficient quota after successful refresh. -/
example : inferCaptured Except.ok rewrittenBounds initialBounds 8 1
    [invalidBinding, validBinding] = .error .exhausted := rfl

#print axioms inferCaptured_capture_refused
#print axioms inferCaptured_refresh_refused
#print axioms inferCaptured_eq
#print axioms inferCaptured_bound

/-- This request supplied only the valid UInt/Integer assignment. -/
def initialRequest : InferenceRequest := ⟨[validBinding], initialBounds⟩
/-- A computed getter reuses live candidate AND query buffers after capture. -/
def replaceRequest (_ : InferenceRequest) : Except Functional.PrototypeTypes.Failure InferenceRequest :=
  .ok ⟨[invalidBinding], [(.var 0, .var 0)]⟩

example : inferCapturedRequest Except.ok replaceRequest initialRequest 8 1 =
    .ok (.unique validBinding) := by
  have valid : satisfies 8 initialBounds validBinding = true := by
    simp only [satisfies, initialBounds, List.all_cons, List.all_nil, substitute, validBinding]
    decide
  simp [inferCapturedRequest, inferCaptured, replaceRequest, initialRequest,
    Except.bind, inferBounded, infer, valid]

/-- Refresh cannot admit a replacement candidate when the initial universe is empty. -/
example : inferCapturedRequest Except.ok replaceRequest ⟨[], initialBounds⟩ 8 1 =
    .ok .none := rfl

/-- Duplicate original candidates remain ambiguous; refresh is not a tie breaker. -/
example : inferCapturedRequest Except.ok replaceRequest
    ⟨[validBinding, validBinding], []⟩ 8 2 =
      .ok (.ambiguous [validBinding, validBinding]) := rfl

/-- Capture failure cannot be replaced by a later getter error or success. -/
example : inferCapturedRequest (fun (_ : Unit) => .error .exhausted)
    (fun _ => .error .bounds) () 8 1 = .error .exhausted := rfl

#print axioms inferCapturedRequest_refused
#print axioms inferCapturedRequest_eq
#print axioms inferCapturedRequest_refresh_refused
#print axioms inferCapturedRequest_unique
end CapturedSchemes

section FinalSourceAdmission
open Functional.DeclarativeMetadata

/-- The finite fixture encodes original UInt/Integer syntax and a closed suffix. -/
def finalSourceMetadata : List Nat × List String := ([0, 1], [])
/-- The original Output descriptor has identity 7 and direct revision 2. -/
def finalSourceBindings : List (Functional.Parameters.BoundParameter String Nat) :=
  [⟨"Output", 7, 2⟩]
/-- Actual post-getter observations retain the same field identity. -/
def finalSourceFields (_ : String) : Option Nat := some 7
/-- A pure direct-revision observation runs after every source callback. -/
def finalSourceRevisions (_ : Nat) : Nat := 2

example : finalizeDeclaredSource finalSourceMetadata finalSourceMetadata
    finalSourceBindings finalSourceFields finalSourceRevisions "artifact" = .ok "artifact" := rfl

/-- A late raw syntax edit refuses despite earlier successful binding admission. -/
example : finalizeDeclaredSource finalSourceMetadata ([2, 1], [])
    finalSourceBindings finalSourceFields finalSourceRevisions "artifact" = .error .bounds := rfl

/-- Reopened parameters cannot pass using the original closed suffix snapshot. -/
example : finalizeDeclaredSource finalSourceMetadata ([0, 1], ["Again"])
    finalSourceBindings finalSourceFields finalSourceRevisions "artifact" = .error .bounds := rfl

/-- A later getter invalidating an earlier descriptor refuses the whole artifact. -/
example : finalizeDeclaredSource finalSourceMetadata finalSourceMetadata
    finalSourceBindings finalSourceFields (fun _ => 3) "artifact" = .error .bounds := rfl

/-- The same final gate also retains exact descriptor identity, not just revision. -/
example : finalizeDeclaredSource finalSourceMetadata finalSourceMetadata
    finalSourceBindings (fun _ => some 8) finalSourceRevisions "artifact" = .error .bounds := rfl

#print axioms finalizeDeclaredSource_changed
#print axioms finalizeDeclaredSource_stale
#print axioms finalizeDeclaredSource_sound
#print axioms finalizeDeclaredSource_error
end FinalSourceAdmission
end LeanPoo.Examples.Parameters
