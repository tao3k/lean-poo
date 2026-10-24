import LeanPoo.Functional.DispatchExtension
import LeanPoo.Functional.DispatchHandling
import LeanPoo.Functional.DeclarativeMetadata
import LeanPoo.Object.MethodCombination

/-! Independently installed document/payment extensions share a generic.
Negative call and shape assumptions protect defaults; refused publication
retains the old warm generic. Accepted methods execute with retained state. -/
namespace LeanPoo.Examples.ProtectedDispatch
open Functional Object Object.MethodCombination Functional.DispatchExtension

structure Args where
  document : String
  channel : String
  amount : Nat
abbrev Action := EStateM String (List String)
structure Fragment where
  name : String
  body : Contribution Args Action Nat
abbrev Generic := Multimethod Args Fragment (Action Nat)

def precedence (args : Args) : DispatchShape :=
  [[args.document, "Document"], [args.channel, "Channel"]]
def combine (fragments : Array Fragment) (args : Args) : Action Nat :=
  effective (fragments.toList.foldr (fun fragment methods => methods.prepend fragment.body) {})
    (fun _ => do modify (· ++ ["default"]); return 0) args
def blank : Generic := { arity := 2, precedence, combine }
def primary (name : String) (fee : Nat) : Fragment :=
  ⟨name, .primary (fun next _ => do
    modify (· ++ [name]); let inherited ← next (); return inherited+fee)⟩
def audit : Fragment := ⟨"card-audit", .around (fun next _ => do
  modify (· ++ ["audit-enter"]); let result ← next (); modify (· ++ ["audit-exit"]); return result)⟩
def path (document channel : String) : List Specializer := [.prototype document, .prototype channel]
def card : Args := ⟨"Invoice", "Card", 10⟩
def low : Args := ⟨"Invoice", "Bank", 10⟩
def high : Args := ⟨"Invoice", "Bank", 150⟩
def watches : List (Watch Args) := [.call low, .call high, .shape (precedence ⟨"Report", "Bank", 0⟩)]
def guarded : Edit Args Fragment := .registerWhen (path "Invoice" "Bank") (·.amount > 100) (primary "risk-fee" 7)

def describe {generic : Generic} {edits : List (Edit Args Fragment)}
    {watches : List (Watch Args)} (failure : Failure generic watches edits) : String :=
  match failure with
  | .registration (.arity expected actual) _ => s!"arity:{expected}/{actual}"
  | .introduced _ _ conflict =>
    s!"watch:{conflict.earlier.length}:" ++ (conflict.violation.firstMethod.map Fragment.name).getD "shape-error"

def run : Except String (List String) := do
  let registered ← (blank.register (path "Invoice" "Card") (primary "card-base" 3)).mapError (fun _ => "register")
  let (_, warm) ← (registered.call card).mapError (fun _ => "warm")
  let previous ← (check warm watches).mapError (fun _ => "baseline")
  let accepted ← (guard warm watches previous [.contribute (path "Invoice" "Card") audit]).mapError describe
  let invocation ← (accepted.certificate.invoke card).mapError (fun _ => "call")
  let action := invocation.result
  let updated := invocation.snapshot
  let execution := match action.run [] with
    | .ok value trace => s!"card:{value}:" ++ String.intercalate "," trace
    | .error error _ => error
  let refused := guard updated watches invocation.certificate [guarded]
  let refusal := match refused with | .error failure => describe failure | .ok _ => "unexpected acceptance"
  let (published, retained) := publish updated watches invocation.certificate [guarded]
  let preserved := s!"retained:{retained.cache.values.size == updated.cache.values.size}:{published.toOption.isNone}"
  let lowCertificate ← (check warm [.call low]).mapError (fun _ => "low baseline")
  let admitted ← (guard warm [.call low] lowCertificate [guarded]).mapError describe
  let (_, lowWarm) ← (admitted.snapshot.call low).mapError (fun _ => "low call")
  let (highAction, _) ← (lowWarm.call high).mapError (fun _ => "high call")
  let dynamic := match highAction.run [] with | .ok value trace => s!"high:{value}:" ++ String.intercalate "," trace | .error error _ => error
  let canceled ← (guard warm watches previous [guarded, .erase (path "Invoice" "Bank")]).mapError describe
  let broad := guard warm watches previous [.register (path "Document" "Bank") (primary "orphan-library" 9)]
  let broadResult := match broad with | .error failure => describe failure | .ok _ => "unexpected acceptance"
  let invalid := guard warm watches previous [guarded, .register [.any] (primary "bad-arity" 1)]
  let invalidResult := match invalid with | .error failure => describe failure | .ok _ => "unexpected acceptance"
  let shapeCertificate ← (check warm [.shape (precedence low)]).mapError (fun _ => "shape baseline")
  let structural := guard warm [.shape (precedence low)] shapeCertificate
    [.registerWhen (path "Invoice" "Bank") (fun _ => false) (primary "cold-candidate" 2)]
  let structuralResult := match structural with | .error failure => describe failure | .ok _ => "unexpected acceptance"
  return [execution, refusal, preserved, dynamic, s!"canceled:{canceled.snapshot.cache.values.size}",
    broadResult, invalidResult, structuralResult]

#guard run.toOption == some ["card:3:audit-enter,card-base,default,audit-exit", "watch:1:risk-fee",
  "retained:true:true", "high:7:risk-fee,default", "canceled:0", "watch:0:orphan-library", "arity:2/1", "watch:0:cold-candidate"]

-- Publication/refusal and admission are universal contracts, including
-- arbitrary callback functions and sound warm candidate caches.
theorem accepted_sound (revision : Revision (Args := Args) (Method := Fragment) (Result := Action Nat) generic watches edits)
    (sound : generic.CacheSound) : revision.snapshot.CacheSound := revision.cacheSound sound

/-- A runtime signature boundary checks an encoded request before dispatch and
checks its result before exposing a warmed generic. Scheme reuses Type.validate;
this abstract contract leaves each actual validator's cost and soundness explicit. -/
theorem invalid_request_retains_no_cache
    (contract : DeclarativeMetadata.Contract Atom Input Output)
    (execute : Input → Except Error (Output × State)) (input : Input)
    (invalid : ¬ contract.input.holds input) :
    contract.invoke execute input = .error (.input contract.input.name) :=
  contract.invoke_input execute input invalid

theorem invalid_result_retains_no_cache
    (contract : DeclarativeMetadata.Contract Atom Input Output)
    (execute : Input → Except Error (Output × State)) (input : Input) (output : Output) (cache : State)
    (valid : contract.input.holds input) (called : execute input = .ok (output,cache))
    (invalid : ¬ contract.output.holds output) :
    contract.invoke execute input = .error (.output contract.output.name) :=
  contract.invoke_output execute input output cache valid called invalid

-- A shape forbids a guarded candidate even when this particular call rejects it.
-- Selection units remain on the warm path; they are not saved by candidate caching.
#guard (selectCounted (0 : Nat) [.when (· > 100) "risk", .always "base"]).2 == 2
#guard (selectCounted (150 : Nat) [.when (· > 100) "risk", .always "base"]).1 == ["risk", "base"]
#guard (selectCounted (10 : Nat) [.when (· > 100) "risk", .always "base"]).1 == ["base"]
#guard cacheComparisons [[ ["Invoice"], ["Card"] ], [ ["Invoice"], ["Bank"] ]] [["Report"], ["Bank"]] == 2
#print axioms selectCounted_cached
#print axioms observedCounted_result
#print axioms cacheComparisons_capacity
#print axioms invalid_request_retains_no_cache
#print axioms invalid_result_retains_no_cache

#eval IO.println s!"protected dispatch: {repr run.toOption}"
#print axioms Functional.DispatchExtension.guard_ok_iff
#print axioms Functional.DispatchExtension.publish_refused
#print axioms Functional.DispatchExtension.shape_covers_call
#print axioms Functional.DispatchExtension.Violation.firstMethod_origin
end LeanPoo.Examples.ProtectedDispatch
