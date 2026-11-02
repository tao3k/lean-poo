import LeanPoo.Functional.StagedPublication
import LeanPoo.Functional.DeclarativeMetadata
import LeanPoo.Functional.ConstructionWorkflow

/-! A materialized settlement graph feeds a typed quote/reserve/cancel family.
Joint admission rejects incoherent generic combinations before publication.
This advances the generalized-prototype/MOP future work. -/
namespace LeanPoo.Functional.ServiceBundle
open GeneralizedGraph GeneralizedMOP
open ConstructionWorkflow (Values Raw Interface Config Call Action)

inductive Service where
  | quote
  | reserve
  | cancel
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable

structure Policy where
  pricing : ConstructionWorkflow.Policy := .aggregate
  reserveShift : Int := 0
  cancelShift : Int := 0
  brokenReserve : Bool := false
  forbiddenCancel : Bool := false
  deriving Repr

abbrev Args : Service → Type
  | .quote => Call
  | .reserve => Nat
  | .cancel => String × Bool
abbrev Method : Service → Type
  | .quote => ConstructionWorkflow.Method
  | .reserve => Nat → Action (Int × Bool)
  | .cancel => (String × Bool) → Action (List String)
abbrev Result : Service → Type
  | .quote => Action Int
  | .reserve => Action (Int × Bool)
  | .cancel => Action (List String)

def seed : (key : Service) → Policy → Interface → Object.Multimethod (Args key) (Method key) (Result key)
  | .quote, policy, cooked => ConstructionWorkflow.model.seed policy.pricing cooked
  | .reserve, policy, _ => {
      arity := if policy.brokenReserve then 2 else 1
      precedence := fun _ => [["Reserve"]]
      combine := fun methods units => match methods[0]? with
        | none => .error "missing:reserve"
        | some method => method units }
  | .cancel, _, _ => {
      arity := 1
      precedence := fun args => [if args.1 == "forbidden" then ["Forbidden"] else ["Cancel"]]
      combine := fun methods args => match methods[0]? with
        | none => .error "missing:cancel"
        | some method => method args }

/-- Method metadata is executable source: qualifiers stay in the existing typed
contribution bodies and guards compile to the existing dispatch operation. -/
def declarations : (key : Service) → Policy → Interface →
    List (DeclarativeMetadata.Declaration (Args key) (Method key))
  | .quote, policy, cooked => DeclarativeMetadata.named "quote"
      (ConstructionWorkflow.model.methods policy.pricing cooked)
  | .reserve, policy, cooked => [.replace "reserve.capacity" [.prototype "Reserve"] (fun units => do
      let capacity ← ConstructionWorkflow.selected cooked.state "total"
      let capacity := capacity+policy.reserveShift
      return (capacity-units,decide ((units : Int) ≤ capacity)))]
  | .cancel, policy, cooked => [.replace "cancel.invoice" [.prototype "Cancel"] (fun args =>
      if !args.2 then .error "cancel.guard" else do
        let invoice ← ConstructionWorkflow.selected cooked.state "invoice"
        return [args.1,"invoice:" ++ toString (invoice+policy.cancelShift)])] ++
      if policy.forbiddenCancel then
        [.replace "cancel.forbidden" [.prototype "Forbidden"] (fun _ => .ok ["forbidden"])] else []

def methods (key : Service) (policy : Policy) (cooked : Interface) :
    List (DispatchExtension.Edit (Args key) (Method key)) :=
  (declarations key policy cooked).map DeclarativeMetadata.Declaration.compile

@[simp] theorem quote_declarations (policy : Policy) (cooked : Interface) :
    methods .quote policy cooked = ConstructionWorkflow.model.methods policy.pricing cooked :=
  DeclarativeMetadata.compile_named _ _

def watches : (key : Service) → List (DispatchExtension.Watch (Args key))
  | .quote => ConstructionWorkflow.watches
  | .reserve => [.shape [["Forbidden"]]]
  | .cancel => [.call ("forbidden",true)]

def model : StagedPublication.Model String Values Service Policy Interface Args Method Result where
  cook := fun policy raw => ConstructionWorkflow.model.cook policy.pricing raw
  generics := {
    keys := [.quote,.reserve,.cancel]
    seed
    seedEmpty := by intro key policy cooked; cases key <;> rfl
    methods
    watches }

abbrev Request := GeneralizedMOP.Request String Values Policy
abbrev Candidate (request : Request) := StagedPublication.Candidate model request
abbrev Edit := Redefinition String Values Policy

def quoteProbe {request : Request} (candidate : Candidate request) : Option Int :=
  (candidate.family.table.call .quote ⟨"Delivery","US",1⟩).toOption.bind fun pair => pair.1.toOption

def reserveProbe {request : Request} (candidate : Candidate request) : Option (Int × Bool) :=
  (candidate.family.table.call .reserve 2).toOption.bind fun pair => pair.1.toOption

def cancelProbe {request : Request} (candidate : Candidate request) : Option (List String) :=
  (candidate.family.table.call .cancel ("customer",true)).toOption.bind fun pair => pair.1.toOption

def expectedQuote (policy : Policy) (input total : Int) : Int :=
  if policy.pricing == .peak then max total input + 11 else total+input+7

/-- The checked obligation observes all three actual generics, not just a policy
label or the shared numerical graph. It is indexed by this exact candidate. -/
structure Approval (request : Request) (candidate : Candidate request) where
  input : Int
  invoice : Int
  total : Int
  inputReady : candidate.cache.closed.raw "input" = some (.ok input)
  invoiceReady : candidate.cache.closed.raw "invoice" = some (.ok invoice)
  totalReady : candidate.cache.closed.raw "total" = some (.ok total)
  limit : Int
  nonnegative : 0 ≤ total
  within : total ≤ limit
  coherent : (quoteProbe candidate,reserveProbe candidate,cancelProbe candidate) =
    (some (expectedQuote request.policy input total),some (total-2,decide (2 ≤ total)),
      some ["customer","invoice:" ++ toString invoice])

def admit (limit : Int) (request : Request) (candidate : Candidate request) : Except String (Approval request candidate) :=
  match inputReady : candidate.cache.closed.raw "input", invoiceReady : candidate.cache.closed.raw "invoice",
      totalReady : candidate.cache.closed.raw "total" with
  | some (.ok input),some (.ok invoice),some (.ok total) =>
    if nonnegative : 0 ≤ total then
      if within : total ≤ limit then
        if coherent : (quoteProbe candidate,reserveProbe candidate,cancelProbe candidate) =
            (some (expectedQuote request.policy input total),some (total-2,decide (2 ≤ total)),
              some ["customer","invoice:" ++ toString invoice]) then
          .ok ⟨input,invoice,total,inputReady,invoiceReady,totalReady,limit,nonnegative,within,coherent⟩
        else .error "generic-coherence"
      else .error "budget"
    else .error "negative-total"
  | _,_,_ => .error "construction-result"

abbrev Version := StagedPublication.Snapshot model Approval

def request (config : Config) (policy : Policy) : Request := ⟨ConstructionWorkflow.graph config,policy⟩

def start (config : Config) (policy : Policy) (limit : Int) :=
  (StagedPublication.start model (request config policy)
    (ConstructionCache.Builder.guarded (request config policy).graph (fun _ => true)) (admit limit)).map
      fun prepared => prepared.snapshot model

def revise (old : Version) (edits : List Edit) (allow : String → Bool) (limit : Int) :=
  StagedPublication.publish model old edits
    (ConstructionCache.Builder.guarded (redefine old.request edits).graph allow) (admit limit)

def failureTag : StagedPublication.Failure (BuildError := String) (AdmissionError := String) model → String
  | .schedule (.opaque _) => "opaque"
  | .schedule (.dependency (.blocked _)) => "cycle"
  | .schedule (.dependency (.unknownDependency _ _)) => "unknown"
  | .schedule (.dependency (.invalidOrder _)) => "order"
  | .construction (.build key _) => "builder:" ++ key
  | .construction (.dependency key) => "unready:" ++ key
  | .construction .incomplete => "incomplete"
  | .generic (.registration key _) => "registration:" ++ reprStr key
  | .generic (.negative key _ _) => "negative:" ++ reprStr key
  | .generic .incomplete => "family-incomplete"
  | .admission _ _ error => error

/-- Cross-generic approval is retained as a kernel equality on the actual family. -/
theorem coherent (version : Version) :
    (quoteProbe version.candidate,reserveProbe version.candidate,cancelProbe version.candidate) =
      (some (expectedQuote version.request.policy version.approval.input version.approval.total),
        some (version.approval.total-2,decide (2 ≤ version.approval.total)),
        some ["customer","invoice:" ++ toString version.approval.invoice]) := version.approval.coherent

end LeanPoo.Functional.ServiceBundle
