import LeanPoo.Functional.GeneralizedMOP
import LeanPoo.Object.MultimethodCombination
import LeanPoo.Object.SimplePolicies

/-! A multi-level settlement workflow exercising automatic generalized closure,
reflection, policy changes and joint graph/dispatch migration. Future work. -/
namespace LeanPoo.Functional.ConstructionWorkflow
open GeneralizedGraph GeneralizedMOP Object DispatchExtension

abbrev Values (_ : String) := Int
abbrev Raw := State String Values
abbrev Node (key : String) := Code String Values key

structure Config where
  input : Int
  discount : Option Int := none
  blocked : Bool := false
  expanded : Bool := false
  invoiceFee : Int := 0
  permit : Bool := false
  deriving Repr

inductive Policy where
  | aggregate
  | peak
  | malformed
  deriving Repr, BEq, DecidableEq

structure Interface where
  layout : String
  state : Raw

structure Call where
  service : String
  region : String
  units : Int
  deriving Repr

abbrev Action := Except String
abbrev Method := MethodCombination.SimpleContribution Call Action Int Int

def need (key : String) (transform : Int → Int) : Node target :=
  .need key fun _ value => value.map transform

def both (left right : String) (combine : Int → Int → Int) : Node target :=
  .both (.need left fun _ value => value) (.need right fun _ value => value)
    fun _ l r => do return combine (← l) (← r)

def codes (config : Config) (key : String) : Option (Node key) :=
  match key with
  | "freight" => some (need "input" fun value => 2 + value / 5)
  | "cover" => some (need "input" fun value => 3 + value / 7)
  | "reserve" => some (if config.expanded then
      .both (both "freight" "cover" (fun l r => 10*l+r))
        (.read "discount" fun _ value => value.getD (.ok 0))
        (fun _ reserve discount => do return (← reserve) - (← discount))
    else both "freight" "cover" (fun l r => 10*l+r))
  | "tax" => some (need "reserve" fun value => 2 + value / 5)
  | "risk" => some (.choose (.inspect "discount" fun _ present => present) (fun _ value => value)
      (need "input" fun value => value / 3) (need "input" fun value => value / 6))
  | "settlement" => some (both "tax" "risk" (· + ·))
  | "invoice" => some (need "settlement" fun value => value + config.invoiceFee)
  | "audit" => some (need "input" fun value => 1 + value / 4)
  | "release" => some (both "invoice" "audit" (· + ·))
  | "gate" => some (.deny "blocked" fun _ => .ok 0)
  | "total" => some (both "release" "gate" (· + ·))
  | _ => none

def keys : List String := ["total","release","invoice","settlement","tax","risk","reserve",
  "freight","cover","audit","gate","input","discount","blocked","permit"]

def graph (config : Config) : GeneralizedGraph.Declaration String Values :=
  ⟨keys, codes config, fun key =>
    if key == "input" then some (.ok config.input)
    else if key == "discount" then config.discount.map Except.ok
    else if key == "blocked" && config.blocked then some (.ok 1)
    else if key == "permit" && config.permit then some (.ok 1)
    else none⟩

def shape (call : Call) : List (List String) :=
  [if call.service == "Forbidden" then ["Forbidden"] else [call.service,"Service"],
    [call.region,"Region"]]

def selected (state : Raw) (key : String) : Action Int :=
  match state key with
  | none => .error ("missing:" ++ key)
  | some (.error error) => .error (reprStr error)
  | some (.ok value) => .ok value

def charge (state : Raw) (key : String) (call : Call) : Action Int :=
  if call.units < 0 then .error "units" else (selected state key).map (· * call.units)

def policy : Policy → MethodCombination.SimplePolicy Int Int Int
  | .aggregate | .malformed => .sum Int
  | .peak => { MethodCombination.SimplePolicy.sum Int with
      step := max }

def model : Model String Values Policy Interface Call Method (Action Int) where
  cook := fun policy raw => ⟨if policy == .aggregate then "settlement/v1" else "settlement/v2", raw⟩
  view := fun _ cooked => cooked.state
  compatible := fun _ _ => rfl
  seed := fun selectedPolicy _ => Multimethod.simple (if selectedPolicy == .malformed then 3 else 2) shape (policy selectedPolicy)
  seedEmpty := fun _ _ => rfl
  methods := fun selectedPolicy cooked =>
    [.register [.prototype "Service",.any] (.item (charge cooked.state "input")),
     .register [.prototype "Delivery",.any] (.item (charge cooked.state "total")),
     .registerWhen [.prototype "Delivery",.prototype "EU"] (fun call => call.units > 0)
       (.item fun call => .ok (2 * call.units)),
     .contribute [.prototype "Service",.any] (.around fun next _ =>
       (next ()).map (· + if selectedPolicy == .aggregate then 7 else 11))] ++
    if (cooked.state "permit").isSome then
      [.register [.prototype "Forbidden",.any] (.item fun _ => .ok 999)] else []

def watches : List (Watch Call) := [.shape [["Forbidden"],["EU","Region"]],
  .call ⟨"Forbidden","US",0⟩]

def failureTag : GeneralizedMOP.Failure (Key := String) (Method := Method) (Result := Action Int) watches → String
  | .construction (.opaque _) => "opaque"
  | .construction (.dependency (.unknownDependency _ _)) => "unknown"
  | .construction (.dependency (.blocked _)) => "cycle"
  | .construction (.dependency (.invalidOrder _)) => "order"
  | .registration _ => "arity"
  | .negative _ _ => "negative"

abbrev Built := Prepared model watches

def request (config : Config) (policy : Policy) : Request String Values Policy := ⟨graph config,policy⟩

/-- Admission is bound to the exact new graph, not a stale old total. -/
structure Approval (built : Built) where
  total : Int
  ready : built.interface.state "total" = some (.ok total)
  nonnegative : 0 ≤ total
  limit : Int
  within : total ≤ limit

def admit (limit : Int) (built : Built) : Except String (Approval built) :=
  match ready : built.interface.state "total" with
  | none => .error "missing:total"
  | some (.error error) => .error (reprStr error)
  | some (.ok total) =>
    if nonnegative : 0 ≤ total then
      if within : total ≤ limit then .ok ⟨total,ready,nonnegative,limit,within⟩
      else .error "budget"
    else .error "negative-total"

abbrev Version := Snapshot model watches Approval

def start (config : Config) (policy : Policy) (limit : Int) :=
  (stage model watches (request config policy) (admit limit)).map fun revision => revision.snapshot

/-- Exercise cache evolution while retaining the graph, policy and provenance. -/
def warm (version : Version) (call : Call) : Except String (Action Int × Version) :=
  match version.built.invoke model watches call with
  | .error error => .error (reprStr error)
  | .ok (result,built) => match admit version.approval.limit built with
    | .error error => .error error
    | .ok approval => .ok (result,⟨built,approval⟩)

def migrate (old : Version) (edits : List (Redefinition String Values Policy)) (limit : Int) :=
  revise model watches old edits (admit limit)

def publicationTag : GeneralizedMOP.PublicationError (AdmissionError := String) model watches → String
  | .preparation error => failureTag error
  | .admission _ error => error

/-- The public interface is closed under the actual selected generalized protocol. -/
theorem closed (built : Built) :
    (built.request.graph.protocol.reindexSelf (model.view built.request.policy)
      (model.cook built.request.policy)).step built.request.graph.keys built.closed.raw
        built.request.graph.base = built.closed.raw := built.closed.fixed

/-- Inferred metadata records both conditional branches and absence observations. -/
theorem risk_reads (config : Config) :
    (graph config).reads "risk" = ["input","input","discount"] := rfl

theorem gate_forbidden (config : Config) :
    ((graph config).footprint "gate").forbidden = ["blocked"] := rfl

/-- A source removal remains distinguishable from a present component failure. -/
theorem removed (config : Config) :
    ((graph config).remove "input").resolve "input" (fun _ => none) = none := rfl

/-- Source-level invoice replacement retains every transitively unaffected
component of any newly closed candidate. This instantiates inferred locality;
clients do not provide a final result equality. -/
theorem invoice_edit_retains (config : Config) (scheduled : Scheduled (graph config))
    (code : Node "invoice")
    (candidate : Prototype.Generalized.Closed ((graph config).define "invoice" code).protocol
      ((graph config).define "invoice" code).keys ((graph config).define "invoice" code).base)
    (key : String) (safe : scheduled.invalidates (· == "invoice") key = false) :
    candidate.raw key = scheduled.closed.raw key := by
  apply scheduled.unaffected (· == "invoice") _ candidate key safe
  intro query unchanged self
  apply (graph config).define_resolve_frame "invoice" query code _ self
  intro same
  subst query
  simp at unchanged

end LeanPoo.Functional.ConstructionWorkflow
