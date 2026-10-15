import LeanPoo.Functional.ServiceBundle

/-! Declarative type refinements and relational logic on an actual selectively
constructed, heterogeneous service family. Generalized-MOP future work. -/
namespace LeanPoo.Functional.ServiceMetadata
open ServiceBundle DeclarativeMetadata

inductive Atom where
  | conservation
  | permission
  deriving Repr, DecidableEq

/-- A positive reservation has an actual Except result carrier. A source-level
error is not confused with an outer dispatch failure or accepted by the type
refinement; conservation relates this result to this call's units and capacity. -/
def reservation (capacity : Int) : Contract Atom Nat (ConstructionWorkflow.Action (Int × Bool)) where
  input := ⟨"positive-units",fun units => 0 < units,fun _ => inferInstance⟩
  output := ⟨"successful-reservation",fun result => match result with
    | .error _ => False
    | .ok (remaining,_) => 0 ≤ remaining,fun result => by cases result <;> exact inferInstance⟩
  meaning atom units result := match atom with
    | .conservation => match result with
      | .error _ => False
      | .ok pair => pair = (capacity-(units : Int),true)
    | .permission => (units : Int) ≤ capacity
  decide atom units result := by
    cases atom with
    | conservation => cases result <;> exact inferInstance
    | permission => exact inferInstance
  rule := .both (.atom .permission) (.atom .conservation)

/-- A receipt grants a universal consumer law for any checked invocation, rather
than extrapolating from the publication's fixed reserve probe. -/
theorem reservation_conservation (capacity : Int)
    {execute : Nat → Except Error (ConstructionWorkflow.Action (Int × Bool) × State)} {units : Nat}
    (receipt : Invocation (reservation capacity) execute units) :
    receipt.result = .ok (capacity-(units : Int),true) ∧ (units : Int) ≤ capacity :=
  by
    refine ⟨?_,receipt.logic.1⟩
    have conserved := receipt.logic.2
    cases found : receipt.result with
    | error error => simp [reservation, found, Formula.Holds] at conserved
    | ok pair =>
      have same : pair = (capacity-(units : Int),true) := by
        simpa [reservation, found, Formula.Holds] using conserved
      simp [found, same]

inductive ReleaseAtom where
  | quoteBound
  | reserveLinked
  | cancelLinked
  | distinctNames
  deriving Repr, DecidableEq

/-- All atoms inspect the completed candidate or its exact declaration source. -/
def meaning (ceiling : Int) (current : Request) (candidate : Candidate current) : ReleaseAtom → Prop
  | .quoteBound => match quoteProbe candidate with
    | none => False
    | some quote => 0 ≤ quote ∧ quote ≤ ceiling
  | .reserveLinked => match candidate.cache.closed.raw "total" with
    | some (.ok capacity) => reserveProbe candidate = some (capacity-2,decide (2 ≤ capacity))
    | _ => False
  | .cancelLinked => match candidate.cache.closed.raw "invoice" with
    | some (.ok invoice) => cancelProbe candidate = some ["customer","invoice:" ++ toString invoice]
    | _ => False
  | .distinctNames => [Service.quote,.reserve,.cancel].all (fun key =>
      decide (((declarations key current.policy candidate.interface).map Declaration.name).Nodup)) = true

instance (ceiling : Int) (current : Request) (candidate : Candidate current) :
    DecidablePred (meaning ceiling current candidate) := fun atom => by
  cases atom with
  | quoteBound => simp only [meaning]; split <;> exact inferInstance
  | reserveLinked => simp only [meaning]; split <;> exact inferInstance
  | cancelLinked => simp only [meaning]; split <;> exact inferInstance
  | distinctNames => exact inferInstanceAs (Decidable (_ = true))

def releaseRule : Formula ReleaseAtom :=
  .both (.atom .distinctNames)
    (.both (.atom .quoteBound) (.both (.atom .reserveLinked) (.atom .cancelLinked)))

/-- The existing graph/business approval is combined with interpreted logical
metadata on this exact family, without a second publication mechanism. -/
structure Approval (ceiling : Int) (current : Request) (candidate : Candidate current) where
  business : ServiceBundle.Approval current candidate
  metadata : Evidence (meaning ceiling current candidate) releaseRule

def admit (limit ceiling : Int) (current : Request) (candidate : Candidate current) :
    Except String (Approval ceiling current candidate) :=
  match ServiceBundle.admit limit current candidate with
  | .error error => .error error
  | .ok business => match releaseRule.check (meaning ceiling current candidate) with
    | .error _ => .error "release-metadata"
    | .ok metadata => .ok ⟨business,metadata⟩

abbrev Version (ceiling : Int) := StagedPublication.Snapshot model (Approval ceiling)

def start (config : ConstructionWorkflow.Config) (policy : Policy) (limit ceiling : Int) :=
  (StagedPublication.start model (request config policy)
    (ConstructionCache.Builder.guarded (request config policy).graph (fun _ => true)) (admit limit ceiling)).map
      fun prepared => prepared.snapshot model

def revise (old : Version ceiling) (edits : List Edit) (allow : String → Bool) (limit : Int) :=
  StagedPublication.publish model old edits
    (ConstructionCache.Builder.guarded (GeneralizedMOP.redefine old.request edits).graph allow) (admit limit ceiling)

/-- Check the actual staged invocation: its returned snapshot has fresh exact-
candidate business and logical approval, plus the existing family cache laws. -/
def reserve (version : Version ceiling) (units : Nat) :=
  (reservation version.approval.business.total).invoke
    (fun args => version.invoke model .reserve args (admit version.approval.business.limit ceiling)) units

/-- Accepted calls retain graph construction and request identities even though
one generic's cache and all candidate-bound approvals have been refreshed. -/
theorem reserve_construction (version : Version ceiling) (units : Nat)
    (receipt : Invocation (reservation version.approval.business.total)
      (fun args => version.invoke model .reserve args (admit version.approval.business.limit ceiling)) units) :
    receipt.state.request = version.request ∧
      receipt.state.candidate.cache.closed.raw = version.candidate.cache.closed.raw ∧
      receipt.state.candidate.cache.evaluated = version.candidate.cache.evaluated ∧
      receipt.state.candidate.cache.reused = version.candidate.cache.reused :=
  StagedPublication.Snapshot.invoke_construction model version .reserve units _ _ _ receipt.called

theorem release_quote_bound (version : Version ceiling) :
    meaning ceiling version.request version.candidate .quoteBound := version.approval.metadata.valid.2.1

theorem release_reserve_linked (version : Version ceiling) :
    meaning ceiling version.request version.candidate .reserveLinked := version.approval.metadata.valid.2.2.1

/-- Published (including warmed) methods originate in the exact declarative
source, cooked construction and policy; metadata is not a detached manifest. -/
theorem declared_origin (version : Version ceiling) (key : Service)
    (generic : Object.Multimethod (Args key) (Method key) (Result key))
    (found : version.candidate.family.table.get? key = some generic) :
    ∃ cold, DeclarativeMetadata.install
        (seed key version.request.policy version.candidate.interface)
        (declarations key version.request.policy version.candidate.interface) = .ok cold ∧
      GeneralizedMOP.definition generic = GeneralizedMOP.definition cold :=
  (version.candidate.family.certified key generic found).origin

end LeanPoo.Functional.ServiceMetadata
