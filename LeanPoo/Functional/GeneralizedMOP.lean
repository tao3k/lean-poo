import LeanPoo.Functional.GeneralizedGraph
import LeanPoo.Functional.DispatchExtension

/-! A checked MOP over finite generalized component declarations. Policy values
select actual cooked interfaces and existing multimethod combiners. Candidates
are rebuilt from declarations, checked, admitted and published as one version.
This is research into the generalized-prototype future work. -/
namespace LeanPoo.Functional.GeneralizedMOP
open GeneralizedGraph Object DispatchExtension

/-- Policy hooks are explicit typed functions, not inferred metadata about
arbitrary Lean callbacks. All method declarations are rebuilt after graph edits. -/
structure Model (Key : Type) (Value : Key → Type) (Policy Cooked Args Method Result : Type) where
  cook : Policy → State Key Value → Cooked
  view : Policy → Cooked → State Key Value
  compatible : ∀ policy raw, view policy (cook policy raw) = raw
  seed : Policy → Cooked → Multimethod Args Method Result
  seedEmpty : ∀ policy cooked, (seed policy cooked).cache = {}
  methods : Policy → Cooked → List (Edit Args Method)

structure Request (Key : Type) (Value : Key → Type) (Policy : Type) where
  graph : GeneralizedGraph.Declaration Key Value
  policy : Policy

variable {Key : Type} {Value : Key → Type} {Policy Cooked Args Method Result : Type}
variable [DecidableEq Key] [BEq Key] [LawfulBEq Key] [Hashable Key]
variable (model : Model Key Value Policy Cooked Args Method Result)
variable (watches : List (Watch Args))

/-- Typed edits target the complete construction request. Support edits are
explicit so removing a provider can retain a watched absent key. -/
inductive Redefinition (Key : Type) (Value : Key → Type) (Policy : Type) where
  | define (key : Key) (code : Code Key Value key)
  | remove (key : Key)
  | setBase (key : Key) (value : Option (Outcome Key Value key))
  | support (keys : List Key)
  | policy (value : Policy)

def Redefinition.apply (edit : Redefinition Key Value Policy) (request : Request Key Value Policy) :
    Request Key Value Policy :=
  match edit with
  | .define key code => {request with graph := request.graph.define key code}
  | .remove key => {request with graph := request.graph.remove key}
  | .setBase key value => {request with graph := request.graph.setBase key value}
  | .support keys => {request with graph := {request.graph with keys}}
  | .policy value => {request with policy := value}

def redefine (request : Request Key Value Policy) (edits : List (Redefinition Key Value Policy)) :
    Request Key Value Policy := edits.foldl (fun current edit => edit.apply current) request

/-- Cache contents may evolve; the complete dispatch definition remains bound
by equality to the method declarations compiled for this exact construction. -/
def definition (generic : Multimethod Args Method Result) : Multimethod Args Method Result :=
  { generic with cache := {} }

structure Prepared where
  request : Request Key Value Policy
  scheduled : Scheduled request.graph
  generic : Multimethod Args Method Result
  origin : ∃ cold, patch (model.seed request.policy (model.cook request.policy scheduled.closed.raw))
      (model.methods request.policy (model.cook request.policy scheduled.closed.raw)) = .ok cold ∧
    definition generic = definition cold
  negative : Certificate generic watches
  sound : generic.CacheSound

/-- The compiled graph is a closed generalized protocol at the selected public
interface, including a nonidentity representation or additional public data. -/
def Prepared.closed (built : Prepared model watches) :
    Prototype.Generalized.Closed
      (built.request.graph.protocol.reindexSelf (model.view built.request.policy)
        (model.cook built.request.policy)) built.request.graph.keys built.request.graph.base :=
  ⟨built.scheduled.closed.raw, by
    rw [Prototype.Generalized.Protocol.step_reindexSelf _ _ _ (model.compatible built.request.policy)]
    exact built.scheduled.closed.fixed⟩

def Prepared.interface (built : Prepared model watches) : Cooked := built.closed.interface

structure Metadata (Key Policy : Type) where
  policy : Policy
  nodes : List (Key × DependencyFootprint Key)
  order : List Key
  arity : Nat
  declarations : Nat

def Prepared.inspect (built : Prepared model watches) : Metadata Key Policy :=
  ⟨built.request.policy, built.request.graph.keys.map (fun key => (key, built.request.graph.footprint key)),
    built.scheduled.order, built.generic.arity, (model.methods built.request.policy built.interface).length⟩

inductive Failure where
  | construction (error : GeneralizedGraph.Error Key)
  | registration (error : MultimethodError)
  | negative (candidate : Multimethod Args Method Result) (conflict : Conflict candidate watches)

/-- The finite graph, public interface, actual policy and method index are
constructed together. Negative watches inspect the completed candidate. -/
def prepare (request : Request Key Value Policy) :
    Except (Failure (Key := Key) (Method := Method) (Result := Result) watches) (Prepared model watches) :=
  match request.graph.schedule with
  | .error error => .error (.construction error)
  | .ok scheduled =>
    let cooked := model.cook request.policy scheduled.closed.raw
    match applied : patch (model.seed request.policy cooked) (model.methods request.policy cooked) with
    | .error error => .error (.registration error)
    | .ok candidate => match check candidate watches with
      | .error conflict => .error (.negative candidate conflict)
      | .ok certificate => .ok ⟨request, scheduled, candidate, ⟨candidate, applied, rfl⟩, certificate,
          patch_sound _ _ _ ((model.seed request.policy cooked).cacheSound_of_empty
            (model.seedEmpty request.policy cooked)) applied⟩

/-- Calling a prepared version changes only its cache, preserving provenance. -/
theorem call_definition (generic updated : Multimethod Args Method Result) (args : Args) (result : Result)
    (called : generic.call args = .ok (result, updated)) : definition updated = definition generic := by
  cases resolved : generic.resolve args with
  | error error => simp [Multimethod.call, resolved, bind, Except.bind] at called
  | ok pair =>
    rcases pair with ⟨candidates, next⟩
    have nextEq : next = updated := by
      have pairEq : generic.combine (MethodCandidate.select candidates args) args = result ∧ next = updated := by
        simpa [Multimethod.call, resolved, bind, Except.bind, pure, Except.pure] using called
      exact pairEq.2
    subst updated
    unfold Multimethod.resolve at resolved
    simp only [bind, Except.bind, pure, Except.pure, throw] at resolved
    repeat' first | contradiction | split at resolved
    all_goals cases resolved; rfl

/-- Warm a published construction using ordinary multimethod invocation. -/
def Prepared.invoke (built : Prepared model watches) (args : Args) :
    Except MultimethodError (Result × Prepared model watches) :=
  match called : built.generic.call args with
  | .error error => .error error
  | .ok (result, updated) => .ok (result, {
      built with
      generic := updated
      origin := by
        obtain ⟨cold, generated, same⟩ := built.origin
        exact ⟨cold, generated, (call_definition built.generic updated args result called).trans same⟩
      negative := built.negative.afterCall args result updated called
      sound := built.generic.call_preserves built.sound args result updated called })

omit [BEq Key] [LawfulBEq Key] [Hashable Key] in
/-- Warm-cache evolution cannot change the cooked graph or selected policy. -/
theorem Prepared.invoke_interface (built : Prepared model watches) (args : Args) (result : Result)
    (next : Prepared model watches)
    (called : built.invoke model watches args = .ok (result,next)) :
    next.interface = built.interface ∧ next.request = built.request := by
  unfold Prepared.invoke at called
  split at called
  · contradiction
  · cases called; exact ⟨rfl,rfl⟩

variable {Approved : Prepared model watches → Type} {AdmissionError : Type}

structure Snapshot (Approved : Prepared model watches → Type) where
  built : Prepared model watches
  approval : Approved built

inductive PublicationError where
  | preparation (error : Failure (Key := Key) (Method := Method) (Result := Result) watches)
  | admission (candidate : Prepared model watches) (error : AdmissionError)

structure Revision (request : Request Key Value Policy)
    (admit : (candidate : Prepared model watches) → Except AdmissionError (Approved candidate)) where
  snapshot : Snapshot model watches Approved
  requested : snapshot.built.request = request
  admitted : admit snapshot.built = .ok snapshot.approval

/-- Whole-construction migration may replace topology, code, base, public
layout, policy and methods. No final provider or closure witness is supplied. -/
def stage (request : Request Key Value Policy)
    (admit : (candidate : Prepared model watches) → Except AdmissionError (Approved candidate)) :
    Except (PublicationError (AdmissionError := AdmissionError) model watches)
      (Revision model watches request admit) :=
  match built : prepare model watches request with
  | .error error => .error (.preparation error)
  | .ok candidate => match admitted : admit candidate with
    | .error error => .error (.admission candidate error)
    | .ok approval => .ok ⟨⟨candidate, approval⟩, by
        unfold prepare at built
        split at built <;> try contradiction
        dsimp only at built
        split at built <;> try contradiction
        split at built <;> try contradiction
        cases built; rfl, admitted⟩

def publish (old : Snapshot model watches Approved) (request : Request Key Value Policy)
    (admit : (candidate : Prepared model watches) → Except AdmissionError (Approved candidate)) :=
  let outcome := stage model watches request admit
  (outcome, match outcome with | .error _ => old | .ok revision => revision.snapshot)

theorem publish_refused (old : Snapshot model watches Approved) (request admit)
    (error : PublicationError (AdmissionError := AdmissionError) model watches)
    (refused : stage model watches request admit = .error error) :
    (publish model watches old request admit).2 = old := by simp [publish, refused]

theorem publish_accepted (old : Snapshot model watches Approved) (request admit)
    (revision : Revision (AdmissionError := AdmissionError) model watches request admit)
    (accepted : stage model watches request admit = .ok revision) :
    (publish model watches old request admit).2 = revision.snapshot := by simp [publish, accepted]

/-- Apply source edits to the old declaration, reconstruct closure and dispatch,
then atomically publish the complete accepted version. -/
def revise (old : Snapshot model watches Approved) (edits : List (Redefinition Key Value Policy))
    (admit : (candidate : Prepared model watches) → Except AdmissionError (Approved candidate)) :=
  publish model watches old (redefine old.built.request edits) admit

theorem revise_refused (old : Snapshot model watches Approved) (edits admit)
    (error : PublicationError (AdmissionError := AdmissionError) model watches)
    (refused : stage model watches (redefine old.built.request edits) admit = .error error) :
    (revise model watches old edits admit).2 = old :=
  publish_refused model watches old _ admit error refused

omit [BEq Key] [LawfulBEq Key] [Hashable Key] in
/-- Accepted calls use the existing uncached ordered dispatch semantics. -/
theorem Prepared.call_correct (built : Prepared model watches) (args : Args) :
    (built.generic.call args).map Prod.fst = built.generic.referenceCall args :=
  built.generic.call_correct built.sound args

end LeanPoo.Functional.GeneralizedMOP
