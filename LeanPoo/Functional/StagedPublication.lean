import LeanPoo.Functional.ConstructionCache
import LeanPoo.Functional.GenericFamily

/-! Selective materialized graph construction followed by atomic publication of
a heterogeneous generic family with joint admission. Generalized-MOP future work. -/
namespace LeanPoo.Functional.StagedPublication
open GeneralizedGraph GeneralizedMOP

structure Model (Key : Type) (Value : Key → Type) (G Policy Cooked : Type) (Args Method Result : G → Type) where
  cook : Policy → State Key Value → Cooked
  generics : GenericFamily.Model G Policy Cooked Args Method Result

variable {Key : Type} {Value : Key → Type} {G Policy Cooked : Type} {Args Method Result : G → Type}
variable [DecidableEq Key] [BEq Key] [LawfulBEq Key] [Hashable Key]
variable [DecidableEq G] [BEq G] [LawfulBEq G] [Hashable G]
variable (model : Model Key Value G Policy Cooked Args Method Result)

structure Candidate (request : Request Key Value Policy) where
  cache : ConstructionCache.Cache request.graph
  family : GenericFamily.Family model.generics request.policy (model.cook request.policy cache.closed.raw)

def Candidate.interface {request : Request Key Value Policy} (candidate : Candidate model request) : Cooked :=
  model.cook request.policy candidate.cache.closed.raw

/-- Raw closure belongs to materialized construction. Public cooking may discard
information and needs no inverse. Cooked-self closure, when needed, requires
separate evidence that the graph's actual reads survive that projection. -/
def Candidate.closed {request : Request Key Value Policy} (candidate : Candidate model request) :
    Prototype.Generalized.Closed request.graph.protocol request.graph.keys request.graph.base :=
  candidate.cache.closed

variable {Approved : (request : Request Key Value Policy) → Candidate model request → Type}
variable {BuildError AdmissionError : Type}

structure Snapshot (Approved : (request : Request Key Value Policy) → Candidate model request → Type) where
  request : Request Key Value Policy
  candidate : Candidate model request
  approval : Approved request candidate

structure Prepared (request : Request Key Value Policy)
    (admit : (request : Request Key Value Policy) → (candidate : Candidate model request) →
      Except AdmissionError (Approved request candidate)) where
  candidate : Candidate model request
  approval : Approved request candidate
  admitted : admit request candidate = .ok approval

inductive Failure where
  | schedule (error : GeneralizedGraph.Error Key)
  | construction (error : ConstructionCache.Failure Key BuildError)
  | generic (error : GenericFamily.Failure model.generics)
  | admission (request : Request Key Value Policy) (candidate : Candidate model request) (error : AdmissionError)

def finish (request : Request Key Value Policy) (cache : ConstructionCache.Cache request.graph)
    (admit : (request : Request Key Value Policy) → (candidate : Candidate model request) →
      Except AdmissionError (Approved request candidate)) :
    Except (Failure (BuildError := BuildError) (AdmissionError := AdmissionError) model) (Prepared model request admit) :=
  match GenericFamily.build model.generics request.policy (model.cook request.policy cache.closed.raw) with
  | .error error => .error (.generic error)
  | .ok family =>
    let candidate : Candidate model request := ⟨cache,family⟩
    match admitted : admit request candidate with
    | .error error => .error (.admission request candidate error)
    | .ok approval => .ok ⟨candidate,approval,admitted⟩

omit [BEq Key] [LawfulBEq Key] [Hashable Key] in
/-- Family construction/admission never changes the supplied materialized
construction. Alternative certified closure algorithms may reuse this boundary. -/
theorem finish_cache (request : Request Key Value Policy) (cache : ConstructionCache.Cache request.graph)
    (admit : (request : Request Key Value Policy) → (candidate : Candidate model request) →
      Except AdmissionError (Approved request candidate))
    (prepared : Prepared model request admit)
    (accepted : finish (BuildError := BuildError) model request cache admit = .ok prepared) :
    prepared.candidate.cache = cache := by
  unfold finish at accepted
  split at accepted
  · contradiction
  · dsimp only at accepted
    split at accepted
    · contradiction
    · cases accepted; rfl

def start (request : Request Key Value Policy) (builder : ConstructionCache.Builder request.graph BuildError)
    (admit : (request : Request Key Value Policy) → (candidate : Candidate model request) →
      Except AdmissionError (Approved request candidate)) :
    Except (Failure (BuildError := BuildError) (AdmissionError := AdmissionError) model) (Prepared model request admit) :=
  match request.graph.schedule with
  | .error error => .error (.schedule error)
  | .ok scheduled => match ConstructionCache.start scheduled builder with
    | .error error => .error (.construction error)
    | .ok cache => finish model request cache admit

/-- Typed edit frames generate the unchanged-resolver certificate. Support edits
conservatively invalidate all nodes; policy-only edits retain the entire graph. -/
def stage (old : Snapshot model Approved) (edits : List (Redefinition Key Value Policy))
    (builder : ConstructionCache.Builder (redefine old.request edits).graph BuildError)
    (admit : (request : Request Key Value Policy) → (candidate : Candidate model request) →
      Except AdmissionError (Approved request candidate)) :
    Except (Failure (BuildError := BuildError) (AdmissionError := AdmissionError) model)
      (Prepared model (redefine old.request edits) admit) :=
  let request := redefine old.request edits
  match request.graph.schedule with
  | .error error => .error (.schedule error)
  | .ok scheduled => match ConstructionCache.refresh scheduled old.candidate.cache
      (ConstructionCache.changed edits) (ConstructionCache.redefine_unchanged old.request edits) builder with
    | .error error => .error (.construction error)
    | .ok cache => finish model request cache admit

def Prepared.snapshot {request : Request Key Value Policy} {admit}
    (prepared : Prepared (Approved := Approved) (AdmissionError := AdmissionError) model request admit) :
    Snapshot model Approved := ⟨request,prepared.candidate,prepared.approval⟩

def publish (old : Snapshot model Approved) (edits : List (Redefinition Key Value Policy))
    (builder : ConstructionCache.Builder (redefine old.request edits).graph BuildError)
    (admit : (request : Request Key Value Policy) → (candidate : Candidate model request) →
      Except AdmissionError (Approved request candidate)) :=
  let outcome := stage model old edits builder admit
  (outcome,match outcome with | .error _ => old | .ok prepared => prepared.snapshot model)

theorem publish_refused (old : Snapshot model Approved) (edits builder admit)
    (error : Failure (BuildError := BuildError) (AdmissionError := AdmissionError) model)
    (refused : stage model old edits builder admit = .error error) :
    (publish model old edits builder admit).2 = old := by simp [publish,refused]

theorem publish_accepted (old : Snapshot model Approved) (edits : List (Redefinition Key Value Policy))
    (builder : ConstructionCache.Builder (redefine old.request edits).graph BuildError) (admit)
    (prepared : Prepared (Approved := Approved) (AdmissionError := AdmissionError) model (redefine old.request edits) admit)
    (accepted : stage model old edits builder admit = .ok prepared) :
    (publish model old edits builder admit).2 = prepared.snapshot model := by simp [publish,accepted]

/-- Warm any signature using the existing table machinery, then recheck the
application's joint approval for the actual updated family. -/
def Snapshot.invoke (old : Snapshot model Approved) (key : G) (args : Args key)
    (admit : (request : Request Key Value Policy) → (candidate : Candidate model request) →
      Except AdmissionError (Approved request candidate)) :
    Except (Sum (Object.DispatchTableError G) AdmissionError) (Result key × Snapshot model Approved) :=
  match old.candidate.family.invoke model.generics old.request.policy old.candidate.interface key args with
  | .error error => .error (.inl error)
  | .ok (result,family) =>
    let candidate : Candidate model old.request := ⟨old.candidate.cache,family⟩
    match admit old.request candidate with
    | .error error => .error (.inr error)
    | .ok approval => .ok (result,⟨old.request,candidate,approval⟩)

omit [BEq Key] [LawfulBEq Key] [Hashable Key] in
/-- Ordinary generic invocation does not rerun or replace graph construction. -/
theorem Snapshot.invoke_construction (old : Snapshot model Approved) (key : G) (args : Args key)
    (admit : (request : Request Key Value Policy) → (candidate : Candidate model request) →
      Except AdmissionError (Approved request candidate))
    (result : Result key) (next : Snapshot model Approved)
    (called : old.invoke model key args admit = .ok (result,next)) :
    next.request = old.request ∧ next.candidate.cache.closed.raw = old.candidate.cache.closed.raw ∧
      next.candidate.cache.evaluated = old.candidate.cache.evaluated ∧
      next.candidate.cache.reused = old.candidate.cache.reused := by
  unfold Snapshot.invoke at called
  split at called
  · contradiction
  · dsimp only at called
    split at called
    · contradiction
    · cases called
      exact ⟨rfl,rfl,rfl,rfl⟩

end LeanPoo.Functional.StagedPublication
