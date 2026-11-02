import LeanPoo.Functional.GeneralizedFragments
import LeanPoo.Functional.GeneralizedMOP
import LeanPoo.Prototype.C3DAG

/-! Source inheritance, analyzed super fragments, graph closure and protected
multimethod publication form one checked generalized-prototype future-work path. -/
namespace LeanPoo.Functional.InheritedMOP
open GeneralizedGraph GeneralizedMOP GeneralizedFragments

structure Source (Key : Type) (Value : Key → Type) (Policy : Type) where
  graph : Prototype.C3.Graph
  root : String
  declarations : String → List (Binding Key Value)
  keys : List Key
  base : State Key Value
  policy : Policy

variable {Key : Type} {Value : Key → Type} {Policy Cooked Args Method Result : Type}
variable [DecidableEq Key] [BEq Key] [LawfulBEq Key] [Hashable Key]
variable (model : Model Key Value Policy Cooked Args Method Result)
variable (watches : List (DispatchExtension.Watch Args))

/-- C3 order fixes both ancestor order and within-class declaration order. -/
def Source.request (source : Source Key Value Policy) (order : List String) : Request Key Value Policy :=
  ⟨declaration source.keys source.base (order.flatMap source.declarations),source.policy⟩

variable {Approved : GeneralizedMOP.Prepared model watches → Type} {AdmissionError : Type}

structure Snapshot (Approved : GeneralizedMOP.Prepared model watches → Type) where
  source : Source Key Value Policy
  order : List String
  valid : Prototype.C3.linearize source.graph source.root = .ok order
  version : GeneralizedMOP.Snapshot model watches Approved
  compiled : version.built.request = source.request order

omit [BEq Key] [LawfulBEq Key] [Hashable Key] in
/-- The source-order proof concerns the actual graph used by this version. -/
theorem Snapshot.derivation (snapshot : Snapshot model watches Approved) :
    Prototype.C3.GraphDerivation snapshot.source.graph snapshot.source.root snapshot.order :=
  Prototype.C3.linearize_derivation _ _ _ snapshot.valid

omit [BEq Key] [LawfulBEq Key] [Hashable Key] in
/-- An independently supplied C3 derivation yields exactly the compiled request. -/
theorem Snapshot.request_reference (snapshot : Snapshot model watches Approved) (order : List String)
    (derived : Prototype.C3.GraphDerivation snapshot.source.graph snapshot.source.root order) :
    snapshot.version.built.request = snapshot.source.request order := by
  rw [← snapshot.derivation.unique derived]
  exact snapshot.compiled

structure Metadata (Key Policy : Type) where
  root : String
  order : List String
  classes : List (String × List (Key × Kind))
  components : GeneralizedMOP.Metadata Key Policy

def Snapshot.inspect (snapshot : Snapshot model watches Approved) : Metadata Key Policy :=
  ⟨snapshot.source.root,snapshot.order,snapshot.order.map (fun name =>
    (name,(snapshot.source.declarations name).map fun ⟨key,body⟩ => (key,body.kind))),
    snapshot.version.built.inspect model watches⟩

omit [BEq Key] [LawfulBEq Key] [Hashable Key] in
/-- Closure concerns the components elaborated from this exact source order. -/
theorem Snapshot.resolves (snapshot : Snapshot model watches Approved) (key : Key) :
    (snapshot.source.request snapshot.order).graph.resolve key snapshot.version.built.closed.raw =
      snapshot.version.built.closed.raw key := by
  rw [← snapshot.compiled]
  exact snapshot.version.built.scheduled.resolver.closed key

inductive Failure where
  | inheritance (error : LeanPoo.C4.Error)
  | construction (error : GeneralizedMOP.PublicationError (AdmissionError := AdmissionError) model watches)

structure Revision (source : Source Key Value Policy)
    (admit : (built : GeneralizedMOP.Prepared model watches) → Except AdmissionError (Approved built)) where
  snapshot : Snapshot model watches Approved
  sourced : snapshot.source = source
  admitted : admit snapshot.version.built = .ok snapshot.version.approval

/-- Never publish a C3 receipt from one graph with closure from another. -/
def stage (source : Source Key Value Policy)
    (admit : (built : GeneralizedMOP.Prepared model watches) → Except AdmissionError (Approved built)) :
    Except (Failure (AdmissionError := AdmissionError) model watches) (Revision model watches source admit) :=
  match valid : Prototype.C3.linearize source.graph source.root with
  | .error error => .error (.inheritance error)
  | .ok order => match GeneralizedMOP.stage model watches (source.request order) admit with
    | .error error => .error (.construction error)
    | .ok revised => .ok ⟨⟨source,order,valid,revised.snapshot,revised.requested⟩,rfl,revised.admitted⟩

theorem stage_inheritance_error (source : Source Key Value Policy) (admit)
    (error : LeanPoo.C4.Error) (failed : Prototype.C3.linearize source.graph source.root = .error error) :
    stage (AdmissionError := AdmissionError) (Approved := Approved) model watches source admit =
      .error (.inheritance error) := by
  unfold stage
  split <;> simp_all

def publish (old : Snapshot model watches Approved) (source : Source Key Value Policy)
    (admit : (built : GeneralizedMOP.Prepared model watches) → Except AdmissionError (Approved built)) :=
  let outcome := stage model watches source admit
  (outcome,match outcome with | .error _ => old | .ok revision => revision.snapshot)

theorem publish_refused (old : Snapshot model watches Approved) (source admit)
    (error : Failure (AdmissionError := AdmissionError) model watches)
    (refused : stage model watches source admit = .error error) :
    (publish model watches old source admit).2 = old := by simp [publish, refused]

theorem publish_accepted (old : Snapshot model watches Approved) (source admit)
    (revision : Revision (AdmissionError := AdmissionError) model watches source admit)
    (accepted : stage model watches source admit = .ok revision) :
    (publish model watches old source admit).2 = revision.snapshot := by simp [publish, accepted]

/-- Warm invocation retains the graph/order/source binding. Approval is checked
for the actual warmed version; no assumption about arbitrary approvals is added. -/
def Snapshot.invoke (old : Snapshot model watches Approved) (args : Args)
    (admit : (built : GeneralizedMOP.Prepared model watches) → Except AdmissionError (Approved built)) :
    Except (Sum Object.MultimethodError AdmissionError) (Result × Snapshot model watches Approved) :=
  match called : old.version.built.invoke model watches args with
  | .error error => .error (.inl error)
  | .ok (result,built) => match admit built with
    | .error error => .error (.inr error)
    | .ok approval => .ok (result,{
        old with version := ⟨built,approval⟩
                 compiled := (old.version.built.invoke_interface model watches args result built called).2.trans old.compiled })

end LeanPoo.Functional.InheritedMOP
