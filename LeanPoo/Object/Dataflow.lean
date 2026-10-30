import LeanPoo.Object.Memo
import LeanPoo.Object.StrictBuilder
import LeanPoo.Functional.GeneralizedFragments
import LeanPoo.Functional.ConstructionCache

/-! C4 definitions with inspectable typed field dependencies and materialized
instance state. Existing fragment compilation, ranked scheduling and construction
cache proofs own execution. Templates retain metadata, not instance results. -/
namespace LeanPoo.Object.Dataflow
open LeanPoo.Functional

variable {Key : Type} {Value : Key → Type}

abbrev Expr (Key : Type) (Value : Key → Type) (Result : Type) :=
  Computation Unit Key (fun _ key => GeneralizedGraph.Outcome Key Value key)
    (fun _ => Except (ComputationError Key) Result)

namespace Expr

def need (key : Key) : Expr Key Value (Value key) := Computation.need key fun _ value => value

instance : Functor (Expr Key Value) where
  map transform expression := .map expression fun _ value => value.map transform

instance : Applicative (Expr Key Value) where
  pure value := .pure fun _ => .ok value
  seq functions values := .both functions (values ()) fun _ function value => do
    let selected ← function
    value.map selected
  map transform expression := .map expression fun _ value => value.map transform

end Expr

structure Declaration (Key : Type) (Value : Key → Type) where
  fields : List (Entry Key (GeneralizedFragments.Fragment Key Value)) := []
  defaults : List (Entry Key Value) := []

abbrev Builder (Key : Type) (Value : Key → Type) := StateM (Declaration Key Value)

namespace Builder

def field [DecidableEq Key] (key : Key) (fragment : GeneralizedFragments.Fragment Key Value key) :
    Builder Key Value PUnit := modify fun declaration =>
  { declaration with fields := declaration.fields ++ [⟨key,fragment,fun _ => inferInstance⟩] }

def value [DecidableEq Key] (key : Key) (value : Value key) : Builder Key Value PUnit :=
  field key (.replace (.pure fun _ => .ok value))

def derived [DecidableEq Key] (key : Key) (expression : Expr Key Value (Value key)) :
    Builder Key Value PUnit := field key (.replace expression)

def default [DecidableEq Key] (key : Key) (value : Value key) : Builder Key Value PUnit :=
  modify fun declaration =>
    { declaration with defaults := declaration.defaults ++ [⟨key,value,fun _ => inferInstance⟩] }

def build (program : Builder Key Value PUnit) : Declaration Key Value := (program.run {}).2
end Builder

/-- C4 composes code, never component values. The fragment compiler retains
ordered/delayed inherited semantics and prunes overridden parent dependencies. -/
def Declaration.metadata (declaration : Declaration Key Value) :
    Object.Declaration Key (fun key => GeneralizedGraph.Code Key Value key) where
  slots := declaration.fields.map fun entry => {
    key := entry.key
    value := .modify fun parent => some (GeneralizedFragments.compile entry.key none
      (entry.value :: parent.toList.map GeneralizedFragments.Fragment.replace))
    decideEq := entry.decideEq }
  defaults := declaration.defaults.map fun entry => {
    key := entry.key
    value := .pure fun _ => .ok entry.value
    decideEq := entry.decideEq }

/-- One declaration owns its lowered metadata for its whole immutable lifetime.
Source extension shares previous owners rather than lowering their fields again. -/
structure PreparedDeclaration (Key : Type) (Value : Key → Type) where
  source : Declaration Key Value
  code : Object.Declaration Key (fun key => GeneralizedGraph.Code Key Value key)
  aligned : code = source.metadata

def Declaration.prepare (declaration : Declaration Key Value) : PreparedDeclaration Key Value :=
  ⟨declaration,declaration.metadata,rfl⟩

structure Source (Key : Type) (Value : Key → Type) where
  graph : C4.Graph
  prepared : String → Option (PreparedDeclaration Key Value)

def Source.empty : Source Key Value := ⟨⟨[]⟩,fun _ => none⟩

def Source.declaration (source : Source Key Value) (name : String) : Option (Declaration Key Value) :=
  (source.prepared name).map PreparedDeclaration.source

def Source.schema (source : Source Key Value) :
    Schema Key (fun key => GeneralizedGraph.Code Key Value key) :=
  ⟨source.graph,fun name => (source.prepared name).map PreparedDeclaration.code⟩

/-- The retained code is the lowering of this exact raw declaration, including
unknown-name lookup. No node label or sampled result authorizes a cache hit. -/
theorem Source.schema_declaration (source : Source Key Value) (name : String) :
    source.schema.declaration name = (source.declaration name).map Declaration.metadata := by
  cases found : source.prepared name with
  | none => simp [schema,declaration,found]
  | some prepared => simp [schema,declaration,found,prepared.aligned]

def Source.add (source : Source Key Value) (node : C4.Node) (declaration : Declaration Key Value) :
    Source Key Value :=
  let prepared := declaration.prepare
  ⟨⟨source.graph.nodes ++ [node]⟩,
    fun query => if query == node.name then some prepared else source.prepared query⟩

/-- An extension preserves the exact prepared owner of every other node. -/
theorem Source.add_prepared_frame (source : Source Key Value) (node : C4.Node)
    (declaration : Declaration Key Value) (name : String) (different : name ≠ node.name) :
    (source.add node declaration).prepared name = source.prepared name := by
  simp [add,different]


variable [DecidableEq Key] [BEq Key] [LawfulBEq Key] [Hashable Key]

abbrev MetadataPlan (Key : Type) (Value : Key → Type) [BEq Key] [LawfulBEq Key] [Hashable Key] :=
  CompiledPlan Key (fun key => GeneralizedGraph.Code Key Value key)

/-- Build the typed component program once from actual C4-selected fragment code.
Both code lookup and later value lookup use dependent tables. -/
def compileGraph (metadata : MetadataPlan Key Value) : GeneralizedGraph.Declaration Key Value :=
  let expressions := tabulate metadata.keys fun key => metadata.resolve key (fun _ => none)
  let watched := metadata.keys.flatMap fun key =>
    match (expressions.get? key).join with
    | none => []
    | some code => code.analyze.values ++ code.analyze.presences
  -- Missing providers remain observable absence nodes. They are not declared
  -- fields and never enter the object's reflected inventory.
  { keys := (metadata.keys ++ watched).eraseDups
    code := fun key => (expressions.get? key).join
    base := fun _ => none }

structure Template (Key : Type) (Value : Key → Type)
    [DecidableEq Key] [BEq Key] [LawfulBEq Key] [Hashable Key] where
  source : Source Key Value
  plan : Plan Key (fun key => GeneralizedGraph.Code Key Value key)
  sourceAligned : plan.schema = source.schema
  metadata : MetadataPlan Key Value
  metadataAligned : metadata = plan.compileMemo
  graph : GeneralizedGraph.Declaration Key Value
  graphAligned : graph = compileGraph metadata
  scheduled : GeneralizedGraph.Scheduled graph
  execution : ConstructionCache.Execution graph

/-- Retain an order/rank only after checking the complete current read sets.
Bodies and literal inputs may change: new instance values are still rebuilt. -/
def Template.rebaseSchedule? (prior : Template Key Value)
    (graph : GeneralizedGraph.Declaration Key Value) : Option (GeneralizedGraph.Scheduled graph) :=
  if sameKeys : graph.keys = prior.graph.keys then
    if sameReads : graph.keys.all (fun key => decide (graph.reads key = prior.graph.reads key)) = true then
      if known : graph.keys.all (fun key => decide ((graph.footprint key).unknown = false)) = true then
        some (prior.scheduled.rebase
          (by
            intro key
            by_cases active : key ∈ graph.keys
            · exact of_decide_eq_true (List.all_eq_true.mp sameReads key active)
            · have absent : key ∉ prior.graph.keys := by simpa [← sameKeys] using active
              simp [GeneralizedGraph.Declaration.reads,GeneralizedGraph.Declaration.footprint,active,absent])
          (by
            intro key
            by_cases active : key ∈ graph.keys
            · exact of_decide_eq_true (List.all_eq_true.mp known key active)
            · simp [GeneralizedGraph.Declaration.footprint,active]))
      else none
    else none
  else none

inductive Error (Key : Type) where
  | duplicate (error : Object.Declaration.DuplicateError Key)
  | schema (error : SchemaMergeError)
  | topology (error : C4.Error)
  | dependency (error : GeneralizedGraph.Error Key)
  | construction (error : ConstructionCache.Failure Key Key)
  deriving Repr

private structure StrictState (Key : Type) (Value : Key → Type) [BEq Key] [Hashable Key] where
  declaration : Declaration Key Value := {}
  slots : Std.HashSet Key := {}
  defaults : Std.HashSet Key := {}

structure StrictBuilder (Key : Type) (Value : Key → Type) [BEq Key] [Hashable Key] (α : Type) where
  run : StrictState Key Value → Except (Object.Declaration.DuplicateError Key) (α × StrictState Key Value)

instance : Monad (StrictBuilder Key Value) where
  pure value := ⟨fun state => .ok (value,state)⟩
  bind program next := ⟨fun state => do
    let (value,state) ← program.run state
    (next value).run state⟩

namespace StrictBuilder

def field [LawfulHashable Key] (key : Key) (fragment : GeneralizedFragments.Fragment Key Value key) :
    StrictBuilder Key Value PUnit := ⟨fun state =>
  if state.slots.contains key then .error (.slot key)
  else .ok (⟨⟩,{ state with
    slots := state.slots.insert key
    declaration := { state.declaration with
      fields := state.declaration.fields ++ [⟨key,fragment,fun _ => inferInstance⟩] } })⟩

def value [LawfulHashable Key] (key : Key) (value : Value key) : StrictBuilder Key Value PUnit :=
  field key (.replace (.pure fun _ => .ok value))

def derived [LawfulHashable Key] (key : Key) (expression : Expr Key Value (Value key)) :
    StrictBuilder Key Value PUnit := field key (.replace expression)

def default [LawfulHashable Key] (key : Key) (value : Value key) : StrictBuilder Key Value PUnit :=
  ⟨fun state => if state.defaults.contains key then .error (.default key)
    else .ok (⟨⟩,{ state with
      defaults := state.defaults.insert key
      declaration := { state.declaration with
        defaults := state.declaration.defaults ++ [⟨key,value,fun _ => inferInstance⟩] } })⟩

def modifyInherited [LawfulHashable Key] (key : Key) (change : Option (Value key) → Option (Value key)) :
    StrictBuilder Key Value PUnit :=
  field key (.extend (.pure fun _ previous => match change previous.toOption with
    | some value => .ok value
    | none => .error (.missing key)))

def build (program : StrictBuilder Key Value PUnit) : Except (Error Key) (Declaration Key Value) :=
  match program.run {} with
  | .error error => .error (.duplicate error)
  | .ok (_,state) => .ok state.declaration
end StrictBuilder

/-- A stored value is a fixed point of this exact compiled source, not an
asserted label or a retained observation from another profile/context. -/
structure Instance (Key : Type) (Value : Key → Type)
    [DecidableEq Key] [BEq Key] [LawfulBEq Key] [Hashable Key] where
  template : Template Key Value
  values : Std.DHashMap Key (fun key => Option (GeneralizedGraph.Outcome Key Value key))
  fixed : template.graph.protocol.step template.graph.keys
    (fun key => (values.get? key).join) template.graph.base = fun key => (values.get? key).join

def Template.prepare (source : Source Key Value) (root : String)
    (prior : Option (Template Key Value) := none) :
    Except (Error Key) (Template Key Value) :=
  match built : Object.compile source.schema root with
  | .error error => .error (.topology error)
  | .ok plan =>
    have aligned : plan.schema = source.schema := by
      unfold Object.compile at built
      split at built
      · contradiction
      · cases built; rfl
    let metadata := plan.compileMemo
    let graph := compileGraph metadata
    let reused := prior.bind fun previous => previous.rebaseSchedule? graph
    match reused with
    | some scheduled => .ok ⟨source,plan,aligned,metadata,rfl,graph,rfl,scheduled,ConstructionCache.Execution.compile graph⟩
    | none => match graph.schedule with
      | .error error => .error (.dependency error)
      | .ok scheduled => .ok ⟨source,plan,aligned,metadata,rfl,graph,rfl,scheduled,ConstructionCache.Execution.compile graph⟩

def Instance.raw (object : Instance Key Value) : GeneralizedGraph.State Key Value :=
  fun key => (object.values.get? key).join

def Instance.closed (object : Instance Key Value) :
    Prototype.Generalized.Closed object.template.graph.protocol
      object.template.graph.keys object.template.graph.base := ⟨object.raw,object.fixed⟩

theorem Instance.reference (object : Instance Key Value) :
    object.raw = object.template.scheduled.closed.raw :=
  object.template.scheduled.unique object.closed

/-- Only the instance owns materialized values. The prepared source can create
many instances; every start executes its resolvers once in the checked order. -/
def Template.build (ready : Template Key Value) :
    Except (Error Key) (Instance Key Value × List Key) :=
  match ConstructionCache.start ready.scheduled
      (ready.execution.guarded (fun _ => true)) with
  | .error error => .error (.construction error)
  | .ok cache =>
    let values := tabulate ready.graph.keys cache.closed.raw
    have reference := ready.scheduled.unique cache.closed
    have same : (fun key => (values.get? key).join) = cache.closed.raw := by
      funext key
      rw [tabulate_get?]
      by_cases active : key ∈ ready.graph.keys
      · simp [active]
      · have base : ready.graph.base key = none := by rw [ready.graphAligned]; rfl
        have closed := ready.scheduled.resolver.closed key
        change ready.graph.resolve key ready.scheduled.closed.raw = ready.scheduled.closed.raw key at closed
        have absent : ready.scheduled.closed.raw key = none := by
          simpa [GeneralizedGraph.Declaration.resolve,active,base] using closed.symm
        simpa [active,reference] using absent.symm
    .ok (⟨ready,values,by rw [same]; exact cache.closed.fixed⟩,cache.evaluated)

/-- The ordinary entrypoint uses the same materializer as observed construction. -/
def Template.instantiate (ready : Template Key Value) : Except (Error Key) (Instance Key Value) :=
  ready.build.map Prod.fst

def Instance.read (object : Instance Key Value) (key : Key) : Option (Value key) :=
  (object.raw key).bind Except.toOption

def Instance.plan (object : Instance Key Value) := object.template.plan

def Instance.slotNames (object : Instance Key Value) : List Key := object.template.metadata.keys

theorem Instance.slotNames_exact (object : Instance Key Value) :
    object.slotNames = LeanPoo.allSlots object.plan := by
  unfold Instance.slotNames Instance.plan
  rw [object.template.metadataAligned]
  rfl

theorem Instance.read_reference (object : Instance Key Value) (key : Key) :
    object.read key = (object.template.scheduled.closed.raw key).bind Except.toOption := by
  unfold Instance.read
  rw [object.reference]

def prepareDefinition (name : String) (program : Builder Key Value PUnit) :
    Except (Error Key) (Template Key Value) :=
  Template.prepare (Source.empty.add {name} (Builder.build program)) name

def define (name : String) (program : Builder Key Value PUnit) : Except (Error Key) (Instance Key Value) := do
  let prepared ← prepareDefinition name program
  prepared.instantiate

def Instance.defineWith (parent : Instance Key Value) (name : String) (supers : List String)
    (program : Builder Key Value PUnit) : Except (Error Key) (Instance Key Value) := do
  let source := parent.template.source.add
    {name, parentOrders := if supers.isEmpty then [] else [supers]} (Builder.build program)
  let prepared ← Template.prepare source name (some parent.template)
  prepared.instantiate

def Instance.extendWith (parent : Instance Key Value) (name : String)
    (program : Builder Key Value PUnit) : Except (Error Key) (Instance Key Value) :=
  parent.defineWith name [parent.plan.root] program

/-- Checked definitions reject duplicate direct declarations before C4/closure. -/
def defineStrict (name : String) (program : StrictBuilder Key Value PUnit) :
    Except (Error Key) (Instance Key Value) := do
  let declaration ← StrictBuilder.build program
  let prepared ← Template.prepare (Source.empty.add {name} declaration) name
  prepared.instantiate

def Instance.defineNodeWith (parent : Instance Key Value) (node : C4.Node)
    (program : Builder Key Value PUnit) : Except (Error Key) (Instance Key Value) := do
  let prepared ← Template.prepare (parent.template.source.add node (Builder.build program))
    node.name (some parent.template)
  prepared.instantiate

def Instance.defineFrom (first : Instance Key Value) (name : String)
    (others : List (Instance Key Value)) (program : Builder Key Value PUnit) :
    Except (Error Key) (Instance Key Value) := do
  let (graph,declaration) ← (mergeDeclarationGraphs
    (first.template.source.graph,first.template.source.prepared)
    (others.map fun object => (object.template.source.graph,object.template.source.prepared)))
    |>.mapError Error.schema
  let source : Source Key Value := ⟨graph,declaration⟩
  let parents := first.plan.root :: others.map (·.plan.root)
  let prepared ← Template.prepare
    (source.add {name,parentOrders := [parents]} (Builder.build program)) name
  prepared.instantiate

def Instance.defineStrictFrom (first : Instance Key Value) (name : String)
    (others : List (Instance Key Value)) (program : StrictBuilder Key Value PUnit) :
    Except (Error Key) (Instance Key Value) := do
  let declaration ← StrictBuilder.build program
  -- A checked program's result is a literal declaration; no second builder runs.
  let (graph,lookup) ← (mergeDeclarationGraphs
    (first.template.source.graph,first.template.source.prepared)
    (others.map fun object => (object.template.source.graph,object.template.source.prepared)))
    |>.mapError Error.schema
  let source : Source Key Value := ⟨graph,lookup⟩
  let parents := first.plan.root :: others.map (·.plan.root)
  let prepared ← Template.prepare (source.add {name,parentOrders := [parents]} declaration) name
  prepared.instantiate

end LeanPoo.Object.Dataflow
