import LeanPoo.Functional.GeneralizedMOP

/-! Materialized construction, with certified skipping of unaffected resolvers.
References to ranked closure occur in proofs; runtime values come only from
cached slots or the explicit builder. This advances generalized-MOP future work. -/
namespace LeanPoo.Functional.ConstructionCache
open GeneralizedGraph

variable {Key : Type} {Value : Key → Type} [DecidableEq Key]

structure Cache (spec : Declaration Key Value) where
  closed : Prototype.Generalized.Closed spec.protocol spec.keys spec.base
  evaluated : List Key
  reused : List Key

/-- Builders may refuse work, but successful work must execute this resolver.
The guarded builder lets clients test that retained nodes really are skipped. -/
structure Builder (spec : Declaration Key Value) (BuildError : Type) where
  run : (key : Key) → State Key Value → Except BuildError (Option (Outcome Key Value key))
  correct : ∀ key self value, run key self = .ok value → value = spec.resolve key self

def Builder.guarded (spec : Declaration Key Value) (allow : Key → Bool) : Builder spec Key where
  run := fun key self => if allow key then .ok (spec.resolve key self) else .error key
  correct := by intro key self value success; split at success <;> cases success; rfl

/-- A reuse slot includes absence and failure, not only successful values. -/
abbrev Reuse {spec : Declaration Key Value} (scheduled : Scheduled spec) :=
  (key : Key) → Option {value : Option (Outcome Key Value key) // value = scheduled.closed.raw key}

structure Partial {spec : Declaration Key Value} (scheduled : Scheduled spec) where
  state : State Key Value
  done : List Key
  agrees : ∀ key ∈ done, state key = scheduled.closed.raw key
  frame : ∀ key, key ∉ spec.keys → state key = spec.base key
  evaluated : List Key
  reused : List Key

variable {BuildError : Type} {spec : Declaration Key Value} (scheduled : Scheduled spec)

inductive Failure (Key BuildError : Type) where
  | dependency (key : Key)
  | incomplete
  | build (key : Key) (error : BuildError)
  deriving Repr

def Partial.empty : Partial scheduled where
  state := spec.base
  done := []
  agrees := by intro key member; cases member
  frame := by intro key _; rfl
  evaluated := []
  reused := []

def Partial.install (prior : Partial scheduled) (key : Key) (active : key ∈ spec.keys)
    (value : Option (Outcome Key Value key)) (correct : value = scheduled.closed.raw key)
    (retained : Bool) : Partial scheduled where
  state := setSlot prior.state key value
  done := key :: prior.done
  agrees := by
    intro query member
    by_cases same : key = query
    · subst query; simpa [setSlot] using correct
    · have member : query ∈ prior.done := by simpa [List.mem_cons, Ne.symm same] using member
      simpa [setSlot, same] using prior.agrees query member
  frame := by
    intro query outside
    have different : key ≠ query := by intro same; subst query; exact outside active
    simpa [setSlot, different] using prior.frame query outside
  evaluated := if retained then prior.evaluated else prior.evaluated ++ [key]
  reused := if retained then prior.reused ++ [key] else prior.reused

/-- Retained branches do not call builder.run or the new resolver. Fresh nodes
read only already materialized dependencies, so shared dependencies execute once. -/
def Partial.step (builder : Builder spec BuildError) (reuse : Reuse scheduled)
    (prior : Partial scheduled) (key : Key) : Except (Failure Key BuildError) (Partial scheduled) :=
  if active : key ∈ spec.keys then
    if key ∈ prior.done then .ok prior
    else match reuse key with
    | some cached => .ok (prior.install scheduled key active cached.val cached.property true)
    | none =>
      if ready : (spec.reads key).all (fun dep => decide (dep ∈ prior.done)) = true then
        match worked : builder.run key prior.state with
        | .error error => .error (.build key error)
        | .ok value => .ok (prior.install scheduled key active value (by
            rw [builder.correct key prior.state value worked]
            calc
              spec.resolve key prior.state = spec.resolve key scheduled.closed.raw := by
                apply spec.locality key (scheduled.known key)
                intro dep member
                exact prior.agrees dep (of_decide_eq_true (List.all_eq_true.mp ready dep member))
              _ = scheduled.closed.raw key := scheduled.resolver.closed key) false)
      else .error (.dependency key)
  else .ok prior

def Partial.finish (prior : Partial scheduled) : Except (Failure Key BuildError) (Cache spec) :=
  if covered : spec.keys.all (fun key => decide (key ∈ prior.done)) = true then
    have same : prior.state = scheduled.closed.raw := by
      funext key
      by_cases active : key ∈ spec.keys
      · exact prior.agrees key (of_decide_eq_true (List.all_eq_true.mp covered key active))
      · rw [prior.frame key active]
        change spec.base key = scheduled.resolver.close key
        have closed := scheduled.resolver.closed key
        simpa [Declaration.resolve, active] using closed
    .ok ⟨⟨prior.state,by rw [same]; exact scheduled.closed.fixed⟩,prior.evaluated,prior.reused⟩
  else .error .incomplete

def materialize (builder : Builder spec BuildError) (reuse : Reuse scheduled) :
    Except (Failure Key BuildError) (Cache spec) :=
  let rec go (prior : Partial scheduled) : List Key → Except (Failure Key BuildError) (Cache spec)
    | [] => prior.finish scheduled
    | key :: rest => match prior.step scheduled builder reuse key with
      | .error error => .error error
      | .ok next => go next rest
  go (Partial.empty scheduled) scheduled.order

/-- Cold construction uses the same materializer without any retained slots. -/
def start (builder : Builder spec BuildError) : Except (Failure Key BuildError) (Cache spec) :=
  materialize scheduled builder (fun _ => none)

/-- Exact resolver equality for unchanged source is mandatory; version labels
or sampled equal outputs cannot certify a reuse branch. -/
def refresh {old : Declaration Key Value} (cache : Cache old) (changed : Key → Bool)
    (unchanged : ∀ key, changed key = false → ∀ self, spec.resolve key self = old.resolve key self)
    (builder : Builder spec BuildError) : Except (Failure Key BuildError) (Cache spec) :=
  materialize scheduled builder fun key =>
    if clean : scheduled.invalidates changed key = false then
      some ⟨cache.closed.raw key,scheduled.unaffected changed
        (by intro key safe self; exact (unchanged key safe self).symm) cache.closed key clean⟩
    else none

theorem Cache.reference (cache : Cache spec) : cache.closed.raw = scheduled.closed.raw :=
  scheduled.unique cache.closed

/-- Source-level statement of skipping: even a builder refusing this node is
irrelevant when a certified reuse slot exists. -/
theorem Partial.step_reused (builder : Builder spec BuildError) (reuse : Reuse scheduled)
    (prior : Partial scheduled) (key : Key) (active : key ∈ spec.keys) (pending : key ∉ prior.done)
    (cached : {value : Option (Outcome Key Value key) // value = scheduled.closed.raw key})
    (hit : reuse key = some cached) :
    prior.step scheduled builder reuse key =
      .ok (prior.install scheduled key active cached.val cached.property true) := by
  simp [Partial.step, active, pending, hit]

/-- A clean materialized slot is independent of every builder implementation,
including one that refuses this node. This is source-level work skipping. -/
theorem Partial.step_reused_builder_independent
    (first : Builder spec FirstError) (second : Builder spec SecondError) (reuse : Reuse scheduled)
    (prior : Partial scheduled) (key : Key) (active : key ∈ spec.keys) (pending : key ∉ prior.done)
    (cached : {value : Option (Outcome Key Value key) // value = scheduled.closed.raw key})
    (hit : reuse key = some cached) :
    (prior.step scheduled first reuse key).toOption =
      (prior.step scheduled second reuse key).toOption := by
  rw [Partial.step_reused scheduled first reuse prior key active pending cached hit,
      Partial.step_reused scheduled second reuse prior key active pending cached hit]
  rfl

theorem Partial.step_done (builder : Builder spec BuildError) (reuse : Reuse scheduled)
    (prior : Partial scheduled) (key : Key) (done : key ∈ prior.done) :
    prior.step scheduled builder reuse key = .ok prior := by
  by_cases active : key ∈ spec.keys <;> simp [Partial.step,active,done]

open GeneralizedMOP
variable {Policy : Type}

def touches (edit : Redefinition Key Value Policy) (key : Key) : Bool :=
  match edit with
  | .define target _ | .remove target | .setBase target _ => decide (target = key)
  | .support _ => true
  | .policy _ => false

theorem edit_unchanged (edit : Redefinition Key Value Policy) (request : Request Key Value Policy)
    (key : Key) (clean : touches edit key = false) (self : State Key Value) :
    (edit.apply request).graph.resolve key self = request.graph.resolve key self := by
  cases edit with
  | define target code =>
    exact request.graph.define_resolve_frame target key code (by simpa [touches] using clean) self
  | remove target =>
    exact request.graph.remove_resolve_frame target key (by simpa [touches] using clean) self
  | setBase target value =>
    exact request.graph.setBase_resolve_frame target key value (by simpa [touches] using clean) self
  | support keys => simp [touches] at clean
  | policy value => rfl

def changed (edits : List (Redefinition Key Value Policy)) (key : Key) : Bool :=
  edits.any (fun edit => touches edit key)

theorem redefine_unchanged (request : Request Key Value Policy) (edits : List (Redefinition Key Value Policy))
    (key : Key) (clean : changed edits key = false) (self : State Key Value) :
    (redefine request edits).graph.resolve key self = request.graph.resolve key self := by
  induction edits generalizing request with
  | nil => rfl
  | cons edit rest ih =>
    have parts : touches edit key = false ∧ changed rest key = false := by
      simpa [changed] using clean
    exact (ih (edit.apply request) parts.2).trans (edit_unchanged edit request key parts.1 self)

end LeanPoo.Functional.ConstructionCache
