import LeanPoo.Functional.ContextView
import LeanPoo.Functional.ContextObservation

/-! Narrow public interfaces directly from built dependency data. Only requested
positions are observed; first source occurrence and requested duplicates remain. -/
namespace LeanPoo.Functional.Requirements
universe u v w x y
variable {Context : Type u} {Key : Type v} {Value : Context → Key → Type w}
variable {Observed : Context → Key → Type x} [DecidableEq Key]

/-- Named observation agrees with observing the named source value. -/
theorem resultAt_observe (expose : ∀ c key, Value c key → Observed c key)
    {context : Context} {source : List Key} (data : Results Value context source)
    (key : Key) (member : key ∈ source) :
    resultAt (observeResults expose data) key member = expose context key (resultAt data key member) := by
  induction source with
  | nil => simp at member
  | cons head rest ih =>
    rcases data with ⟨value, tail⟩
    by_cases same : head = key
    · subst key; simp [resultAt, observeResults]
    · simp only [resultAt, observeResults, dite_eq_right same]
      exact ih tail _

/-- Both orderings produce equal values. Project first to avoid observers on
unrequested source positions; requested duplicates still repeat observers. -/
theorem projectResults_observe (expose : ∀ c key, Value c key → Observed c key)
    {context : Context} {source : List Key} (data : Results Value context source)
    (keys : List Key) (included : ∀ key ∈ keys, key ∈ source) :
    projectResults (observeResults expose data) keys included =
      observeResults expose (projectResults data keys included) := by
  induction keys with
  | nil => rfl
  | cons key rest ih =>
    simp only [projectResults, observeResults, resultAt_observe]
    exact congrArg (fun remaining => (expose context key (resultAt data key _), remaining)) (ih _)

variable {source : List Key} {Claim : ∀ c, Results Value c source → Prop}
variable {ready : Certified source Claim}

/-- One narrow public certificate, with a consequence over original built data.
No broad public certificate or intermediate narrow Claim is required. -/
def Certified.observeProject (ready : Certified source Claim) (keys : List Key)
    (included : ∀ key ∈ keys, key ∈ source)
    (expose : ∀ c key, Value c key → Observed c key)
    (Public : ∀ c, Results Observed c keys → Prop)
    (derive : ∀ c data, Claim c data → Public c (observeResults expose (projectResults data keys included))) :
    Certified keys Public :=
  ⟨Requirements.observe expose (Requirements.project ready.factories keys included), fun c => by
    rw [build_observe, build_project]
    exact derive c _ (ready.valid c)⟩

def Snapshot.observeProject {context : Context} (data : Snapshot ready context) (keys : List Key)
    (included : ∀ key ∈ keys, key ∈ source) (expose : ∀ c key, Value c key → Observed c key)
    (Public : ∀ c, Results Observed c keys → Prop) (derive) :
    Snapshot (ready.observeProject keys included expose Public derive) context :=
  ⟨observeResults expose (projectResults data.val keys included), by
    constructor
    · change _ = build (Requirements.observe expose (Requirements.project ready.factories keys included)) context
      rw [build_observe, build_project, data.property.1]
    · exact derive context data.val data.property.2⟩

@[simp] theorem Snapshot.observeProject_val {context : Context} (data : Snapshot ready context)
    (keys : List Key) (included : ∀ key ∈ keys, key ∈ source) (expose : ∀ c key, Value c key → Observed c key) (Public) (derive) :
    (data.observeProject keys included expose Public derive).val =
      observeResults expose (projectResults data.val keys included) := rfl

/-- Observe only requested positions in a populated slot; empty stays empty.
No dependency factory or output constructor is called during conversion. -/
def ContextSlot.observeProject (slot : ContextSlot ready) (keys : List Key)
    (included : ∀ key ∈ keys, key ∈ source) (expose : ∀ c key, Value c key → Observed c key)
    (Public : ∀ c, Results Observed c keys → Prop) (derive) :
    ContextSlot (ready.observeProject keys included expose Public derive) :=
  ⟨slot.retained.map fun ⟨c, data⟩ => ⟨c, data.observeProject keys included expose Public derive⟩⟩

@[simp] theorem ContextSlot.observeProject_empty (ready : Certified source Claim)
    (keys : List Key) (included : ∀ key ∈ keys, key ∈ source) (expose : ∀ c key, Value c key → Observed c key) (Public) (derive) :
    (ContextSlot.empty ready).observeProject keys included expose Public derive =
      ContextSlot.empty (ready.observeProject keys included expose Public derive) := rfl

theorem ContextSlot.observeProject_retained (slot : ContextSlot ready) (context : Context)
    (data : Snapshot ready context) (saved : slot.retained = some ⟨context, data⟩)
    (keys : List Key) (included : ∀ key ∈ keys, key ∈ source) (expose : ∀ c key, Value c key → Observed c key) (Public) (derive) :
    (slot.observeProject keys included expose Public derive).retained =
      some ⟨context, data.observeProject keys included expose Public derive⟩ := by
  simp [ContextSlot.observeProject, saved]

theorem ContextSlot.observeProject_hit [DecidableEq Context] (slot : ContextSlot ready)
    (context : Context) (data : Snapshot ready context) (saved : slot.retained = some ⟨context, data⟩)
    (keys : List Key) (included : ∀ key ∈ keys, key ∈ source) (expose : ∀ c key, Value c key → Observed c key) (Public) (derive) :
    ((slot.observeProject keys included expose Public derive).read context).2.2 = true := by
  rw [ContextSlot.read_hit _ context (data.observeProject keys included expose Public derive)
    (slot.observeProject_retained context data saved keys included expose Public derive)]

theorem ContextSlot.observeProject_consume [DecidableEq Context] (slot : ContextSlot ready)
    (keys : List Key) (included : ∀ key ∈ keys, key ∈ source) (expose : ∀ c key, Value c key → Observed c key) (Public) (derive)
    {Output : Context → Type y} (construct : ∀ c data, Public c data → Output c) (context : Context) :
    ((slot.observeProject keys included expose Public derive).consume construct context).1 =
      construct context (observeResults expose (projectResults (build ready.factories context) keys included))
        (derive context _ (ready.valid context)) := by
  rw [ContextSlot.consume_value, Certified.consume_apply]
  change construct context (build (Requirements.observe expose (Requirements.project ready.factories keys included)) context) _ = _
  simp only [build_observe, build_project]

end LeanPoo.Functional.Requirements
