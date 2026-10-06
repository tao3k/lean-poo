import LeanPoo.Functional.ObservedView

/-! Read narrow public data while retaining the broad cache for other consumers. -/
namespace LeanPoo.Functional.Requirements
universe u v w x y
variable {Context : Type u} {Key : Type v} {Value : Context → Key → Type w}
variable {Observed : Context → Key → Type x} [DecidableEq Key] [DecidableEq Context]
variable {source : List Key} {Claim : ∀ c, Results Value c source → Prop}
variable {ready : Certified source Claim}

/-- Read the broad cache once, expose this consumer's view, and return the broad
next slot. Observation runs on every read; misses build the entire broad family. -/
def ContextSlot.readView (slot : ContextSlot ready) (keys : List Key)
    (included : ∀ key ∈ keys, key ∈ source) (expose : ∀ c key, Value c key → Observed c key)
    (Public : ∀ c, Results Observed c keys → Prop) (derive : ∀ c data, Claim c data → Public c (observeResults expose (projectResults data keys included))) (context : Context) :
    Snapshot (ready.observeProject keys included expose Public derive) context × ContextSlot ready × Bool :=
  let (data, next, reused) := slot.read context
  (data.observeProject keys included expose Public derive, next, reused)

/-- View reads preserve the exact broad cache transition and hit flag. -/
theorem ContextSlot.readView_state (slot : ContextSlot ready) (keys : List Key)
    (included : ∀ key ∈ keys, key ∈ source) (expose : ∀ c key, Value c key → Observed c key)
    (Public) (derive : ∀ c data, Claim c data → Public c (observeResults expose (projectResults data keys included))) (context : Context) :
    (slot.readView keys included expose Public derive context).2 = (slot.read context).2 := rfl

/-- Public values agree with projecting and observing an uncached broad build. -/
theorem ContextSlot.readView_value (slot : ContextSlot ready) (keys : List Key)
    (included : ∀ key ∈ keys, key ∈ source) (expose : ∀ c key, Value c key → Observed c key)
    (Public) (derive : ∀ c data, Claim c data → Public c (observeResults expose (projectResults data keys included))) (context : Context) :
    (slot.readView keys included expose Public derive context).1.val =
      observeResults expose (projectResults (build ready.factories context) keys included) := by
  change observeResults expose (projectResults (slot.read context).1.val keys included) = _
  rw [ContextSlot.read_value]

/-- Run a proof-aware view consumer and keep broad dependencies available for
later consumers with different keys or observations. Constructors always run. -/
def ContextSlot.consumeView (slot : ContextSlot ready) (keys : List Key)
    (included : ∀ key ∈ keys, key ∈ source) (expose : ∀ c key, Value c key → Observed c key)
    (Public : ∀ c, Results Observed c keys → Prop) (derive : ∀ c data, Claim c data → Public c (observeResults expose (projectResults data keys included)))
    {Output : Context → Type y} (construct : ∀ c data, Public c data → Output c) (context : Context) :
    Output context × ContextSlot ready × Bool :=
  let (data, next, reused) := slot.readView keys included expose Public derive context
  (construct context data.val data.property.2, next, reused)

theorem ContextSlot.consumeView_value (slot : ContextSlot ready) (keys : List Key)
    (included : ∀ key ∈ keys, key ∈ source) (expose : ∀ c key, Value c key → Observed c key)
    (Public) (derive : ∀ c data, Claim c data → Public c (observeResults expose (projectResults data keys included))) {Output : Context → Type y}
    (construct : ∀ c data, Public c data → Output c) (context : Context) :
    (slot.consumeView keys included expose Public derive construct context).1 =
      (ready.observeProject keys included expose Public derive).consume construct context := by
  unfold ContextSlot.consumeView
  generalize found : slot.readView keys included expose Public derive context = result
  rcases result with ⟨⟨data, aligned, valid⟩, next, reused⟩
  dsimp only
  rw [Certified.consume_apply]
  cases aligned
  rfl

end LeanPoo.Functional.Requirements
