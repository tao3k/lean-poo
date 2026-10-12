import LeanPoo.Functional.BorrowedView

/-! Consume several narrow interfaces from one aligned broad snapshot. The
caller chooses the views and constructors; the broad cache advances once. -/
namespace LeanPoo.Functional.Requirements
universe u v w x y
variable {Context : Type u} {Key : Type v} {Value : Context → Key → Type w}
variable {source : List Key} {Claim : ∀ c, Results Value c source → Prop}
variable {ready : Certified source Claim}

/-- Construct an output from the existing data and joint proof. -/
def Snapshot.consume {context : Context} (data : Snapshot ready context)
    {Output : Context → Type x} (construct : ∀ c values, Claim c values → Output c) : Output context :=
  construct context data.val data.property.2

/-- Observe only this interface's positions in an already read broad snapshot. -/
def Snapshot.consumeView [DecidableEq Key] {context : Context} (data : Snapshot ready context)
    (keys : List Key) (included : ∀ key ∈ keys, key ∈ source)
    {Observed : Context → Key → Type x} (expose : ∀ c key, Value c key → Observed c key)
    (Public : ∀ c, Results Observed c keys → Prop)
    (derive : ∀ c values, Claim c values → Public c (observeResults expose (projectResults values keys included)))
    {Output : Context → Type y} (construct : ∀ c values, Public c values → Output c) : Output context :=
  (data.observeProject keys included expose Public derive).consume construct

theorem Snapshot.consumeView_value [DecidableEq Key] {context : Context} (data : Snapshot ready context)
    (keys : List Key) (included : ∀ key ∈ keys, key ∈ source)
    {Observed : Context → Key → Type x} (expose : ∀ c key, Value c key → Observed c key)
    (Public) (derive) {Output : Context → Type y}
    (construct : ∀ c values, Public c values → Output c) :
    data.consumeView keys included expose Public derive construct =
      (ready.observeProject keys included expose Public derive).consume construct context := by
  unfold Snapshot.consumeView
  generalize found : data.observeProject keys included expose Public derive = observed
  rcases observed with ⟨values, aligned, valid⟩
  unfold Snapshot.consume
  rw [Certified.consume_apply]
  cases aligned
  rfl

/-- Read once and give the same aligned snapshot to a composite consumer. -/
def ContextSlot.consumeSnapshot [DecidableEq Context] (slot : ContextSlot ready)
    {Output : Context → Type x} (construct : ∀ c, Snapshot ready c → Output c) (context : Context) :
    Output context × ContextSlot ready × Bool :=
  let (data, next, reused) := slot.read context
  (construct context data, next, reused)

theorem ContextSlot.consumeSnapshot_state [DecidableEq Context] (slot : ContextSlot ready)
    {Output : Context → Type x} (construct : ∀ c, Snapshot ready c → Output c) (context : Context) :
    (slot.consumeSnapshot construct context).2 = (slot.read context).2 := rfl

theorem ContextSlot.consumeSnapshot_value [DecidableEq Context] (slot : ContextSlot ready)
    {Output : Context → Type x} (construct : ∀ c, Snapshot ready c → Output c) (context : Context) :
    (slot.consumeSnapshot construct context).1 =
      construct context ⟨build ready.factories context, rfl, ready.valid context⟩ := by
  have aligned : (slot.read context).1 =
      (⟨build ready.factories context, rfl, ready.valid context⟩ : Snapshot ready context) :=
    Subtype.ext (ContextSlot.read_value slot context)
  exact congrArg (construct context) aligned

/-- Fan out to two heterogeneous consumers while returning one broad next slot
and one dependency-hit decision. Constructors run on hits as well as misses. -/
def ContextSlot.consumePair [DecidableEq Context] (slot : ContextSlot ready)
    {Left : Context → Type x} {Right : Context → Type y}
    (left : ∀ c, Snapshot ready c → Left c) (right : ∀ c, Snapshot ready c → Right c)
    (context : Context) : (Left context × Right context) × ContextSlot ready × Bool :=
  slot.consumeSnapshot (fun c data => (left c data, right c data)) context

theorem ContextSlot.consumePair_state [DecidableEq Context] (slot : ContextSlot ready)
    {Left : Context → Type x} {Right : Context → Type y}
    (left : ∀ c, Snapshot ready c → Left c) (right : ∀ c, Snapshot ready c → Right c) (context : Context) :
    (slot.consumePair left right context).2 = (slot.read context).2 := rfl

theorem ContextSlot.consumePair_values [DecidableEq Context] (slot : ContextSlot ready)
    {Left : Context → Type x} {Right : Context → Type y}
    (left : ∀ c, Snapshot ready c → Left c) (right : ∀ c, Snapshot ready c → Right c) (context : Context) :
    (slot.consumePair left right context).1 =
      (left context ⟨build ready.factories context, rfl, ready.valid context⟩,
       right context ⟨build ready.factories context, rfl, ready.valid context⟩) :=
  slot.consumeSnapshot_value _ context

end LeanPoo.Functional.Requirements
