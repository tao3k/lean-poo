import LeanPoo.Functional.ContextSlot
import LeanPoo.Functional.Reindex

/-! Read a fixed certified family through an explicit outer-context projection.
Only the base context needs executable equality; outputs may use the full outer
context. Arbitrary outer-dependent factories cannot be silently admitted. -/
namespace LeanPoo.Functional.Requirements
universe u v w x y
variable {Context : Type u} {Outer : Type x} {Key : Type v}
variable {Value : Context → Key → Type w} {keys : List Key}
variable {Claim : ∀ c, Results Value c keys → Prop} {ready : Certified keys Claim}
variable [DecidableEq Context]

/-- Read at the complete context of the fixed base family. The projection is
executed once here; outer fields cannot change this family's dependencies. -/
def ContextSlot.readAlong (slot : ContextSlot ready) (project : Outer → Context)
    (outer : Outer) : Snapshot ready (project outer) × ContextSlot ready × Bool :=
  slot.read (project outer)

theorem ContextSlot.readAlong_value (slot : ContextSlot ready) (project : Outer → Context)
    (outer : Outer) :
    (slot.readAlong project outer).1.val = build ready.factories (project outer) :=
  slot.read_value (project outer)

/-- Different outer contexts can hit when their complete base context agrees. -/
theorem ContextSlot.readAlong_hit (slot : ContextSlot ready) (project : Outer → Context)
    (outer : Outer) (context : Context) (data : Snapshot ready context)
    (retained : slot.retained = some ⟨context, data⟩) (same : context = project outer) :
    (slot.readAlong project outer).2.2 = true := by
  subst context
  rw [ContextSlot.readAlong, ContextSlot.read_hit slot _ data retained]

/-- Consume cached base dependency data with the full outer context. The output
constructor still runs for every outer request, including equal-base hits. -/
def ContextSlot.consumeAlong (slot : ContextSlot ready) (project : Outer → Context)
    {Output : Outer → Type y}
    (construct : ∀ outer data, Claim (project outer) data → Output outer) (outer : Outer) :
    Output outer × ContextSlot ready × Bool :=
  let (data, next, reused) := slot.readAlong project outer
  (construct outer data.val data.property.2, next, reused)

theorem ContextSlot.consumeAlong_value (slot : ContextSlot ready) (project : Outer → Context)
    {Output : Outer → Type y} (construct : ∀ outer data, Claim (project outer) data → Output outer)
    (outer : Outer) :
    (slot.consumeAlong project construct outer).1 =
      construct outer (build ready.factories (project outer)) (ready.valid (project outer)) := by
  unfold ContextSlot.consumeAlong
  generalize found : slot.readAlong project outer = result
  rcases result with ⟨⟨data, aligned, valid⟩, next, reused⟩
  dsimp only
  cases aligned
  rfl

/-- A base-only constructor agrees with its existing factory reindexing. -/
theorem ContextSlot.consumeAlong_reindex (slot : ContextSlot ready) (project : Outer → Context)
    {Output : Context → Type y} (construct : ∀ c data, Claim c data → Output c) (outer : Outer) :
    (slot.consumeAlong project (fun o data proof => construct (project o) data proof) outer).1 =
      Factory.reindex project (ready.consume construct) outer := by
  rw [ContextSlot.consumeAlong_value]
  exact (Certified.consume_apply ready construct (project outer)).symm

end LeanPoo.Functional.Requirements
