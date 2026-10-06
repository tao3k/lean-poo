import LeanPoo.Functional.CertifiedConsumer

/-! A bounded one-context memo of built dependency data, aligned to an exact
certified family. Misses replace the slot; output constructors are not memoized. -/
namespace LeanPoo.Functional.Requirements
universe u v w x
variable {Context : Type u} {Key : Type v} {Value : Context → Key → Type w}
variable {keys : List Key} {Claim : ∀ c, Results Value c keys → Prop}

/-- Built data with both exact factory alignment and its joint analytic proof. -/
def Snapshot (ready : Certified keys Claim) (context : Context) :=
  {data : Results Value context keys // data = build ready.factories context ∧ Claim context data}

/-- A cache value retains zero or one context/data pair, never a context map.
The family is a type index: changing it requires explicit equality/reconstruction. -/
structure ContextSlot (ready : Certified keys Claim) where
  retained : Option ((context : Context) × Snapshot ready context)

def ContextSlot.empty (ready : Certified keys Claim) : ContextSlot ready := ⟨none⟩

/-- Read at exactly this context. A hit casts retained data along context equality
without building factories; a miss builds once and replaces the previous pair.
The Bool reports reuse of dependency data, not of the output constructor. -/
def ContextSlot.read [DecidableEq Context] {ready : Certified keys Claim}
    (slot : ContextSlot ready) (context : Context) : Snapshot ready context × ContextSlot ready × Bool :=
  match slot.retained with
  | some ⟨previous, data⟩ =>
    if same : previous = context then (same ▸ data, slot, true)
    else
      let fresh : Snapshot ready context := ⟨build ready.factories context, rfl, ready.valid context⟩
      (fresh, ⟨some ⟨context, fresh⟩⟩, false)
  | none =>
    let fresh : Snapshot ready context := ⟨build ready.factories context, rfl, ready.valid context⟩
    (fresh, ⟨some ⟨context, fresh⟩⟩, false)

/-- An exact-context hit returns the retained tuple and unchanged slot. -/
theorem ContextSlot.read_hit [DecidableEq Context] {ready : Certified keys Claim}
    (slot : ContextSlot ready) (context : Context) (data : Snapshot ready context)
    (retained : slot.retained = some ⟨context, data⟩) :
    slot.read context = (data, slot, true) := by
  simp [ContextSlot.read, retained]

/-- A miss replaces the slot with exactly the requested context and built data. -/
theorem ContextSlot.read_miss [DecidableEq Context] {ready : Certified keys Claim}
    (slot : ContextSlot ready) (context : Context)
    (absent : ∀ previous data, slot.retained = some ⟨previous, data⟩ → previous ≠ context) :
    (slot.read context).2.2 = false ∧
      (slot.read context).2.1.retained = some ⟨context, (slot.read context).1⟩ := by
  cases stored : slot.retained with
  | none => simp [ContextSlot.read, stored]
  | some pair =>
    rcases pair with ⟨previous, data⟩
    simp [ContextSlot.read, stored, absent previous data stored]

/-- Every read has exactly the uncached built data, at its dependent context. -/
theorem ContextSlot.read_value [DecidableEq Context] {ready : Certified keys Claim}
    (slot : ContextSlot ready) (context : Context) :
    (slot.read context).1.val = build ready.factories context := (slot.read context).1.property.1

/-- Consume cached dependency data and its analytic proof. The constructor runs
on hits as well as misses; it receives no stale context or family evidence. -/
def ContextSlot.consume [DecidableEq Context] {ready : Certified keys Claim}
    (slot : ContextSlot ready) {Output : Context → Type x}
    (construct : ∀ c data, Claim c data → Output c) (context : Context) :
    Output context × ContextSlot ready × Bool :=
  let (data, next, reused) := slot.read context
  (construct context data.val data.property.2, next, reused)

/-- Cached and uncached proof-aware consumers produce the same output. -/
theorem ContextSlot.consume_value [DecidableEq Context] {ready : Certified keys Claim}
    (slot : ContextSlot ready) {Output : Context → Type x}
    (construct : ∀ c data, Claim c data → Output c) (context : Context) :
    (slot.consume construct context).1 = ready.consume construct context := by
  unfold ContextSlot.consume
  generalize found : slot.read context = result
  rcases result with ⟨⟨data, aligned, valid⟩, next, reused⟩
  dsimp only
  rw [Certified.consume_apply]
  cases aligned
  rfl

/-- Reuse built data for an explicitly equal factory family and fixed Claim.
Only the erased family alignment changes; no factory or constructor runs. -/
def ContextSlot.rebind {left : Certified keys Claim} (slot : ContextSlot left)
    (right : Certified keys Claim) (same : left.factories = right.factories) : ContextSlot right :=
  Certified.ext left right same ▸ slot

/-- Explicit rebinding preserves proof-aware consumer outputs. -/
theorem ContextSlot.rebind_consume [DecidableEq Context] {left : Certified keys Claim}
    (slot : ContextSlot left) (right : Certified keys Claim) (same : left.factories = right.factories)
    {Output : Context → Type x} (construct : ∀ c data, Claim c data → Output c) (context : Context) :
    ((slot.rebind right same).consume construct context).1 = (slot.consume construct context).1 := by
  rw [ContextSlot.consume_value, ContextSlot.consume_value]
  exact congrFun (Certified.consume_congr right left construct same.symm) context

end LeanPoo.Functional.Requirements
