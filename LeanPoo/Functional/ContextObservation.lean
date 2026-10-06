import LeanPoo.Functional.ContextSlot

/-! Explicit public observations of built dependency caches. Hidden replacement
values are not reconstructed; only aligned public data can be retained. -/
namespace LeanPoo.Functional.Requirements
universe u v w x y z
variable {Context : Type u} {Key : Type v}
variable {Value : Context → Key → Type w} {Other : Context → Key → Type x}
variable {Observed : Context → Key → Type y}
variable {keys : List Key} {Claim : ∀ c, Results Value c keys → Prop}
variable {ready : Certified keys Claim}

/-- Observe already built data and derive a public joint proof. The observation
functions run now; no provider, factory or output constructor is called. -/
def Snapshot.observe {context : Context} (data : Snapshot ready context)
    (expose : ∀ c key, Value c key → Observed c key)
    (Public : ∀ c, Results Observed c keys → Prop)
    (derive : ∀ c data, Claim c data → Public c (observeResults expose data)) :
    Snapshot (ready.observe expose Public derive) context :=
  ⟨observeResults expose data.val, by
    constructor
    · rw [Certified.observe_factories, build_observe, data.property.1]
    · exact derive context data.val data.property.2⟩

@[simp] theorem Snapshot.observe_val {context : Context} (data : Snapshot ready context)
    (expose : ∀ c key, Value c key → Observed c key) (Public) (derive) :
    (data.observe expose Public derive).val = observeResults expose data.val := rfl

/-- Map a populated cache to its public representation at the same context.
An empty cache remains empty. Clients may retain the original hidden cache. -/
def ContextSlot.observe (slot : ContextSlot ready)
    (expose : ∀ c key, Value c key → Observed c key)
    (Public : ∀ c, Results Observed c keys → Prop)
    (derive : ∀ c data, Claim c data → Public c (observeResults expose data)) :
    ContextSlot (ready.observe expose Public derive) :=
  ⟨slot.retained.map fun ⟨context, data⟩ => ⟨context, data.observe expose Public derive⟩⟩

@[simp] theorem ContextSlot.observe_empty (ready : Certified keys Claim)
    (expose : ∀ c key, Value c key → Observed c key) (Public) (derive) :
    (ContextSlot.empty ready).observe expose Public derive =
      ContextSlot.empty (ready.observe expose Public derive) := rfl

theorem ContextSlot.observe_retained (slot : ContextSlot ready) (context : Context)
    (data : Snapshot ready context) (retained : slot.retained = some ⟨context, data⟩)
    (expose : ∀ c key, Value c key → Observed c key) (Public) (derive) :
    (slot.observe expose Public derive).retained =
      some ⟨context, data.observe expose Public derive⟩ := by
  simp [ContextSlot.observe, retained]

theorem ContextSlot.observe_hit [DecidableEq Context] (slot : ContextSlot ready)
    (context : Context) (data : Snapshot ready context)
    (retained : slot.retained = some ⟨context, data⟩)
    (expose : ∀ c key, Value c key → Observed c key) (Public) (derive) :
    ((slot.observe expose Public derive).read context).2.2 = true := by
  rw [ContextSlot.read_hit _ context (data.observe expose Public derive)
    (slot.observe_retained context data retained expose Public derive)]

theorem ContextSlot.observe_consume [DecidableEq Context] (slot : ContextSlot ready)
    (expose : ∀ c key, Value c key → Observed c key) (Public) (derive)
    {Output : Context → Type z} (construct : ∀ c data, Public c data → Output c)
    (context : Context) :
    ((slot.observe expose Public derive).consume construct context).1 =
      construct context (observeResults expose (build ready.factories context))
        (derive context _ (ready.valid context)) := by
  rw [ContextSlot.consume_value, Certified.consume_apply]
  simp only [Certified.observe_factories, build_observe]

/-- Hand the public cache to an explicitly compatible replacement family.
No candidate hidden values are built; future misses use its public factories. -/
def ContextSlot.replaceObservedPublic
    (expose : ∀ c key, Value c key → Observed c key)
    (reveal : ∀ c key, Other c key → Observed c key)
    (Public : ∀ c, Results Observed c keys → Prop)
    {old : Certified keys (fun c data => Public c (observeResults expose data))}
    (slot : ContextSlot old) (candidate : Factories Context Other keys)
    (compatible : Related (fun c key a b => expose c key a = reveal c key b)
      keys old.factories candidate) :
    ContextSlot ((Certified.replaceObserved keys expose reveal Public old candidate compatible).observe
      reveal Public (fun _ _ proof => proof)) :=
  (slot.observe expose Public (fun _ _ proof => proof)).rebind _
    (congrArg Certified.factories
      (Certified.replaceObserved_public keys expose reveal Public old candidate compatible))

/-- Replacement preserves every public proof-aware consumer output. -/
theorem ContextSlot.replaceObservedPublic_consume [DecidableEq Context]
    (expose : ∀ c key, Value c key → Observed c key)
    (reveal : ∀ c key, Other c key → Observed c key) (Public)
    {old : Certified keys (fun c data => Public c (observeResults expose data))}
    (slot : ContextSlot old) (candidate : Factories Context Other keys) (compatible)
    {Output : Context → Type z} (construct : ∀ c data, Public c data → Output c)
    (context : Context) :
    ((slot.replaceObservedPublic expose reveal Public candidate compatible).consume construct context).1 =
      ((slot.observe expose Public (fun _ _ proof => proof)).consume construct context).1 := by
  exact ContextSlot.rebind_consume _ _ _ construct context

end LeanPoo.Functional.Requirements
