import LeanPoo.Functional.ContractConsequence

/-! Combine independently admitted proofs about exactly the same dependency
functions. Equal Claim shapes alone cannot justify reusing another family. -/
namespace LeanPoo.Functional.Requirements
universe u v w x
variable {Context : Type u} {Key : Type v} {Value : Context → Key → Type w}
variable {keys : List Key} {Left Right : ∀ c, Results Value c keys → Prop}
variable {ready : Certified keys Left}

/-- Retain the left family and conjoin both certificates' analytic proofs.
Function equality is supplied explicitly and is erased, not checked at runtime. -/
def Certified.conjoin (ready : Certified keys Left) (other : Certified keys Right)
    (same : ready.factories = other.factories) : Certified keys (fun c data => Left c data ∧ Right c data) :=
  ⟨ready.factories, fun c => ⟨ready.valid c, by rw [same]; exact other.valid c⟩⟩

@[simp] theorem Certified.conjoin_factories (ready : Certified keys Left)
    (other : Certified keys Right) (same : ready.factories = other.factories) :
    (ready.conjoin other same).factories = ready.factories := rfl

/-- The exact cached alignment permits using the second built-data theorem;
no general implication from Left to Right is required. -/
def Snapshot.conjoin {context : Context} (data : Snapshot ready context)
    (other : Certified keys Right) (same : ready.factories = other.factories) :
    Snapshot (ready.conjoin other same) context :=
  ⟨data.val, data.property.1, data.property.2, by
    rw [data.property.1, same]; exact other.valid context⟩

@[simp] theorem Snapshot.conjoin_val {context : Context} (data : Snapshot ready context)
    (other : Certified keys Right) (same : ready.factories = other.factories) :
    (data.conjoin other same).val = data.val := rfl

/-- Retain built values and enrich their proof. Only the Option/context wrapper
is mapped; no tuple traversal, factory, observer or constructor runs. -/
def ContextSlot.conjoin (slot : ContextSlot ready) (other : Certified keys Right)
    (same : ready.factories = other.factories) : ContextSlot (ready.conjoin other same) :=
  ⟨slot.retained.map fun ⟨c, data⟩ => ⟨c, data.conjoin other same⟩⟩

@[simp] theorem ContextSlot.conjoin_empty (ready : Certified keys Left)
    (other : Certified keys Right) (same : ready.factories = other.factories) :
    (ContextSlot.empty ready).conjoin other same = ContextSlot.empty (ready.conjoin other same) := rfl

theorem ContextSlot.conjoin_retained (slot : ContextSlot ready) (context : Context)
    (data : Snapshot ready context) (saved : slot.retained = some ⟨context, data⟩)
    (other : Certified keys Right) (same : ready.factories = other.factories) :
    (slot.conjoin other same).retained = some ⟨context, data.conjoin other same⟩ := by
  simp [ContextSlot.conjoin, saved]

theorem ContextSlot.conjoin_hit [DecidableEq Context] (slot : ContextSlot ready) (context : Context)
    (data : Snapshot ready context) (saved : slot.retained = some ⟨context, data⟩)
    (other : Certified keys Right) (same : ready.factories = other.factories) :
    ((slot.conjoin other same).read context).2.2 = true := by
  rw [ContextSlot.read_hit _ context (data.conjoin other same)
    (slot.conjoin_retained context data saved other same)]

theorem ContextSlot.conjoin_consume [DecidableEq Context] (slot : ContextSlot ready)
    (other : Certified keys Right) (same : ready.factories = other.factories)
    {Output : Context → Type x} (construct : ∀ c data, Left c data ∧ Right c data → Output c)
    (context : Context) :
    ((slot.conjoin other same).consume construct context).1 =
      (ready.conjoin other same).consume construct context :=
  ContextSlot.consume_value _ construct context

end LeanPoo.Functional.Requirements
