import LeanPoo.Functional.ContextSlot

/-! Change only the joint proof via an explicit consequence, retaining functions
and built values. No dependency projection or value observation is performed. -/
namespace LeanPoo.Functional.Requirements
universe u v w x
variable {Context : Type u} {Key : Type v} {Value : Context → Key → Type w}
variable {keys : List Key} {Claim : ∀ c, Results Value c keys → Prop}
variable {Next : ∀ c, Results Value c keys → Prop}
variable {ready : Certified keys Claim}

/-- Derive another contract from the original proof without preparing functions. -/
def Certified.entails (ready : Certified keys Claim) (Next : ∀ c, Results Value c keys → Prop)
    (derive : ∀ c data, Claim c data → Next c data) : Certified keys Next :=
  ⟨ready.factories, fun c => derive c _ (ready.valid c)⟩

@[simp] theorem Certified.entails_factories (ready : Certified keys Claim) (Next) (derive) :
    (ready.entails Next derive).factories = ready.factories := rfl

/-- Intermediate proof contracts can be omitted; the complete certificate agrees. -/
theorem Certified.entails_trans (ready : Certified keys Claim) (Next)
    (derive : ∀ c data, Claim c data → Next c data)
    (Final : ∀ c, Results Value c keys → Prop) (finish : ∀ c data, Next c data → Final c data) :
    (ready.entails Next derive).entails Final finish =
      ready.entails Final (fun c data proof => finish c data (derive c data proof)) := rfl

/-- Preserve built data and exact family alignment while deriving the new proof. -/
def Snapshot.entails {context : Context} (data : Snapshot ready context) (Next)
    (derive : ∀ c data, Claim c data → Next c data) : Snapshot (ready.entails Next derive) context :=
  ⟨data.val, data.property.1, derive context data.val data.property.2⟩

@[simp] theorem Snapshot.entails_val {context : Context} (data : Snapshot ready context) (Next) (derive) :
    (data.entails Next derive).val = data.val := rfl

/-- Map only the retained proof. No factories, observers or constructors run.
The Option/context wrapper is mapped; no Results tuple is traversed or rebuilt. -/
def ContextSlot.entails (slot : ContextSlot ready) (Next)
    (derive : ∀ c data, Claim c data → Next c data) : ContextSlot (ready.entails Next derive) :=
  ⟨slot.retained.map fun ⟨c, data⟩ => ⟨c, data.entails Next derive⟩⟩

@[simp] theorem ContextSlot.entails_empty (ready : Certified keys Claim) (Next) (derive) :
    (ContextSlot.empty ready).entails Next derive = ContextSlot.empty (ready.entails Next derive) := rfl

theorem ContextSlot.entails_retained (slot : ContextSlot ready) (context : Context)
    (data : Snapshot ready context) (saved : slot.retained = some ⟨context, data⟩) (Next) (derive) :
    (slot.entails Next derive).retained = some ⟨context, data.entails Next derive⟩ := by
  simp [ContextSlot.entails, saved]

theorem ContextSlot.entails_hit [DecidableEq Context] (slot : ContextSlot ready) (context : Context)
    (data : Snapshot ready context) (saved : slot.retained = some ⟨context, data⟩) (Next) (derive) :
    ((slot.entails Next derive).read context).2.2 = true := by
  rw [ContextSlot.read_hit _ context (data.entails Next derive)
    (slot.entails_retained context data saved Next derive)]

theorem ContextSlot.entails_consume [DecidableEq Context] (slot : ContextSlot ready) (Next)
    (derive : ∀ c data, Claim c data → Next c data) {Output : Context → Type x}
    (construct : ∀ c data, Next c data → Output c) (context : Context) :
    ((slot.entails Next derive).consume construct context).1 =
      ready.consume (fun c data proof => construct c data (derive c data proof)) context := by
  rw [ContextSlot.consume_value, Certified.consume_apply, Certified.consume_apply]
  rfl

end LeanPoo.Functional.Requirements
