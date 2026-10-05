import LeanPoo.Functional.ContextSlot
import LeanPoo.Functional.ResultView

/-! Narrow a retained dependency-data cache without building factories. -/
namespace LeanPoo.Functional.Requirements
universe u v w x
variable {Context : Type u} {Key : Type v} {Value : Context → Key → Type w}
variable [DecidableEq Key]
variable {source : List Key} {Claim : ∀ c, Results Value c source → Prop}
variable {ready : Certified source Claim}

/-- Project aligned built data and derive the narrow joint proof over values. -/
def Snapshot.project {context : Context} (data : Snapshot ready context)
    (keys : List Key) (included : ∀ key ∈ keys, key ∈ source)
    (Narrow : ∀ c, Results Value c keys → Prop)
    (derive : ∀ c data, Claim c data → Narrow c (projectResults data keys included)) :
    Snapshot (ready.projectData keys included Narrow derive) context :=
  ⟨projectResults data.val keys included, by
    constructor
    · rw [Certified.projectData_factories, build_project, data.property.1]
    · exact derive context data.val data.property.2⟩

@[simp] theorem Snapshot.project_val {context : Context} (data : Snapshot ready context)
    (keys : List Key) (included : ∀ key ∈ keys, key ∈ source) (Narrow) (derive) :
    (data.project keys included Narrow derive).val = projectResults data.val keys included := rfl

/-- Retain the same context with only the requested data/proof. Empty stays empty.
Source order may be changed or duplicated; no factory or constructor is called. -/
def ContextSlot.project (slot : ContextSlot ready)
    (keys : List Key) (included : ∀ key ∈ keys, key ∈ source)
    (Narrow : ∀ c, Results Value c keys → Prop)
    (derive : ∀ c data, Claim c data → Narrow c (projectResults data keys included)) :
    ContextSlot (ready.projectData keys included Narrow derive) :=
  ⟨slot.retained.map fun ⟨context, data⟩ => ⟨context, data.project keys included Narrow derive⟩⟩

@[simp] theorem ContextSlot.project_empty (ready : Certified source Claim)
    (keys : List Key) (included : ∀ key ∈ keys, key ∈ source) (Narrow) (derive) :
    (ContextSlot.empty ready).project keys included Narrow derive =
      ContextSlot.empty (ready.projectData keys included Narrow derive) := rfl

/-- A populated cache projects to data at the identical dependent context. -/
theorem ContextSlot.project_retained (slot : ContextSlot ready) (context : Context)
    (data : Snapshot ready context) (retained : slot.retained = some ⟨context, data⟩)
    (keys : List Key) (included : ∀ key ∈ keys, key ∈ source) (Narrow) (derive) :
    (slot.project keys included Narrow derive).retained =
      some ⟨context, data.project keys included Narrow derive⟩ := by
  simp [ContextSlot.project, retained]

/-- Reading the projected populated cache at the same context is a hit. -/
theorem ContextSlot.project_hit [DecidableEq Context] (slot : ContextSlot ready)
    (context : Context) (data : Snapshot ready context)
    (retained : slot.retained = some ⟨context, data⟩)
    (keys : List Key) (included : ∀ key ∈ keys, key ∈ source) (Narrow) (derive) :
    ((slot.project keys included Narrow derive).read context).2.2 = true := by
  rw [ContextSlot.read_hit _ context (data.project keys included Narrow derive)
    (slot.project_retained context data retained keys included Narrow derive)]

/-- Narrow cached consumption agrees with projecting the original uncached data.
The output constructor still executes on every call. -/
theorem ContextSlot.project_consume [DecidableEq Context] (slot : ContextSlot ready)
    (keys : List Key) (included : ∀ key ∈ keys, key ∈ source) (Narrow) (derive)
    {Output : Context → Type x} (construct : ∀ c data, Narrow c data → Output c)
    (context : Context) :
    ((slot.project keys included Narrow derive).consume construct context).1 =
      construct context (projectResults (build ready.factories context) keys included)
        (derive context _ (ready.valid context)) := by
  rw [ContextSlot.consume_value, Certified.consume_apply]
  simp only [Certified.projectData_factories, build_project]

end LeanPoo.Functional.Requirements
