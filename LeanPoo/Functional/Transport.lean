import LeanPoo.Functional.Observation

/-! Reuse data-indexed evidence after a semantic replacement. Equality is
explicit: this does not infer analytic equivalence or change the context. -/
namespace LeanPoo.Functional.Factory

universe u v w

/-- Retain a witness family while replacing the data it refers to. The result
is indexed by the new data at the same context; the old witness body is kept. -/
def transport {Context : Type u} {Data : Context → Type v}
    (Witness : (context : Context) → Data context → Type w)
    {left right : Factory Context Data} (same : ∀ context, left context = right context)
    (witness : Factory Context (fun context => Witness context (left context))) :
    Factory Context (fun context => Witness context (right context)) :=
  fun context => (show Witness context (right context) from same context ▸ witness context)

@[simp] theorem transport_refl {Context : Type u} {Data : Context → Type v}
    (Witness : (context : Context) → Data context → Type w) (data : Factory Context Data)
    (witness : Factory Context (fun context => Witness context (data context))) :
    transport Witness (fun _ => rfl) witness = witness := rfl

private theorem cast_trans {Data : Type v} (Witness : Data → Type w)
    {a b c : Data} (first : a = b) (second : b = c) (witness : Witness a) :
    second ▸ (first ▸ witness) = (first.trans second) ▸ witness := by
  cases first; cases second; rfl

/-- Two certified replacements compose without changing the retained witness. -/
theorem transport_trans {Context : Type u} {Data : Context → Type v}
    (Witness : (context : Context) → Data context → Type w)
    {left middle right : Factory Context Data}
    (first : ∀ context, left context = middle context)
    (second : ∀ context, middle context = right context)
    (witness : Factory Context (fun context => Witness context (left context))) :
    transport Witness second (transport Witness first witness) =
      transport Witness (fun context => (first context).trans (second context)) witness := by
  funext context
  exact cast_trans (Witness context) (first context) (second context) (witness context)

/-- Going to equal replacement data and back returns the exact witness family. -/
theorem transport_roundtrip {Context : Type u} {Data : Context → Type v}
    (Witness : (context : Context) → Data context → Type w)
    {left right : Factory Context Data} (same : ∀ context, left context = right context)
    (witness : Factory Context (fun context => Witness context (left context))) :
    transport Witness (fun context => (same context).symm)
      (transport Witness same witness) = witness :=
  (transport_trans Witness same (fun context => (same context).symm) witness).trans
    (transport_refl Witness left witness)

/-- Transport an existing proposition-valued theorem directly, without PLift.
Use fromProof afterwards only when a Type-valued factory is needed. -/
theorem transportProof {Context : Type u} {Data : Context → Type v}
    (Claim : (context : Context) → Data context → Prop)
    {left right : Factory Context Data} (same : ∀ context, left context = right context)
    (prove : ∀ context, Claim context (left context)) :
    ∀ context, Claim context (right context) :=
  fun context => same context ▸ prove context

end LeanPoo.Functional.Factory
