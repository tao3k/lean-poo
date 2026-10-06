import LeanPoo.Functional.CertifiedObservation

/-! Compile a proof-aware consumer over a complete prepared dependency family.
Construction is explicit; no analytic consequence or capability is inferred. -/
namespace LeanPoo.Functional.Requirements
universe u v w x y z
variable {Context : Type u} {Key : Type v} {Value : Context → Key → Type w}

/-- Build the dependency tuple once per context and pass its joint proof to a
user constructor. Output may itself contain dependent data and proof fields.
No provider lookup, preparation or graph computation occurs in this wrapper. -/
def Certified.consume {keys : List Key} {Claim : ∀ c, Results Value c keys → Prop}
    (ready : Certified keys Claim) {Output : Context → Type x}
    (construct : ∀ c data, Claim c data → Output c) : Factory Context Output :=
  fun c =>
    let data := ready.build c
    construct c data.val data.property

@[simp] theorem Certified.consume_apply {keys : List Key}
    {Claim : ∀ c, Results Value c keys → Prop} (ready : Certified keys Claim)
    {Output : Context → Type x} (construct : ∀ c data, Claim c data → Output c) (c : Context) :
    ready.consume construct c = construct c (Requirements.build ready.factories c) (ready.valid c) := rfl

/-- Equal retained data determines the consumer even if certificate proofs
were constructed differently. The constructor and joint Claim remain fixed. -/
theorem Certified.consume_congr {keys : List Key} {Claim : ∀ c, Results Value c keys → Prop}
    (left right : Certified keys Claim) {Output : Context → Type x}
    (construct : ∀ c data, Claim c data → Output c) (same : left.factories = right.factories) :
    left.consume construct = right.consume construct := by
  rw [Certified.ext left right same]

/-- A proof-aware public consumer survives an explicitly compatible internal
representation replacement. Hidden-field consumers are outside this contract. -/
theorem Certified.consume_observed {Other : Context → Key → Type y}
    {Observed : Context → Key → Type z} (keys : List Key)
    (expose : ∀ c key, Value c key → Observed c key)
    (reveal : ∀ c key, Other c key → Observed c key)
    (Public : ∀ c, Results Observed c keys → Prop)
    (ready : Certified keys (fun c data => Public c (observeResults expose data)))
    (candidate : Factories Context Other keys) (compatible)
    {Output : Context → Type x} (construct : ∀ c data, Public c data → Output c) :
    (ready.observe expose Public (fun _ _ proof => proof)).consume construct =
      ((Certified.replaceObserved keys expose reveal Public ready candidate compatible).observe
        reveal Public (fun _ _ proof => proof)).consume construct :=
  congrArg (fun certified => Certified.consume certified construct)
    (Certified.replaceObserved_public keys expose reveal Public ready candidate compatible)

/-- Prepare and compile a certified consumer in one all-or-error call. Missing
keys return before factory application; successful functions retain dependencies. -/
def prepareConsumer (provider : Provider Context Key Value) (keys : List Key)
    (Claim : ∀ c, Results Value c keys → Prop)
    (admit : ∀ factories, Selected provider keys factories → ∀ c, Claim c (build factories c))
    {Output : Context → Type x} (construct : ∀ c data, Claim c data → Output c) :
    Except Key (Factory Context Output) :=
  (prepareCertified provider keys Claim admit).map (fun ready => ready.consume construct)

/-- Consumer compilation preserves the exact first preparation error. -/
theorem prepareConsumer_error_iff (provider : Provider Context Key Value) (keys : List Key)
    (Claim : ∀ c, Results Value c keys → Prop) (admit)
    {Output : Context → Type x} (construct : ∀ c data, Claim c data → Output c) (key : Key) :
    prepareConsumer provider keys Claim admit construct = .error key ↔ prepare provider keys = .error key := by
  unfold prepareConsumer
  rw [← prepareCertified_error_iff provider keys Claim admit key]
  cases prepareCertified provider keys Claim admit <;> simp [Except.map]

end LeanPoo.Functional.Requirements
