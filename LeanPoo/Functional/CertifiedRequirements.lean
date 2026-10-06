import LeanPoo.Functional.Requirements

/-! Prepare a heterogeneous consumer with its explicit joint data contract.
Proof fields are erased; this does not infer dependencies or analytic facts. -/
namespace LeanPoo.Functional.Requirements
universe u v w
variable {Context : Type u} {Key : Type v} {Value : Context → Key → Type w}

/-- Retained functions and a proof about their complete results at every context.
The contract may relate several capabilities, rather than each key separately. -/
structure Certified (keys : List Key)
    (Claim : ∀ context, Results Value context keys → Prop) where
  factories : Factories Context Value keys
  valid : ∀ context, Claim context (build factories context)

/-- Apply the retained functions and return data indexed by its joint proof.
No provider lookup, graph computation, or runtime predicate check is added. -/
def Certified.build {keys : List Key} {Claim : ∀ context, Results Value context keys → Prop}
    (ready : Certified keys Claim) (context : Context) :
    {data : Results Value context keys // Claim context data} :=
  ⟨Requirements.build ready.factories context, ready.valid context⟩

@[simp] theorem Certified.build_val {keys : List Key}
    {Claim : ∀ context, Results Value context keys → Prop}
    (ready : Certified keys Claim) (context : Context) :
    (ready.build context).val = Requirements.build ready.factories context := rfl

/-- Certify a tuple already prepared by any selection path, including the
indexed transaction APIs. The supplied analytic proof remains an obligation. -/
def certify {keys : List Key} (factories : Factories Context Value keys)
    (Claim : ∀ context, Results Value context keys → Prop)
    (valid : ∀ context, Claim context (build factories context)) : Certified keys Claim :=
  ⟨factories, valid⟩

/-- One all-or-error preparation. Admission proves the joint contract for an
exact selected tuple; missing keys retain their original first-error behavior. -/
def prepareCertified (provider : Provider Context Key Value) (keys : List Key)
    (Claim : ∀ context, Results Value context keys → Prop)
    (admit : ∀ factories, Selected provider keys factories →
      ∀ context, Claim context (build factories context)) : Except Key (Certified keys Claim) :=
  match ready : prepare provider keys with
  | .error key => .error key
  | .ok factories => .ok ⟨factories, admit factories ((prepare_ok_iff _ _ _).mp ready)⟩

/-- Erasing the certificate reproduces the complete original result, including
missing keys. Successful preparation runs once; proof admission is erased. -/
theorem prepareCertified_forget (provider : Provider Context Key Value) (keys : List Key)
    (Claim : ∀ context, Results Value context keys → Prop)
    (admit : ∀ factories, Selected provider keys factories →
      ∀ context, Claim context (build factories context)) :
    (prepareCertified provider keys Claim admit).map Certified.factories = prepare provider keys := by
  unfold prepareCertified
  split <;> rename_i ready
  · simp [Except.map, ready]
  · simp [Except.map, ready]

/-- Data determines the whole certified tuple: proof choices are irrelevant. -/
theorem Certified.ext {keys : List Key} {Claim : ∀ context, Results Value context keys → Prop}
    (left right : Certified keys Claim) (same : left.factories = right.factories) : left = right := by
  cases left; cases right; cases same; rfl

/-- Missing-key admission requires no complete tuple or proof. -/
theorem prepareCertified_error_iff (provider : Provider Context Key Value) (keys : List Key)
    (Claim : ∀ context, Results Value context keys → Prop)
    (admit : ∀ factories, Selected provider keys factories →
      ∀ context, Claim context (build factories context)) (key : Key) :
    prepareCertified provider keys Claim admit = .error key ↔ prepare provider keys = .error key := by
  unfold prepareCertified
  split <;> rename_i ready <;> simp [ready]

/-- Forgetting proofs is injective, including the exact error payload. -/
theorem Certified.forget_injective {keys : List Key}
    {Claim : ∀ context, Results Value context keys → Prop} :
    Function.Injective (fun outcome : Except Key (Certified keys Claim) =>
      outcome.map Certified.factories) := by
  intro left right same
  cases left with
  | error key =>
    cases right with
    | error other => simpa only [Except.map, Except.error.injEq] using same
    | ok b => simp [Except.map] at same
  | ok a =>
    cases right with
    | error key => simp [Except.map] at same
    | ok b =>
      apply congrArg Except.ok
      exact Certified.ext a b (Except.ok.inj same)

/-- Equal complete preparation results give equal certified results, even if
providers differ elsewhere and callers supply different admission proofs. -/
theorem prepareCertified_congr (provider other : Provider Context Key Value) (keys : List Key)
    (Claim : ∀ context, Results Value context keys → Prop)
    (admit : ∀ factories, Selected provider keys factories →
      ∀ context, Claim context (build factories context))
    (otherAdmit : ∀ factories, Selected other keys factories →
      ∀ context, Claim context (build factories context))
    (same : prepare other keys = prepare provider keys) :
    prepareCertified other keys Claim otherAdmit = prepareCertified provider keys Claim admit := by
  apply Certified.forget_injective
  change (prepareCertified other keys Claim otherAdmit).map Certified.factories =
    (prepareCertified provider keys Claim admit).map Certified.factories
  rw [prepareCertified_forget, prepareCertified_forget, same]

end LeanPoo.Functional.Requirements
