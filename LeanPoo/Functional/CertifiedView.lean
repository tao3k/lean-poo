import LeanPoo.Functional.View
import LeanPoo.Functional.CachedPreparation

/-! Narrow joint certificates without treating a missing broad dependency as a
missing consumer dependency. Analytic consequences remain explicit premises. -/
namespace LeanPoo.Functional.Requirements
universe u v w
variable {Context : Type u} {Key : Type v} {Value : Context → Key → Type w}
variable [DecidableEq Key]

/-- Retain only declared functions and derive their joint contract from the
original proof. Projection scans the retained tuple, without provider lookups. -/
def Certified.project {source : List Key} {Claim : ∀ c, Results Value c source → Prop}
    (ready : Certified source Claim) (keys : List Key)
    (included : ∀ key ∈ keys, key ∈ source)
    (Narrow : ∀ c, Results Value c keys → Prop)
    (derive : ∀ c, Claim c (Requirements.build ready.factories c) →
      Narrow c (Requirements.build (Requirements.project ready.factories keys included) c)) : Certified keys Narrow :=
  ⟨Requirements.project ready.factories keys included, fun c => derive c (ready.valid c)⟩

@[simp] theorem Certified.project_factories {source : List Key}
    {Claim : ∀ c, Results Value c source → Prop} (ready : Certified source Claim)
    (keys : List Key) (included : ∀ key ∈ keys, key ∈ source)
    (Narrow : ∀ c, Results Value c keys → Prop) (derive) :
    (ready.project keys included Narrow derive).factories =
      Requirements.project ready.factories keys included := rfl

/-- A broad success supplies a narrow certificate without preparation. A broad
failure requires narrow preparation: the missing key may be unrequested.
Fresh admission and the analytic consequence are explicit, erased proofs. -/
def CachedPreparation.narrow (provider : Provider Context Key Value) (source keys : List Key)
    (Claim : ∀ c, Results Value c source → Prop) (Narrow : ∀ c, Results Value c keys → Prop)
    (cache : CachedPreparation provider source Claim)
    (included : ∀ key ∈ keys, key ∈ source)
    (derive : ∀ ready : Certified source Claim, ∀ c,
      Claim c (Requirements.build ready.factories c) → Narrow c (Requirements.build (Requirements.project ready.factories keys included) c))
    (admit : ∀ factories, Selected provider keys factories → ∀ c, Narrow c (build factories c)) :
    CachedPreparation provider keys Narrow :=
  match found : cache.outcome with
  | .error _ => cacheCertified provider keys Narrow admit
  | .ok ready =>
    ⟨.ok (ready.project keys included Narrow (derive ready)), by
      have broad : prepare provider source = .ok ready.factories := by
        rw [← cache.aligned, found]; rfl
      exact (project_ready provider ready.factories broad keys included).symm⟩

/-- The successful branch retains projected functions and the derived proof;
it does not invoke the fallback preparation. -/
theorem CachedPreparation.narrow_of_ok (provider : Provider Context Key Value) (source keys : List Key)
    (Claim : ∀ c, Results Value c source → Prop) (Narrow : ∀ c, Results Value c keys → Prop)
    (cache : CachedPreparation provider source Claim) (included : ∀ key ∈ keys, key ∈ source)
    (derive) (admit) (ready : Certified source Claim) (found : cache.outcome = .ok ready) :
    (cache.narrow provider source keys Claim Narrow included derive admit).outcome =
      .ok (ready.project keys included Narrow (derive ready)) := by
  unfold CachedPreparation.narrow
  split
  · rename_i key h
    rw [found] at h
    cases h
  · rename_i other h
    have same := Except.ok.inj (h.symm.trans found)
    subst other
    rfl

/-- The complete narrow result equals independent certified preparation,
including the narrow interface's own first missing key and duplicates. -/
theorem CachedPreparation.narrow_eq (provider : Provider Context Key Value) (source keys : List Key)
    (Claim : ∀ c, Results Value c source → Prop) (Narrow : ∀ c, Results Value c keys → Prop)
    (cache : CachedPreparation provider source Claim) (included : ∀ key ∈ keys, key ∈ source)
    (derive) (admit) :
    (cache.narrow provider source keys Claim Narrow included derive admit).outcome =
      prepareCertified provider keys Narrow admit := by
  apply Certified.forget_injective
  change (cache.narrow provider source keys Claim Narrow included derive admit).outcome.map Certified.factories =
    (prepareCertified provider keys Narrow admit).map Certified.factories
  rw [(cache.narrow provider source keys Claim Narrow included derive admit).aligned, prepareCertified_forget]

end LeanPoo.Functional.Requirements
