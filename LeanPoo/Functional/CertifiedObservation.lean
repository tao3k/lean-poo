import LeanPoo.Functional.Observation
import LeanPoo.Functional.CertifiedRequirements

/-! Reuse joint consumer evidence across explicitly equivalent public
observations, even when providers use different internal result types. -/
namespace LeanPoo.Functional.Requirements
universe u v w x y
variable {Context : Type u} {Key : Type v}
variable {Value : Context → Key → Type w} {Other : Context → Key → Type x}
variable {Observed : Context → Key → Type y}

/-- Observe an already built heterogeneous tuple. Only the supplied observation
functions run; no provider or factory is called. -/
def observeResults (expose : ∀ c key, Value c key → Observed c key) {context : Context} :
    {keys : List Key} → Results Value context keys → Results Observed context keys
  | [], _ => PUnit.unit
  | key :: _, (value, tail) => (expose context key value, observeResults expose tail)

@[simp] theorem observeResults_id (data : Results Value context keys) :
    observeResults (fun _ _ value => value) data = data := by
  induction keys with
  | nil => cases data; rfl
  | cons key rest ih =>
    rcases data with ⟨head, tail⟩
    exact congrArg (fun remaining => (head, remaining)) (ih tail)

/-- Observing retained factories commutes with observing built data. -/
theorem build_observe (expose : ∀ c key, Value c key → Observed c key)
    (factories : Factories Context Value keys) (context : Context) :
    build (observe expose factories) context = observeResults expose (build factories context) := by
  induction keys with
  | nil => rfl
  | cons key rest ih =>
    rcases factories with ⟨factory, tail⟩
    exact congrArg (fun remaining => (expose context key (factory context), remaining)) (ih tail)

/-- Expose a certified public interface using an explicit analytic consequence
about its data. Internal values remain inaccessible through this certificate. -/
def Certified.observe {keys : List Key} {Claim : ∀ c, Results Value c keys → Prop}
    (ready : Certified keys Claim) (expose : ∀ c key, Value c key → Observed c key)
    (Public : ∀ c, Results Observed c keys → Prop)
    (derive : ∀ c data, Claim c data → Public c (observeResults expose data)) :
    Certified keys Public :=
  ⟨Requirements.observe expose ready.factories, fun c => by
    rw [build_observe]
    exact derive c _ (ready.valid c)⟩

@[simp] theorem Certified.observe_factories {keys : List Key}
    {Claim : ∀ c, Results Value c keys → Prop} (ready : Certified keys Claim)
    (expose : ∀ c key, Value c key → Observed c key) (Public) (derive) :
    (ready.observe expose Public derive).factories = Requirements.observe expose ready.factories := rfl

/-- Replace internal data while retaining a joint theorem stated only over its
public observation. Compatibility and candidate availability are explicit;
this performs no preparation, dependency inference or analytic proof search. -/
def Certified.replaceObserved (keys : List Key)
    (expose : ∀ c key, Value c key → Observed c key)
    (reveal : ∀ c key, Other c key → Observed c key)
    (Public : ∀ c, Results Observed c keys → Prop)
    (ready : Certified keys (fun c data => Public c (observeResults expose data)))
    (candidate : Factories Context Other keys)
    (compatible : Related (fun c key a b => expose c key a = reveal c key b)
      keys ready.factories candidate) :
    Certified keys (fun c data => Public c (observeResults reveal data)) :=
  ⟨candidate, fun c => by
    have same := congrArg (fun factories => Requirements.build factories c)
      (observe_congr expose reveal keys ready.factories candidate compatible)
    rw [build_observe, build_observe] at same
    rw [← same]
    exact ready.valid c⟩

@[simp] theorem Certified.replaceObserved_factories (keys : List Key)
    (expose : ∀ c key, Value c key → Observed c key)
    (reveal : ∀ c key, Other c key → Observed c key)
    (Public : ∀ c, Results Observed c keys → Prop)
    (ready : Certified keys (fun c data => Public c (observeResults expose data)))
    (candidate : Factories Context Other keys) (compatible) :
    (Certified.replaceObserved keys expose reveal Public ready candidate compatible).factories = candidate := rfl

/-- The entire certified public interface is preserved, including arbitrary
joint Claims. Equality of hidden data or proof terms is not required. -/
theorem Certified.replaceObserved_public (keys : List Key)
    (expose : ∀ c key, Value c key → Observed c key)
    (reveal : ∀ c key, Other c key → Observed c key)
    (Public : ∀ c, Results Observed c keys → Prop)
    (ready : Certified keys (fun c data => Public c (observeResults expose data)))
    (candidate : Factories Context Other keys) (compatible) :
    ready.observe expose Public (fun _ _ proof => proof) =
      (Certified.replaceObserved keys expose reveal Public ready candidate compatible).observe
        reveal Public (fun _ _ proof => proof) := by
  apply Certified.ext
  change Requirements.observe expose ready.factories = Requirements.observe reveal candidate
  exact observe_congr expose reveal keys ready.factories candidate compatible

end LeanPoo.Functional.Requirements
