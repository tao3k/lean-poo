import LeanPoo.Prototype.GeneralizedContext

/-! Future-work extension: configuration is part of a declared construction key.
Automatic reuse uses existing dependency refresh; recooking existing raw closure
requires the original compatible-self projection proof. -/
namespace LeanPoo.Prototype.Generalized

/-- Enrich the public interface without changing the certified raw fixed point. -/
def Closed.reindexSelf {protocol : Protocol Raw Cooked Fragment} {fragments : List Fragment} {base : Raw}
    (closed : Closed protocol fragments base) (view : Other → Cooked) (cook : Raw → Other)
    (compatible : ∀ raw, view (cook raw) = protocol.cook raw) :
    Closed (protocol.reindexSelf view cook) fragments base where
  raw := closed.raw
  fixed := by rw [protocol.step_reindexSelf view cook compatible]; exact closed.fixed

theorem Closed.reindexSelf_view {protocol : Protocol Raw Cooked Fragment} {fragments : List Fragment} {base : Raw}
    (closed : Closed protocol fragments base) (view : Other → Cooked) (cook : Raw → Other)
    (compatible : ∀ raw, view (cook raw) = protocol.cook raw) :
    view (closed.reindexSelf view cook compatible).interface = closed.interface := compatible closed.raw

/-- Configuration equality and selected dependency equality are both required.
A configuration value is actual family input, not an unverified version label. -/
def Closed.refreshConfiguration {Config Dependency Raw Cooked Fragment Error : Type}
    {family : Config → Dependency → Protocol Raw Cooked Fragment}
    [DecidableEq Config] [DecidableEq Dependency]
    {oldConfig : Config} {oldDependency : Dependency} {fragments : List Fragment} {base : Raw}
    (original : Closed (family oldConfig oldDependency) fragments base)
    (config : Config) (dependency : Dependency)
    (build : (config : Config) → (dependency : Dependency) → Except Error (Closed (family config dependency) fragments base)) :
    Except Error (DependencyRefresh (family := fun key : Config × Dependency => family key.1 key.2)
      (old := (oldConfig,oldDependency)) original (config,dependency)) :=
  original.refreshDependency (family := fun key : Config × Dependency => family key.1 key.2)
    (old := (oldConfig,oldDependency)) (config,dependency) (fun key => build key.1 key.2)

theorem Closed.refreshConfiguration_reuses {Config Dependency Raw Cooked Fragment Error : Type}
    {family : Config → Dependency → Protocol Raw Cooked Fragment}
    [DecidableEq Config] [DecidableEq Dependency]
    {oldConfig : Config} {oldDependency : Dependency} {fragments : List Fragment} {base : Raw}
    (original : Closed (family oldConfig oldDependency) fragments base) (config : Config) (dependency : Dependency)
    (build : (config : Config) → (dependency : Dependency) → Except Error (Closed (family config dependency) fragments base))
    (sameConfig : config = oldConfig) (sameDependency : dependency = oldDependency) :
    ∃ refreshed, original.refreshConfiguration config dependency build = .ok refreshed ∧ refreshed.reused = true :=
  original.refreshDependency_reuses (family := fun key : Config × Dependency => family key.1 key.2)
    (old := (oldConfig,oldDependency)) _ _ (Prod.ext sameConfig sameDependency)

theorem Closed.refreshConfiguration_error {Config Dependency Raw Cooked Fragment Error : Type}
    {family : Config → Dependency → Protocol Raw Cooked Fragment}
    [DecidableEq Config] [DecidableEq Dependency]
    {oldConfig : Config} {oldDependency : Dependency} {fragments : List Fragment} {base : Raw}
    (original : Closed (family oldConfig oldDependency) fragments base) (config : Config) (dependency : Dependency)
    (build : (config : Config) → (dependency : Dependency) → Except Error (Closed (family config dependency) fragments base))
    (changed : config ≠ oldConfig ∨ dependency ≠ oldDependency)
    (error : Error) (failed : build config dependency = .error error) :
    original.refreshConfiguration config dependency build = .error error := by
  apply original.refreshDependency_error (family := fun key : Config × Dependency => family key.1 key.2)
    (old := (oldConfig,oldDependency)) (config,dependency) (fun key => build key.1 key.2)
  · intro same
    cases changed with
    | inl different => exact different (congrArg Prod.fst same)
    | inr different => exact different (congrArg Prod.snd same)
  · exact failed

end LeanPoo.Prototype.Generalized
