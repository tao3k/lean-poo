import LeanPoo.Prototype.GeneralizedComponents

/-! Future-work extension: triangular cooked-interface dependencies. Storage
focuses remain independent; downstream closure is indexed by the selected
upstream view. No arbitrary dependency or termination inference is assumed. -/
namespace LeanPoo.Prototype.Generalized
open Functional

/-- The final self carries the exact dependency selecting the local protocol. -/
def familyCompiler (family : Dependency → Protocol Raw Cooked Fragment) :
    Compiler Raw (Dependency × Cooked) Fragment :=
  fun fragment self parent => (family self.get.1).compile fragment (self.map Prod.snd) parent

theorem family_assemble (family : Dependency → Protocol Raw Cooked Fragment)
    (fragments : List Fragment) (self : Thunk (Dependency × Cooked)) (parent : Thunk Raw)
    (dependency : Dependency) (selected : self.get.1 = dependency) :
    (familyCompiler family).assemble fragments self parent =
      (family dependency).assemble fragments (self.map Prod.snd) parent := by
  induction fragments with
  | nil => rfl
  | cons fragment rest ih =>
    change (family self.get.1).compile fragment (self.map Prod.snd)
      (Thunk.mk fun _ => (familyCompiler family).assemble rest self parent) = _
    rw [selected,ih]
    rfl

structure DependentComponents (upstream : Protocol U UC UF)
    (downstream : Dependency → Protocol D DC DF) (Whole Global : Type) where
  upstreamFocus : Focus Whole U
  downstreamFocus : Focus Whole D
  independent : Focus.Independent upstreamFocus downstreamFocus
  select : UC → Dependency
  upstreamView : Global → UC
  downstreamView : Global → DC
  cook : Whole → Global
  upstreamCompatible : ∀ whole, upstreamView (cook whole) = upstream.cook (upstreamFocus.get whole)
  downstreamCompatible : ∀ whole, downstreamView (cook whole) =
    (downstream (select (upstream.cook (upstreamFocus.get whole)))).cook (downstreamFocus.get whole)

variable {upstream : Protocol U UC UF} {downstream : Dependency → Protocol D DC DF}

def DependentComponents.mounting (components : DependentComponents upstream downstream Whole Global) :
    Mounting upstream.compile (familyCompiler downstream) Whole Global :=
  ⟨components.upstreamFocus,components.downstreamFocus,components.independent,
    components.upstreamView,(fun service => (components.select (components.upstreamView service),components.downstreamView service)),
    components.cook⟩

def DependentComponents.protocol (components : DependentComponents upstream downstream Whole Global) :
    Protocol Whole Global (Sum UF DF) := components.mounting.protocol

def DependentComponents.dependency (components : DependentComponents upstream downstream Whole Global) (whole : Whole) : Dependency :=
  components.select (upstream.cook (components.upstreamFocus.get whole))

theorem DependentComponents.step_partition (components : DependentComponents upstream downstream Whole Global)
    (fragments : List (Sum UF DF)) (final base : Whole) :
    components.protocol.step fragments final base =
      components.downstreamFocus.set
        ((downstream (components.dependency final)).step (rightFragments fragments)
          (components.downstreamFocus.get final) (components.downstreamFocus.get base))
        (components.upstreamFocus.set
          (upstream.step (leftFragments fragments) (components.upstreamFocus.get final) (components.upstreamFocus.get base)) base) := by
  unfold Protocol.step
  change components.mounting.protocol.assemble fragments (Thunk.mk fun _ => components.cook final) (Thunk.mk fun _ => base) = _
  rw [components.mounting.assemble_partition]
  rw [family_assemble downstream _ _ _ (components.dependency final) (by
    change components.select (components.upstreamView (components.cook final)) = _
    rw [components.upstreamCompatible]
    rfl)]
  change components.downstreamFocus.set
    ((downstream (components.dependency final)).assemble _ (Thunk.mk fun _ => components.downstreamView (components.cook final)) _)
    (components.upstreamFocus.set (upstream.assemble _ (Thunk.mk fun _ => components.upstreamView (components.cook final)) _) _) = _
  rw [components.upstreamCompatible,components.downstreamCompatible]
  rfl

theorem DependentComponents.approximate_upstream (components : DependentComponents upstream downstream Whole Global)
    (fragments : List (Sum UF DF)) (base seed : Whole) (depth : Nat) :
    components.upstreamFocus.get (components.protocol.approximate fragments base seed depth) =
      upstream.approximate (leftFragments fragments) (components.upstreamFocus.get base) (components.upstreamFocus.get seed) depth := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
    rw [Protocol.approximate_succ,components.step_partition]
    simp only [components.independent.left_read,components.upstreamFocus.get_set]
    rw [ih]
    rfl

/-- Downstream uses the dependency of the previous approximation, not a value
silently substituted from the newly computed upstream result. -/
theorem DependentComponents.downstream_succ (components : DependentComponents upstream downstream Whole Global)
    (fragments : List (Sum UF DF)) (base seed : Whole) (depth : Nat) :
    components.downstreamFocus.get (components.protocol.approximate fragments base seed (depth+1)) =
      (downstream (components.dependency (components.protocol.approximate fragments base seed depth))).step
        (rightFragments fragments) (components.downstreamFocus.get (components.protocol.approximate fragments base seed depth))
        (components.downstreamFocus.get base) := by
  rw [Protocol.approximate_succ,components.step_partition,components.downstreamFocus.get_set]

theorem DependentComponents.advance_downstream (components : DependentComponents upstream downstream Whole Global)
    (fragments : List (Sum UF DF)) (base seed : Whole) (start : Nat) (dependency : Dependency)
    (stable : ∀ extra, components.dependency (components.protocol.approximate fragments base seed (start+extra)) = dependency)
    (extra : Nat) :
    components.downstreamFocus.get (components.protocol.approximate fragments base seed (start+extra)) =
      (downstream dependency).approximate (rightFragments fragments) (components.downstreamFocus.get base)
        (components.downstreamFocus.get (components.protocol.approximate fragments base seed start)) extra := by
  induction extra with
  | zero => rfl
  | succ extra ih =>
    rw [Nat.add_succ,components.downstream_succ,stable extra,ih]
    rfl

/-- Close upstream first, then require closure of downstream at that exact selected view. -/
def DependentComponents.close (components : DependentComponents upstream downstream Whole Global)
    (fragments : List (Sum UF DF)) (base : Whole)
    (upstreamClosed : Closed upstream (leftFragments fragments) (components.upstreamFocus.get base))
    (downstreamClosed : Closed (downstream (components.select upstreamClosed.interface))
      (rightFragments fragments) (components.downstreamFocus.get base)) :
    Closed components.protocol fragments base where
  raw := components.downstreamFocus.set downstreamClosed.raw (components.upstreamFocus.set upstreamClosed.raw base)
  fixed := by
    rw [components.step_partition]
    change components.downstreamFocus.set
      ((downstream (components.select (upstream.cook (components.upstreamFocus.get
        (components.downstreamFocus.set downstreamClosed.raw (components.upstreamFocus.set upstreamClosed.raw base)))))).step _
        (components.downstreamFocus.get (components.downstreamFocus.set downstreamClosed.raw (components.upstreamFocus.set upstreamClosed.raw base))) _)
      (components.upstreamFocus.set (upstream.step _ (components.upstreamFocus.get
        (components.downstreamFocus.set downstreamClosed.raw (components.upstreamFocus.set upstreamClosed.raw base))) _) _) = _
    rw [components.independent.left_read,components.upstreamFocus.get_set,components.downstreamFocus.get_set]
    rw [upstreamClosed.fixed]
    change components.downstreamFocus.set
      ((downstream (components.select upstreamClosed.interface)).step _ downstreamClosed.raw _) _ = _
    rw [downstreamClosed.fixed]

theorem DependentComponents.close_upstream (components : DependentComponents upstream downstream Whole Global)
    (fragments : List (Sum UF DF)) (base : Whole)
    (upstreamClosed : Closed upstream (leftFragments fragments) (components.upstreamFocus.get base))
    (downstreamClosed : Closed (downstream (components.select upstreamClosed.interface))
      (rightFragments fragments) (components.downstreamFocus.get base)) :
    components.upstreamView (components.close fragments base upstreamClosed downstreamClosed).interface = upstreamClosed.interface := by
  change components.upstreamView (components.cook _) = _
  rw [components.upstreamCompatible]
  change upstream.cook (components.upstreamFocus.get
    (components.downstreamFocus.set downstreamClosed.raw (components.upstreamFocus.set upstreamClosed.raw base))) = _
  rw [components.independent.left_read,components.upstreamFocus.get_set]
  rfl

theorem DependentComponents.close_downstream (components : DependentComponents upstream downstream Whole Global)
    (fragments : List (Sum UF DF)) (base : Whole)
    (upstreamClosed : Closed upstream (leftFragments fragments) (components.upstreamFocus.get base))
    (downstreamClosed : Closed (downstream (components.select upstreamClosed.interface))
      (rightFragments fragments) (components.downstreamFocus.get base)) :
    components.downstreamView (components.close fragments base upstreamClosed downstreamClosed).interface = downstreamClosed.interface := by
  change components.downstreamView (components.cook _) = _
  rw [components.downstreamCompatible]
  change (downstream (components.select (upstream.cook (components.upstreamFocus.get
    (components.downstreamFocus.set downstreamClosed.raw (components.upstreamFocus.set upstreamClosed.raw base)))))).cook
    (components.downstreamFocus.get (components.downstreamFocus.set downstreamClosed.raw (components.upstreamFocus.set upstreamClosed.raw base))) = _
  rw [components.independent.left_read,components.upstreamFocus.get_set,components.downstreamFocus.get_set]
  rfl

/-- Storage grouping retains the actual fixed point, including dependent views. -/
def DependentComponents.regroup (components : DependentComponents upstream downstream Whole Global)
    {fragments : List (Sum UF DF)} {base : Whole} (closed : Closed components.protocol fragments base) :
    Closed components.protocol (groupedFragments fragments) base where
  raw := closed.raw
  fixed := by
    change components.mounting.protocol.assemble (groupedFragments fragments)
      (Thunk.mk fun _ => components.cook closed.raw) (Thunk.mk fun _ => base) = _
    rw [components.mounting.assemble_grouped]
    exact closed.fixed

theorem DependentComponents.regroup_interface (components : DependentComponents upstream downstream Whole Global)
    {fragments : List (Sum UF DF)} {base : Whole} (closed : Closed components.protocol fragments base) :
    (components.regroup closed).interface = closed.interface := rfl

theorem DependentComponents.frame (components : DependentComponents upstream downstream Whole Global)
    (fragments : List (Sum UF DF)) (base seed : Whole) (depth : Nat) (observe : Whole → Frame)
    (upstreamFrame : ∀ part whole, observe (components.upstreamFocus.set part whole) = observe whole)
    (downstreamFrame : ∀ part whole, observe (components.downstreamFocus.set part whole) = observe whole) :
    observe (components.protocol.approximate fragments base seed (depth+1)) = observe base := by
  rw [Protocol.approximate_succ,components.step_partition,downstreamFrame,upstreamFrame]

/-- Equality concerns the selected dependency, not the whole upstream interface. -/
def Closed.reuseDependency {family : Dependency → Protocol Raw Cooked Fragment} {old : Dependency}
    {fragments : List Fragment} {base : Raw} (closed : Closed (family old) fragments base)
    (revised : Dependency) (same : revised = old) : Closed (family revised) fragments base where
  raw := closed.raw
  fixed := by rw [same]; exact closed.fixed

theorem Closed.reuseDependency_interface {family : Dependency → Protocol Raw Cooked Fragment} {old : Dependency}
    {fragments : List Fragment} {base : Raw} (closed : Closed (family old) fragments base)
    (revised : Dependency) (same : revised = old) :
    (closed.reuseDependency revised same).interface = closed.interface := by cases same; rfl

/-- Reuse unchanged construction after proving equality of its ordered fragments. -/
def Closed.reindexFragments {protocol : Protocol Raw Cooked Fragment} {old : List Fragment} {base : Raw}
    (closed : Closed protocol old base) (revised : List Fragment) (same : revised = old) :
    Closed protocol revised base where
  raw := closed.raw
  fixed := by rw [same]; exact closed.fixed

structure DependencyRefresh {family : Dependency → Protocol Raw Cooked Fragment} {old : Dependency}
    {fragments : List Fragment} {base : Raw} (original : Closed (family old) fragments base) (revised : Dependency) where
  closed : Closed (family revised) fragments base
  reused : Bool
  sameDependency : reused = true → revised = old
  sameRaw : reused = true → closed.raw = original.raw

theorem DependencyRefresh.interface_same {family : Dependency → Protocol Raw Cooked Fragment} {old : Dependency}
    {fragments : List Fragment} {base : Raw} {original : Closed (family old) fragments base} {revised : Dependency}
    (refresh : DependencyRefresh original revised) (reused : refresh.reused = true) :
    refresh.closed.interface = original.interface := by
  change (family revised).cook refresh.closed.raw = (family old).cook original.raw
  rw [refresh.sameRaw reused,refresh.sameDependency reused]

/-- Explicit dependency equality bypasses reconstruction; changes require fresh
closure admission at the new dependency. Failure returns no new publication. -/
def Closed.refreshDependency {family : Dependency → Protocol Raw Cooked Fragment} [DecidableEq Dependency]
    {old : Dependency} {fragments : List Fragment} {base : Raw}
    (original : Closed (family old) fragments base) (revised : Dependency)
    (rebuild : (dependency : Dependency) → Except Error (Closed (family dependency) fragments base)) :
    Except Error (DependencyRefresh original revised) :=
  if same : revised = old then
    .ok ⟨original.reuseDependency revised same,true,fun _ => same,fun _ => rfl⟩
  else
    match rebuild revised with
    | .error error => .error error
    | .ok closed => .ok ⟨closed,false,by simp,by simp⟩

theorem Closed.refreshDependency_reuses {family : Dependency → Protocol Raw Cooked Fragment} [DecidableEq Dependency]
    {old : Dependency} {fragments : List Fragment} {base : Raw}
    (original : Closed (family old) fragments base) (revised : Dependency)
    (rebuild : (dependency : Dependency) → Except Error (Closed (family dependency) fragments base))
    (same : revised = old) :
    ∃ refresh, original.refreshDependency revised rebuild = .ok refresh ∧ refresh.reused = true := by
  subst revised
  simp [Closed.refreshDependency]

theorem Closed.refreshDependency_error {family : Dependency → Protocol Raw Cooked Fragment} [DecidableEq Dependency]
    {old : Dependency} {fragments : List Fragment} {base : Raw}
    (original : Closed (family old) fragments base) (revised : Dependency)
    (rebuild : (dependency : Dependency) → Except Error (Closed (family dependency) fragments base))
    (changed : revised ≠ old) (error : Error) (failed : rebuild revised = .error error) :
    original.refreshDependency revised rebuild = .error error := by
  simp [Closed.refreshDependency,changed,failed]

theorem Closed.refreshDependency_same {family : Dependency → Protocol Raw Cooked Fragment} [DecidableEq Dependency]
    {old : Dependency} {fragments : List Fragment} {base : Raw}
    (original : Closed (family old) fragments base) (revised : Dependency)
    (first second : (dependency : Dependency) → Except Error (Closed (family dependency) fragments base))
    (same : revised = old) :
    original.refreshDependency revised first = original.refreshDependency revised second := by
  simp [Closed.refreshDependency,same]

end LeanPoo.Prototype.Generalized
