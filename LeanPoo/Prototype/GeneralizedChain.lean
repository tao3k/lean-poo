import LeanPoo.Prototype.GeneralizedDependencies

/-! Future-work extension: finite, heterogeneous chains of certified components.
Each edge selects an explicit public view. Existing local closure and dependency
refresh supply every admission; the chain supplies sequencing, not an evaluator. -/
namespace LeanPoo.Prototype.Generalized

/-- Each stage may have different storage, interface, fragments and dependency.
Only selected dependency values require decidable equality. -/
inductive DependencyChain : Type → Type 1 where
  | done {Input : Type} : DependencyChain Input
  | link {Input Raw Cooked Fragment Next : Type} [DecidableEq Input]
      (family : Input → Protocol Raw Cooked Fragment)
      (fragments : List Fragment) (base : Raw) (select : Cooked → Next)
      (rest : DependencyChain Next) : DependencyChain Input

/-- Closure of a suffix is indexed by the actual preceding published interface. -/
def DependencyChain.Publication : DependencyChain Input → Input → Type
  | .done, _ => Unit
  | @DependencyChain.link _ _ _ _ _ _ family fragments base select rest, dependency =>
      (closed : Closed (family dependency) fragments base) ×'
        rest.Publication (select closed.interface)

/-- Builders return existing kernel-checked closure witnesses, or a refusal. -/
def DependencyChain.Builders (Error : Type) : DependencyChain Input → Type
  | .done => Unit
  | @DependencyChain.link _ _ _ _ _ _ family fragments base _ rest =>
      ((dependency : _) → Except Error (Closed (family dependency) fragments base)) × rest.Builders Error

/-- A receipt per stage retains the exact reuse premises and the selected suffix
index. There is no untyped list of claims standing in for closure evidence. -/
def DependencyChain.Refresh : (chain : DependencyChain Input) →
    {old : Input} → chain.Publication old → Input → Type
  | .done, _, _, _ => Unit
  | @DependencyChain.link _ _ _ _ _ _ _ _ _ select rest, _, original, revised =>
      (head : DependencyRefresh original.1 revised) ×'
        rest.Refresh original.2 (select head.closed.interface)

def DependencyChain.Refresh.publication : {chain : DependencyChain Input} →
    {old revised : Input} → {original : chain.Publication old} →
    chain.Refresh original revised → chain.Publication revised
  | .done, _, _, _, _ => ()
  | @DependencyChain.link _ _ _ _ _ _ _ _ _ _ _, _, _, _, refresh => ⟨refresh.1.closed,refresh.2.publication⟩

def DependencyChain.Refresh.reused : {chain : DependencyChain Input} →
    {old revised : Input} → {original : chain.Publication old} →
    chain.Refresh original revised → List Bool
  | .done, _, _, _, _ => []
  | @DependencyChain.link _ _ _ _ _ _ _ _ _ _ _, _, _, _, refresh => refresh.1.reused :: refresh.2.reused

/-- Compare every full local interface across two publications, even when the
external dependency indices differ. -/
def DependencyChain.SameInterfaces : (chain : DependencyChain Input) →
    {first second : Input} → chain.Publication first → chain.Publication second → Prop
  | .done, _, _, _, _ => True
  | @DependencyChain.link _ _ _ _ _ _ _ _ _ _ rest, _, _, first, second =>
      first.1.interface = second.1.interface ∧ rest.SameInterfaces first.2 second.2

theorem DependencyChain.Refresh.interfaces_same : {chain : DependencyChain Input} →
    {old revised : Input} → {original : chain.Publication old} →
    (refresh : chain.Refresh original revised) →
    (∀ flag ∈ refresh.reused, flag = true) → chain.SameInterfaces refresh.publication original
  | .done, _, _, _, _, _ => True.intro
  | @DependencyChain.link _ _ _ _ _ _ _ _ _ _ _, _, _, _, refresh, retained => by
      constructor
      · exact refresh.1.interface_same (retained _ (List.mem_cons_self ..))
      · exact refresh.2.interfaces_same (fun flag member => retained flag (List.mem_cons_of_mem _ member))

/-- Left-to-right refresh may stop invalidation at any unchanged selected view.
A refusal returns no partial publication and does not construct later stages.
Builder effects outside Except are not rolled back by this pure operation. -/
def DependencyChain.refresh : (chain : DependencyChain Input) →
    {old : Input} → (original : chain.Publication old) → (revised : Input) →
    chain.Builders Error → Except Error (chain.Refresh original revised)
  | .done, _, _, _, _ => .ok ()
  | @DependencyChain.link _ _ _ _ _ _ _ _ _ select rest, _, original, revised, builders => do
      let head ← original.1.refreshDependency revised builders.1
      let tail ← rest.refresh original.2 (select head.closed.interface) builders.2
      return ⟨head,tail⟩

/-- Initial publication follows the same exact selected-view indices. -/
def DependencyChain.publish : (chain : DependencyChain Input) → (dependency : Input) →
    chain.Builders Error → Except Error (chain.Publication dependency)
  | .done, _, _ => .ok ()
  | @DependencyChain.link _ _ _ _ _ _ _ _ _ select rest, dependency, builders => do
      let head ← builders.1 dependency
      let tail ← rest.publish (select head.interface) builders.2
      return ⟨head,tail⟩

variable {Input Raw Cooked Fragment Next Error : Type}

/-- A head refusal is independent of all suffix builders. -/
theorem DependencyChain.refresh_head_error
    {family : Input → Protocol Raw Cooked Fragment} [DecidableEq Input]
    {fragments : List Fragment} {base : Raw} {select : Cooked → Next}
    (rest : DependencyChain Next) {old revised : Input}
    (original : (DependencyChain.link family fragments base select rest).Publication old)
    (builders : (DependencyChain.link family fragments base select rest).Builders Error)
    (error : Error) (failed : original.1.refreshDependency revised builders.1 = .error error) :
    (DependencyChain.link family fragments base select rest).refresh original revised builders = .error error := by
  simp only [DependencyChain.refresh,failed]
  rfl

/-- A suffix refusal is propagated exactly, even after a successful prefix. -/
theorem DependencyChain.refresh_tail_error
    {family : Input → Protocol Raw Cooked Fragment} [DecidableEq Input]
    {fragments : List Fragment} {base : Raw} {select : Cooked → Next}
    (rest : DependencyChain Next) {old revised : Input}
    (original : (DependencyChain.link family fragments base select rest).Publication old)
    (builders : (DependencyChain.link family fragments base select rest).Builders Error)
    (head : DependencyRefresh original.1 revised)
    (accepted : original.1.refreshDependency revised builders.1 = .ok head)
    (error : Error)
    (failed : rest.refresh original.2 (select head.closed.interface) builders.2 = .error error) :
    (DependencyChain.link family fragments base select rest).refresh original revised builders = .error error := by
  simp only [DependencyChain.refresh,accepted]
  change (Except.bind (β := (DependencyChain.link family fragments base select rest).Refresh original revised)
    (rest.refresh original.2 (select head.closed.interface) builders.2)
    (fun tail => .ok ⟨head,tail⟩)) = .error error
  rw [failed]
  rfl

/-- Equal input bypasses the first builder, including a builder that refuses.
The selected interface equality then controls reuse at the next edge. -/
theorem DependencyChain.refresh_same_head
    {family : Input → Protocol Raw Cooked Fragment} [DecidableEq Input]
    {fragments : List Fragment} {base : Raw} {select : Cooked → Next}
    (rest : DependencyChain Next) {old revised : Input}
    (original : (DependencyChain.link family fragments base select rest).Publication old)
    (first second : (dependency : Input) → Except Error (Closed (family dependency) fragments base))
    (suffix : rest.Builders Error) (same : revised = old) :
    (DependencyChain.link family fragments base select rest).refresh original revised (first,suffix) =
      (DependencyChain.link family fragments base select rest).refresh original revised (second,suffix) := by
  simp only [DependencyChain.refresh,original.1.refreshDependency_same revised first second same]
  rfl

variable {U UC UF D DC DF Dependency : Type}

/-- Canonical product mounting allows a closed prefix to become the upstream
component of another edge. Repeated application gives multi-level storage. -/
def DependentComponents.pair (upstream : Protocol U UC UF)
    (downstream : Dependency → Protocol D DC DF) (select : UC → Dependency) :
    DependentComponents upstream downstream (U × D) (UC × DC) where
  upstreamFocus := ⟨Prod.fst,(fun value raw => (value,raw.2)),fun _ _ => rfl,fun _ => rfl,fun _ _ _ => rfl⟩
  downstreamFocus := ⟨Prod.snd,(fun value raw => (raw.1,value)),fun _ _ => rfl,fun _ => rfl,fun _ _ _ => rfl⟩
  independent := ⟨fun _ _ => rfl,fun _ _ => rfl,fun _ _ _ => rfl⟩
  select := select
  upstreamView := Prod.fst
  downstreamView := Prod.snd
  cook := fun raw => (upstream.cook raw.1,(downstream (select (upstream.cook raw.1))).cook raw.2)
  upstreamCompatible := fun _ => rfl
  downstreamCompatible := fun _ => rfl

/-- Combine a prefix and the next exact local witness using the existing close
construction. Neither methods nor cooked self are rebuilt by a new interpreter. -/
def DependentComponents.closePair {upstream : Protocol U UC UF}
    {downstream : Dependency → Protocol D DC DF} (select : UC → Dependency)
    {upFragments : List UF} {downFragments : List DF} {upBase : U} {downBase : D}
    (upClosed : Closed upstream upFragments upBase)
    (suffix : Closed (downstream (select upClosed.interface)) downFragments downBase) :
    Closed (DependentComponents.pair upstream downstream select).protocol
      (upFragments.map Sum.inl ++ downFragments.map Sum.inr) (upBase,downBase) :=
  (DependentComponents.pair upstream downstream select).close _ _
    (upClosed.reindexFragments _ (by simp only [leftFragments_append,leftFragments_map_left,leftFragments_map_right,List.append_nil]))
    (suffix.reindexFragments _ (by simp only [rightFragments_append,rightFragments_map_left,rightFragments_map_right,List.nil_append]))

theorem DependentComponents.closePair_interface {upstream : Protocol U UC UF}
    {downstream : Dependency → Protocol D DC DF} (select : UC → Dependency)
    {upFragments : List UF} {downFragments : List DF} {upBase : U} {downBase : D}
    (upClosed : Closed upstream upFragments upBase)
    (suffix : Closed (downstream (select upClosed.interface)) downFragments downBase) :
    (DependentComponents.closePair select upClosed suffix).interface = (upClosed.interface,suffix.interface) := by
  apply Prod.ext
  · exact (DependentComponents.pair upstream downstream select).close_upstream _ _ _ _
  · exact (DependentComponents.pair upstream downstream select).close_downstream _ _ _ _

end LeanPoo.Prototype.Generalized
