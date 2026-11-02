import LeanPoo.Prototype.GeneralizedFork

/-! Future-work extension: preserve explicit shared context through multiple
fork/join levels. Reuse compares the entire declared join key, including context;
retaining both branch closures alone does not establish that key is unchanged. -/
namespace LeanPoo.Prototype.Generalized
variable {Input Context LD RD L LC LF R RC RF Error : Type}
variable {left : LD → Protocol L LC LF} {right : RD → Protocol R RC RF}

/-- Reuse a declared fork under a view of a wider shared context. -/
def DependencyFork.contramap (fork : DependencyFork Input left right) (view : Context → Input) :
    DependencyFork Context left right :=
  ⟨fork.selectLeft ∘ view,fork.selectRight ∘ view,fork.leftFragments,fork.rightFragments,
    fork.leftBase,fork.rightBase⟩

theorem DependencyFork.contramap_id (fork : DependencyFork Input left right) : fork.contramap id = fork := rfl

theorem DependencyFork.contramap_compose (fork : DependencyFork Input left right)
    {Outer : Type} (first : Context → Input) (second : Outer → Context) :
    (fork.contramap first).contramap second = fork.contramap (first ∘ second) := rfl

/-- Reindex existing local evidence when the wider input projects to its index. -/
def DependencyFork.Publication.pullback {fork : DependencyFork Input left right}
    (view : Context → Input) (context : Context) (publication : fork.Publication (view context)) :
    (fork.contramap view).Publication context :=
  ⟨publication.leftClosed,publication.rightClosed⟩

theorem DependencyFork.Publication.pullback_interface {fork : DependencyFork Input left right}
    (view : Context → Input) (context : Context) (publication : fork.Publication (view context)) :
    (publication.pullback view context).closed.interface = publication.closed.interface := rfl

/-- The join may read both explicit shared input and complete refreshed branches.
The old join is indexed by old context; the new receipt uses revised context. -/
def DependencyFork.Refresh.joinWith {fork : DependencyFork Input left right} {old revised : Input}
    {original : fork.Publication old} (refresh : fork.Refresh original revised)
    {JD J JC JF : Type} [DecidableEq JD]
    {joinFamily : JD → Protocol J JC JF} (select : Input × (LC × RC) → JD)
    {fragments : List JF} {base : J}
    (originalJoin : Closed (joinFamily (select (old,original.closed.interface))) fragments base)
    (build : (dependency : JD) → Except Error (Closed (joinFamily dependency) fragments base)) :
    Except Error (DependencyRefresh originalJoin (select (revised,refresh.publication.closed.interface))) :=
  originalJoin.refreshDependency (select (revised,refresh.publication.closed.interface)) build

/-- The earlier branch-only join is the context-ignoring special case. -/
theorem DependencyFork.Refresh.joinWith_branches {fork : DependencyFork Input left right} {old revised : Input}
    {original : fork.Publication old} (refresh : fork.Refresh original revised)
    {JD J JC JF : Type} [DecidableEq JD]
    {joinFamily : JD → Protocol J JC JF} (select : LC × RC → JD)
    {fragments : List JF} {base : J}
    (originalJoin : Closed (joinFamily (select original.closed.interface)) fragments base)
    (build : (dependency : JD) → Except Error (Closed (joinFamily dependency) fragments base)) :
    refresh.joinWith (fun input => select input.2) originalJoin build = refresh.join select originalJoin build := rfl

/-- Equality of the whole declared key, rather than branch reuse markers,
licenses reuse and bypasses a refusing join builder. -/
theorem DependencyFork.Refresh.joinWith_reuses {fork : DependencyFork Input left right} {old revised : Input}
    {original : fork.Publication old} (refresh : fork.Refresh original revised)
    {JD J JC JF : Type} [DecidableEq JD]
    {joinFamily : JD → Protocol J JC JF} (select : Input × (LC × RC) → JD)
    {fragments : List JF} {base : J}
    (originalJoin : Closed (joinFamily (select (old,original.closed.interface))) fragments base)
    (build : (dependency : JD) → Except Error (Closed (joinFamily dependency) fragments base))
    (same : select (revised,refresh.publication.closed.interface) = select (old,original.closed.interface)) :
    ∃ joined, refresh.joinWith select originalJoin build = .ok joined ∧ joined.reused = true :=
  originalJoin.refreshDependency_reuses _ build same

theorem DependencyFork.Refresh.joinWith_same_view {fork : DependencyFork Input left right} {old revised : Input}
    {original : fork.Publication old} (refresh : fork.Refresh original revised)
    {JD J JC JF : Type} [DecidableEq JD]
    {joinFamily : JD → Protocol J JC JF} (select : Input × (LC × RC) → JD)
    {fragments : List JF} {base : J}
    (originalJoin : Closed (joinFamily (select (old,original.closed.interface))) fragments base)
    (first second : (dependency : JD) → Except Error (Closed (joinFamily dependency) fragments base))
    (same : select (revised,refresh.publication.closed.interface) = select (old,original.closed.interface)) :
    refresh.joinWith select originalJoin first = refresh.joinWith select originalJoin second :=
  originalJoin.refreshDependency_same _ first second same

/-- A changed contextual key requires fresh admission; refusal is exact. -/
theorem DependencyFork.Refresh.joinWith_error {fork : DependencyFork Input left right} {old revised : Input}
    {original : fork.Publication old} (refresh : fork.Refresh original revised)
    {JD J JC JF : Type} [DecidableEq JD]
    {joinFamily : JD → Protocol J JC JF} (select : Input × (LC × RC) → JD)
    {fragments : List JF} {base : J}
    (originalJoin : Closed (joinFamily (select (old,original.closed.interface))) fragments base)
    (build : (dependency : JD) → Except Error (Closed (joinFamily dependency) fragments base))
    (changed : select (revised,refresh.publication.closed.interface) ≠ select (old,original.closed.interface))
    (error : Error) (failed : build (select (revised,refresh.publication.closed.interface)) = .error error) :
    refresh.joinWith select originalJoin build = .error error :=
  originalJoin.refreshDependency_error _ build changed error failed

end LeanPoo.Prototype.Generalized
