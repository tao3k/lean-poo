import LeanPoo.Prototype.GeneralizedChain

/-! Future-work extension: independently refreshed branches from one declared
input, joined through their exact cooked interfaces. This reuses existing
independent mounting and dependency refresh; no graph discovery is inferred. -/
namespace LeanPoo.Prototype.Generalized

variable {Input LD RD L LC LF R RC RF Error : Type}

/-- Canonical independent product mounting, preserving both full interfaces. -/
def Components.pair (left : Protocol L LC LF) (right : Protocol R RC RF) :
    Components left right (L × R) (LC × RC) where
  leftFocus := ⟨Prod.fst,(fun value raw => (value,raw.2)),fun _ _ => rfl,fun _ => rfl,fun _ _ _ => rfl⟩
  rightFocus := ⟨Prod.snd,(fun value raw => (raw.1,value)),fun _ _ => rfl,fun _ => rfl,fun _ _ _ => rfl⟩
  independent := ⟨fun _ _ => rfl,fun _ _ => rfl,fun _ _ _ => rfl⟩
  leftView := Prod.fst
  rightView := Prod.snd
  cook := fun raw => (left.cook raw.1,right.cook raw.2)
  leftCompatible := fun _ => rfl
  rightCompatible := fun _ => rfl

/-- Two branches can select different dependency types from the same input. -/
structure DependencyFork (Input : Type) (left : LD → Protocol L LC LF)
    (right : RD → Protocol R RC RF) where
  selectLeft : Input → LD
  selectRight : Input → RD
  leftFragments : List LF
  rightFragments : List RF
  leftBase : L
  rightBase : R

variable {left : LD → Protocol L LC LF} {right : RD → Protocol R RC RF}

abbrev DependencyFork.components (fork : DependencyFork Input left right) (input : Input) :=
  Components.pair (left (fork.selectLeft input)) (right (fork.selectRight input))

def DependencyFork.family (fork : DependencyFork Input left right) (input : Input) :=
  (fork.components input).protocol

def DependencyFork.fragments (fork : DependencyFork Input left right) : List (Sum LF RF) :=
  fork.leftFragments.map Sum.inl ++ fork.rightFragments.map Sum.inr

def DependencyFork.base (fork : DependencyFork Input left right) : L × R :=
  (fork.leftBase,fork.rightBase)

/-- Both closures are indexed by views of one input, never mixed revisions. -/
structure DependencyFork.Publication (fork : DependencyFork Input left right) (input : Input) where
  leftClosed : Closed (left (fork.selectLeft input)) fork.leftFragments fork.leftBase
  rightClosed : Closed (right (fork.selectRight input)) fork.rightFragments fork.rightBase

def DependencyFork.Publication.closed {fork : DependencyFork Input left right} {input : Input}
    (publication : fork.Publication input) : Closed (fork.family input) fork.fragments fork.base :=
  (fork.components input).close _ _
    (publication.leftClosed.reindexFragments _ (by simp only [DependencyFork.fragments,
      leftFragments_append,leftFragments_map_left,leftFragments_map_right,List.append_nil]))
    (publication.rightClosed.reindexFragments _ (by simp only [DependencyFork.fragments,
      rightFragments_append,rightFragments_map_left,rightFragments_map_right,List.nil_append]))

/-- Assemble any interleaving under equality of both complete ordered projections. -/
def DependencyFork.Publication.closeInterleaved {fork : DependencyFork Input left right} {input : Input}
    (publication : fork.Publication input) (fragments : List (Sum LF RF))
    (sameLeft : LeanPoo.Prototype.Generalized.leftFragments fragments = fork.leftFragments)
    (sameRight : LeanPoo.Prototype.Generalized.rightFragments fragments = fork.rightFragments) :
    Closed (fork.family input) fragments fork.base :=
  (fork.components input).close _ _
    (publication.leftClosed.reindexFragments _ sameLeft)
    (publication.rightClosed.reindexFragments _ sameRight)

/-- For a fixed input, every finite branch projection is its existing local
iteration. No synchronous dependency on the other branch is introduced. -/
theorem DependencyFork.approximate_left (fork : DependencyFork Input left right) (input : Input)
    (seed : L × R) (depth : Nat) :
    ((fork.family input).approximate fork.fragments fork.base seed depth).1 =
      (left (fork.selectLeft input)).approximate fork.leftFragments fork.leftBase seed.1 depth := by
  have law := (fork.components input).approximate_left fork.fragments fork.base seed depth
  simpa only [DependencyFork.family,DependencyFork.components,Components.pair,DependencyFork.base,DependencyFork.fragments,leftFragments_append,leftFragments_map_left,
    leftFragments_map_right,List.append_nil] using law

theorem DependencyFork.approximate_right (fork : DependencyFork Input left right) (input : Input)
    (seed : L × R) (depth : Nat) :
    ((fork.family input).approximate fork.fragments fork.base seed depth).2 =
      (right (fork.selectRight input)).approximate fork.rightFragments fork.rightBase seed.2 depth := by
  have law := (fork.components input).approximate_right fork.fragments fork.base seed depth
  simpa only [DependencyFork.family,DependencyFork.components,Components.pair,DependencyFork.base,DependencyFork.fragments,rightFragments_append,rightFragments_map_left,
    rightFragments_map_right,List.nil_append] using law

theorem DependencyFork.Publication.interface {fork : DependencyFork Input left right} {input : Input}
    (publication : fork.Publication input) :
    publication.closed.interface = (publication.leftClosed.interface,publication.rightClosed.interface) := by
  apply Prod.ext
  · exact (fork.components input).close_left _ _ _ _
  · exact (fork.components input).close_right _ _ _ _

structure DependencyFork.Refresh {fork : DependencyFork Input left right} {old : Input}
    (original : fork.Publication old) (revised : Input) where
  left : DependencyRefresh original.leftClosed (fork.selectLeft revised)
  right : DependencyRefresh original.rightClosed (fork.selectRight revised)

def DependencyFork.Refresh.publication {fork : DependencyFork Input left right} {old revised : Input}
    {original : fork.Publication old} (refresh : fork.Refresh original revised) : fork.Publication revised :=
  ⟨refresh.left.closed,refresh.right.closed⟩

def DependencyFork.refresh (fork : DependencyFork Input left right) [DecidableEq LD] [DecidableEq RD]
    {old : Input} (original : fork.Publication old) (revised : Input)
    (buildLeft : (dependency : LD) → Except Error (Closed (left dependency) fork.leftFragments fork.leftBase))
    (buildRight : (dependency : RD) → Except Error (Closed (right dependency) fork.rightFragments fork.rightBase)) :
    Except Error (fork.Refresh original revised) := do
  let freshLeft ← original.leftClosed.refreshDependency (fork.selectLeft revised) buildLeft
  let freshRight ← original.rightClosed.refreshDependency (fork.selectRight revised) buildRight
  return ⟨freshLeft,freshRight⟩

def DependencyFork.publish (fork : DependencyFork Input left right) (input : Input)
    (buildLeft : (dependency : LD) → Except Error (Closed (left dependency) fork.leftFragments fork.leftBase))
    (buildRight : (dependency : RD) → Except Error (Closed (right dependency) fork.rightFragments fork.rightBase)) :
    Except Error (fork.Publication input) := do
  let leftClosed ← buildLeft (fork.selectLeft input)
  let rightClosed ← buildRight (fork.selectRight input)
  return ⟨leftClosed,rightClosed⟩

/-- Selecting from the assembled publication ties the join to both new branches. -/
def DependencyFork.Refresh.join {fork : DependencyFork Input left right} {old revised : Input}
    {original : fork.Publication old} (refresh : fork.Refresh original revised)
    {JD J JC JF : Type} [DecidableEq JD]
    {joinFamily : JD → Protocol J JC JF} (select : LC × RC → JD)
    {fragments : List JF} {base : J}
    (originalJoin : Closed (joinFamily (select original.closed.interface)) fragments base)
    (build : (dependency : JD) → Except Error (Closed (joinFamily dependency) fragments base)) :
    Except Error (DependencyRefresh originalJoin (select refresh.publication.closed.interface)) :=
  originalJoin.refreshDependency (select refresh.publication.closed.interface) build

theorem DependencyFork.Refresh.left_interface {fork : DependencyFork Input left right} {old revised : Input}
    {original : fork.Publication old} (refresh : fork.Refresh original revised) (reused : refresh.left.reused = true) :
    refresh.publication.closed.interface.1 = original.closed.interface.1 := by
  rw [DependencyFork.Publication.interface,DependencyFork.Publication.interface]
  exact refresh.left.interface_same reused

theorem DependencyFork.Refresh.right_interface {fork : DependencyFork Input left right} {old revised : Input}
    {original : fork.Publication old} (refresh : fork.Refresh original revised) (reused : refresh.right.reused = true) :
    refresh.publication.closed.interface.2 = original.closed.interface.2 := by
  rw [DependencyFork.Publication.interface,DependencyFork.Publication.interface]
  exact refresh.right.interface_same reused

/-- Retaining both branches preserves any declared join view and bypasses even
an unavailable join constructor. No equality of function-bearing Input is used. -/
theorem DependencyFork.Refresh.join_reuses {fork : DependencyFork Input left right} {old revised : Input}
    {original : fork.Publication old} (refresh : fork.Refresh original revised)
    {JD J JC JF : Type} [DecidableEq JD]
    {joinFamily : JD → Protocol J JC JF} (select : LC × RC → JD)
    {fragments : List JF} {base : J}
    (originalJoin : Closed (joinFamily (select original.closed.interface)) fragments base)
    (build : (dependency : JD) → Except Error (Closed (joinFamily dependency) fragments base))
    (leftReused : refresh.left.reused = true) (rightReused : refresh.right.reused = true) :
    ∃ joined, refresh.join select originalJoin build = .ok joined ∧ joined.reused = true := by
  apply originalJoin.refreshDependency_reuses
  exact congrArg select (Prod.ext (refresh.left_interface leftReused) (refresh.right_interface rightReused))

/-- The join view can remain equal even when a branch needed fresh evidence.
That equality bypasses either supplied join builder. -/
theorem DependencyFork.Refresh.join_same_view {fork : DependencyFork Input left right} {old revised : Input}
    {original : fork.Publication old} (refresh : fork.Refresh original revised)
    {JD J JC JF : Type} [DecidableEq JD]
    {joinFamily : JD → Protocol J JC JF} (select : LC × RC → JD)
    {fragments : List JF} {base : J}
    (originalJoin : Closed (joinFamily (select original.closed.interface)) fragments base)
    (first second : (dependency : JD) → Except Error (Closed (joinFamily dependency) fragments base))
    (same : select refresh.publication.closed.interface = select original.closed.interface) :
    refresh.join select originalJoin first = refresh.join select originalJoin second :=
  originalJoin.refreshDependency_same _ first second same

/-- Failure of the left branch skips the right builder; no partial publication. -/
theorem DependencyFork.refresh_left_error (fork : DependencyFork Input left right)
    [DecidableEq LD] [DecidableEq RD] {old revised : Input} (original : fork.Publication old)
    (buildLeft : (dependency : LD) → Except Error (Closed (left dependency) fork.leftFragments fork.leftBase))
    (buildRight : (dependency : RD) → Except Error (Closed (right dependency) fork.rightFragments fork.rightBase))
    (error : Error) (failed : original.leftClosed.refreshDependency (fork.selectLeft revised) buildLeft = .error error) :
    fork.refresh original revised buildLeft buildRight = .error error := by
  simp only [DependencyFork.refresh,failed]
  rfl

/-- Right failure after an accepted left branch is forwarded exactly. -/
theorem DependencyFork.refresh_right_error (fork : DependencyFork Input left right)
    [DecidableEq LD] [DecidableEq RD] {old revised : Input} (original : fork.Publication old)
    (buildLeft : (dependency : LD) → Except Error (Closed (left dependency) fork.leftFragments fork.leftBase))
    (buildRight : (dependency : RD) → Except Error (Closed (right dependency) fork.rightFragments fork.rightBase))
    (freshLeft : DependencyRefresh original.leftClosed (fork.selectLeft revised))
    (accepted : original.leftClosed.refreshDependency (fork.selectLeft revised) buildLeft = .ok freshLeft)
    (error : Error) (failed : original.rightClosed.refreshDependency (fork.selectRight revised) buildRight = .error error) :
    fork.refresh original revised buildLeft buildRight = .error error := by
  simp only [DependencyFork.refresh,accepted]
  change (original.rightClosed.refreshDependency (fork.selectRight revised) buildRight).bind
    (β := fork.Refresh original revised) (fun freshRight => .ok ⟨freshLeft,freshRight⟩) = .error error
  rw [failed]
  rfl

end LeanPoo.Prototype.Generalized
