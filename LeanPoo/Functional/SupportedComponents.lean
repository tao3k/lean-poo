import LeanPoo.Functional.GraphRevision

/-! Active finite support is separate from a fixed key/lens universe. Native SCC
validation rejects dangling reads before any construction, including on deletion. -/
namespace LeanPoo.Functional.StrongComponents

/-- Inactive universe positions cannot acquire paths through a current source. -/
def supportedEdge {n : Nat} (keys : List (Fin n)) (edge : Fin n → Fin n → Bool) (a b : Fin n) : Bool :=
  decide (a ∈ keys) && decide (b ∈ keys) && edge a b

/-- Finite support must be distinct and closed under every declared active read. -/
def SupportedLaws {n : Nat} (keys : List (Fin n)) (edge : Fin n → Fin n → Bool) : Prop :=
  keys.Nodup ∧ ∀ a b, a ∈ keys → edge a b = true → b ∈ keys

/-- Active source plus exact checked reachability over the declared lens universe. -/
structure Supported {n : Nat} (edge : Fin n → Fin n → Bool) where
  keys : List (Fin n)
  laws : SupportedLaws keys edge
  graph : Checked (supportedEdge keys edge)

/-- Validate reads BEFORE masking. Dropping a component with a surviving reader
must fail, rather than silently treating the dangling edge as absent. -/
def discoverSupported {n : Nat} (keys : List (Fin n)) (edge : Fin n → Fin n → Bool) : Option (Supported edge) :=
  letI : Decidable (SupportedLaws keys edge) := by unfold SupportedLaws; infer_instance
  if valid : SupportedLaws keys edge then
    (discover (supportedEdge keys edge)).map (fun graph => ⟨keys,valid,graph⟩)
  else none

/-- The accepted graph retains the exact requested active support. -/
theorem discoverSupported_keys {n : Nat} (keys : List (Fin n)) (edge : Fin n → Fin n → Bool)
    (source : Supported edge) (accepted : discoverSupported keys edge = some source) : source.keys = keys := by
  unfold discoverSupported at accepted
  split at accepted
  · cases found : discover (supportedEdge keys edge) with
    | none => simp [found] at accepted
    | some graph => simp only [found, Option.map] at accepted; cases accepted; rfl
  · contradiction

/-- Dangling deletion cannot produce an admitted graph certificate at all. -/
theorem discoverSupported_dangling {n : Nat} (keys : List (Fin n)) (edge : Fin n → Fin n → Bool)
    (reader dep : Fin n) (active : reader ∈ keys) (reads : edge reader dep = true) (missing : dep ∉ keys) :
    discoverSupported keys edge = none := by
  have invalid : ¬ SupportedLaws keys edge := fun laws => missing (laws.2 reader dep active reads)
  simp [discoverSupported, invalid]

/-- Every path starting at an active node stays inside current support. -/
theorem Reach.support_target {n : Nat} (keys : List (Fin n)) (edge : Fin n → Fin n → Bool)
    {a b : Fin n} (path : Reach (supportedEdge keys edge) a b) : a ∈ keys → b ∈ keys := by
  induction path with
  | refl => exact id
  | step direct _ ih =>
    intro _
    simp only [supportedEdge, Bool.and_eq_true, decide_eq_true_eq] at direct
    exact ih direct.1.2

/-- Masking introduces no invented paths in the original declared graph. -/
theorem Reach.forget_support {n : Nat} (keys : List (Fin n)) (edge : Fin n → Fin n → Bool)
    {a b : Fin n} (path : Reach (supportedEdge keys edge) a b) : Reach edge a b := by
  induction path with
  | refl key => exact .refl key
  | step direct _ ih =>
    simp only [supportedEdge, Bool.and_eq_true, decide_eq_true_eq] at direct
    exact .step direct.2 ih

/-- Validating every active read makes masking lossless on actual declared paths. -/
theorem Supported.lift_path {n : Nat} {edge : Fin n → Fin n → Bool} (source : Supported edge)
    {a b : Fin n} (path : Reach edge a b) : a ∈ source.keys → Reach (supportedEdge source.keys edge) a b := by
  induction path with
  | refl key => intro _; exact .refl key
  | @step a b c direct rest ih =>
    intro active
    have next := source.laws.2 a b active direct
    exact .step (by simp [supportedEdge, active, next, direct]) (ih next)

/-- Native groups enumerate active members only; inactive positions have no group. -/
def Supported.members {n : Nat} {edge : Fin n → Fin n → Bool} (source : Supported edge)
    (key : Fin n) : List (Fin n) := source.keys.filter (source.graph.same key)

/-- Accepted active membership is exactly mutual graph reachability in support. -/
theorem Supported.mem_members {n : Nat} {edge : Fin n → Fin n → Bool} (source : Supported edge)
    (key node : Fin n) : node ∈ source.members key ↔ node ∈ source.keys ∧
    Reach (supportedEdge source.keys edge) key node ∧ Reach (supportedEdge source.keys edge) node key := by
  simp [members, Checked.same, source.graph.exact]

/-- Active groups are exactly SCCs of the ORIGINAL validated declared graph. -/
theorem Supported.mem_members_declared {n : Nat} {edge : Fin n → Fin n → Bool} (source : Supported edge)
    (key node : Fin n) (active : key ∈ source.keys) : node ∈ source.members key ↔
    node ∈ source.keys ∧ Reach edge key node ∧ Reach edge node key := by
  rw [source.mem_members]
  constructor
  · rintro ⟨present,forward,back⟩
    exact ⟨present, forward.forget_support _ _, back.forget_support _ _⟩
  · rintro ⟨present,forward,back⟩
    exact ⟨present, source.lift_path forward active, source.lift_path back present⟩

/-- A removed component has no observable group even though its lens-universe
position still exists. This avoids conflating removal with an isolated singleton. -/
theorem Supported.inactive_members {n : Nat} {edge : Fin n → Fin n → Bool} (source : Supported edge)
    (key : Fin n) (inactive : key ∉ source.keys) : source.members key = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro node member
  have found := (source.mem_members key node).mp member
  exact inactive (Reach.support_target _ _ found.2.2 found.1)

/-- Active member-list changes include adding/removing singleton components;
ordinary full-universe SCC membership alone would miss an isolated addition. -/
def supportRevisionSeed {n : Nat} {oldEdge newEdge : Fin n → Fin n → Bool}
    (old : Supported oldEdge) (next : Supported newEdge) (body : Fin n → Bool) (key : Fin n) : Bool :=
  body key || decide (old.members key ≠ next.members key) || (List.finRange n).any
    (fun dep => decide (supportedEdge old.keys oldEdge key dep ≠ supportedEdge next.keys newEdge key dep))

/-- Invalidation is materialized only on active nodes; deleted slots are erased. -/
def Supported.dirty {n : Nat} {edge : Fin n → Fin n → Bool} (source : Supported edge)
    (seed : Fin n → Bool) (key : Fin n) : Bool :=
  if key ∈ source.keys then source.graph.dirty seed key else false

/-- Every changed active group rebuilds atomically in the new support. -/
theorem support_membership_dirty {n : Nat} {oldEdge newEdge : Fin n → Fin n → Bool}
    (old : Supported oldEdge) (next : Supported newEdge) (body : Fin n → Bool) (key : Fin n)
    (active : key ∈ next.keys) (moved : old.members key ≠ next.members key) :
    next.dirty (supportRevisionSeed old next body) key = true := by
  simp only [Supported.dirty, ite_eq_left active, Checked.dirty, List.any_eq_true, Bool.and_eq_true]
  exact ⟨key, by simp, next.graph.laws.1 key, by simp [supportRevisionSeed, moved]⟩

/-- Even a fresh isolated component must construct; an old singleton at the same
universe position is not a cached current component. -/
theorem added_component_dirty {n : Nat} {oldEdge newEdge : Fin n → Fin n → Bool}
    (old : Supported oldEdge) (next : Supported newEdge) (body : Fin n → Bool) (key : Fin n)
    (absent : key ∉ old.keys) (present : key ∈ next.keys) :
    next.dirty (supportRevisionSeed old next body) key = true := by
  apply support_membership_dirty old next body key present
  intro equal
  have member : key ∈ next.members key := (next.mem_members key key).mpr ⟨present,.refl key,.refl key⟩
  rw [← equal, old.inactive_members key absent] at member
  simp at member

/-- Removed slots cannot be retained as active cache entries. -/
theorem Supported.inactive_dirty {n : Nat} {edge : Fin n → Fin n → Bool} (source : Supported edge)
    (seed : Fin n → Bool) (key : Fin n) (inactive : key ∉ source.keys) : source.dirty seed key = false := by
  simp [dirty, inactive]

/-- Shared dependencies propagate changes through all current active services. -/
theorem Supported.reader_dirty {n : Nat} {edge : Fin n → Fin n → Bool} (source : Supported edge)
    (seed : Fin n → Bool) (reader dep : Fin n) (active : reader ∈ source.keys) (depActive : dep ∈ source.keys)
    (path : Reach (supportedEdge source.keys edge) reader dep) (changed : source.dirty seed dep = true) :
    source.dirty seed reader = true := by
  simp only [dirty, ite_eq_left active, ite_eq_left depActive] at changed ⊢
  exact source.graph.reader_dirty seed reader dep ((source.graph.exact reader dep).mpr path) changed
end LeanPoo.Functional.StrongComponents
