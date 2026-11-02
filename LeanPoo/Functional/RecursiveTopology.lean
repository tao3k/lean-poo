import LeanPoo.Functional.RecursiveMigration

/-! Old/new SCC discipline for selective recursive reclosure. Removed edges seed
their consumer, so splitting a former group cannot leave an old partner clean.
The runtime need not compute partitions on its ordinary invalidation path. Graphs
use a common finite name embedding; support/row changes use RecursiveMigration.
Complete declared reads and host source/identity correspondence remain premises.
This advances generalized MOP future work. -/
namespace LeanPoo.Functional.RecursiveTopology

/-- Consumer-to-dependency edges interpreted by existing finite path/SCC proofs. -/
def edge (reads : Fin n → List (Fin n)) (reader target : Fin n) : Bool := decide (target ∈ reads reader)

/-- Body changes and complete ordered footprint changes are current revision seeds. -/
def seed (old next : Fin n → List (Fin n)) (body : Fin n → Bool) (node : Fin n) : Bool :=
  body node || decide (old node ≠ next node)

/-- Reuse the existing positive least invalidation over the NEW dependency graph. -/
def dirty (old next : Fin n → List (Fin n)) (body : Fin n → Bool) : Fin n → Bool :=
  RecursiveMigration.invalidate next (seed old next body)

/-- A deleted edge dirties its consumer even though propagation cannot follow it. -/
theorem removed_edge_dirty (old next : Fin n → List (Fin n)) (body : Fin n → Bool) (reader target : Fin n)
    (before : target ∈ old reader) (after : target ∉ next reader) : dirty old next body reader = true := by
  have different : old reader ≠ next reader := by intro same; exact after (same ▸ before)
  exact RecursiveMigration.seed_dirty next (seed old next body) reader (by simp [seed,different])

/-- One old edge still propagates invalidation: either it survives, or its removal
already seeded the consumer. This is the split-group step absent from a naive
argument that considers only current reachability to a changed node. -/
theorem old_reader_dirty (old next : Fin n → List (Fin n)) (body : Fin n → Bool) (reader target : Fin n)
    (readsTarget : target ∈ old reader) (changed : dirty old next body target = true) :
    dirty old next body reader = true := by
  by_cases present : target ∈ next reader
  · exact RecursiveMigration.reader_dirty next (seed old next body) reader target present changed
  · exact removed_edge_dirty old next body reader target readsTarget present

/-- Current paths propagate without SCC discovery or group representatives. -/
theorem new_path_dirty (old next : Fin n → List (Fin n)) (body : Fin n → Bool)
    (path : StrongComponents.Reach (edge next) reader target) (changed : dirty old next body target = true) :
    dirty old next body reader = true := by
  induction path with
  | refl => exact changed
  | @step a b c direct rest ih =>
    exact RecursiveMigration.reader_dirty next (seed old next body) a b (by simpa [edge] using direct) (ih changed)

/-- Every old path also propagates, including across edges removed during splits. -/
theorem old_path_dirty (old next : Fin n → List (Fin n)) (body : Fin n → Bool)
    (path : StrongComponents.Reach (edge old) reader target) (changed : dirty old next body target = true) :
    dirty old next body reader = true := by
  induction path with
  | refl => exact changed
  | @step a b c direct rest ih =>
    exact old_reader_dirty old next body a b (by simpa [edge] using direct) (ih changed)

/-- All partners of an OLD SCC have equal current dirtiness, even after it splits. -/
theorem old_scc_atomic (old next : Fin n → List (Fin n)) (body : Fin n → Bool)
    (forward : StrongComponents.Reach (edge old) a b) (backward : StrongComponents.Reach (edge old) b a) :
    dirty old next body a = dirty old next body b := by
  cases left : dirty old next body a <;> cases right : dirty old next body b
  · rfl
  · have bad := old_path_dirty old next body forward right; simp [left] at bad
  · have bad := old_path_dirty old next body backward left; simp [right] at bad
  · rfl

/-- All members of a NEW merged SCC are rebuilt together as well. -/
theorem new_scc_atomic (old next : Fin n → List (Fin n)) (body : Fin n → Bool)
    (forward : StrongComponents.Reach (edge next) a b) (backward : StrongComponents.Reach (edge next) b a) :
    dirty old next body a = dirty old next body b := by
  cases left : dirty old next body a <;> cases right : dirty old next body b
  · rfl
  · have bad := new_path_dirty old next body forward right; simp [left] at bad
  · have bad := new_path_dirty old next body backward left; simp [right] at bad
  · rfl

/-- Retention requires unchanged complete reads, not merely equal computed values. -/
theorem clean_reads (old next : Fin n → List (Fin n)) (body : Fin n → Bool) (node : Fin n)
    (clean : dirty old next body node = false) : old node = next node := by
  by_cases same : old node = next node
  · exact same
  · have bad := RecursiveMigration.seed_dirty next (seed old next body) node (by simp [seed,same])
    simp [dirty,bad] at clean

/-- A clean root cannot have an old reachable dirty target. -/
theorem old_path_clean (old next : Fin n → List (Fin n)) (body : Fin n → Bool)
    (path : StrongComponents.Reach (edge old) reader target) (clean : dirty old next body reader = false) :
    dirty old next body target = false := by
  cases changed : dirty old next body target with
  | false => rfl
  | true => have bad := old_path_dirty old next body path changed; simp [clean] at bad

/-- A clean root cannot have a current reachable dirty target. -/
theorem new_path_clean (old next : Fin n → List (Fin n)) (body : Fin n → Bool)
    (path : StrongComponents.Reach (edge next) reader target) (clean : dirty old next body reader = false) :
    dirty old next body target = false := by
  cases changed : dirty old next body target with
  | false => rfl
  | true => have bad := new_path_dirty old next body path changed; simp [clean] at bad

/-- Every old path from a retained root survives in the current graph. -/
theorem clean_old_to_new (old next : Fin n → List (Fin n)) (body : Fin n → Bool)
    (path : StrongComponents.Reach (edge old) reader target) :
    dirty old next body reader = false → StrongComponents.Reach (edge next) reader target := by
  induction path with
  | refl node => intro _; exact .refl node
  | @step a b c direct rest ih =>
    intro clean
    have member : b ∈ next a := (clean_reads old next body a clean) ▸ (by simpa [edge] using direct : b ∈ old a)
    exact .step (by simpa [edge] using member)
      (ih (RecursiveMigration.clean_dependency next (seed old next body) a b member clean))

/-- Every new path from a retained root already existed in its admitted snapshot. -/
theorem clean_new_to_old (old next : Fin n → List (Fin n)) (body : Fin n → Bool)
    (path : StrongComponents.Reach (edge next) reader target) :
    dirty old next body reader = false → StrongComponents.Reach (edge old) reader target := by
  induction path with
  | refl node => intro _; exact .refl node
  | @step a b c direct rest ih =>
    intro clean
    have member : b ∈ next a := by simpa [edge] using direct
    have previous : b ∈ old a := (clean_reads old next body a clean).symm ▸ member
    exact .step (by simpa [edge] using previous)
      (ih (RecursiveMigration.clean_dependency next (seed old next body) a b member clean))

/-- Checked SCC membership is stable for every retained node, independent of
representative/row choices. Exact path certificates, not sampled totals, decide it. -/
theorem clean_same (old next : Fin n → List (Fin n)) (body : Fin n → Bool)
    (before : StrongComponents.Checked (edge old)) (after : StrongComponents.Checked (edge next))
    (clean : dirty old next body a = false) (b : Fin n) : before.same a b = true ↔ after.same a b = true := by
  constructor
  · intro same
    have both : before.rel a b = true ∧ before.rel b a = true := by simpa [StrongComponents.Checked.same] using same
    have forward := (before.exact a b).mp both.1
    have backward := (before.exact b a).mp both.2
    exact after.no_quotient_cycle a b (clean_old_to_new old next body forward clean)
      (clean_old_to_new old next body backward (old_path_clean old next body forward clean))
  · intro same
    have both : after.rel a b = true ∧ after.rel b a = true := by simpa [StrongComponents.Checked.same] using same
    have forward := (after.exact a b).mp both.1
    have backward := (after.exact b a).mp both.2
    exact before.no_quotient_cycle a b (clean_new_to_old old next body forward clean)
      (clean_new_to_old old next body backward (new_path_clean old next body forward clean))

/-- The old/new checked member sets agree for clean nodes. -/
theorem clean_members (old next : Fin n → List (Fin n)) (body : Fin n → Bool)
    (before : StrongComponents.Checked (edge old)) (after : StrongComponents.Checked (edge next))
    (clean : dirty old next body a = false) : before.members a = after.members a := by
  have predicates : before.same a = after.same a := by
    funext b
    have same := clean_same old next body before after clean b
    cases left : before.same a b <;> cases right : after.same a b <;> simp_all
  simp [StrongComponents.Checked.members,predicates]

/-- Every merge/split participant is dirty using footprint/body seeds alone.
No separate SCC pass is required on the ordinary construction path. -/
theorem membership_changed_dirty (old next : Fin n → List (Fin n)) (body : Fin n → Bool)
    (before : StrongComponents.Checked (edge old)) (after : StrongComponents.Checked (edge next))
    (changed : before.members a ≠ after.members a) : dirty old next body a = true := by
  cases found : dirty old next body a with
  | true => rfl
  | false => exact False.elim (changed (clean_members old next body before after found))

end LeanPoo.Functional.RecursiveTopology
