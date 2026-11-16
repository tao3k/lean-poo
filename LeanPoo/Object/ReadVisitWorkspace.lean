import Std
namespace LeanPoo.Object.ReadVisitWorkspace
variable {Read : Type} [DecidableEq Read]

abbrev Index (Read : Type) := Read → Option Nat

abbrev visited (index : Index Read) (generation : Nat) (read : Read) : Prop :=
  index read = some generation

def mark (index : Index Read) (generation : Nat) (read : Read) : Index Read :=
  fun query => if query = read then some generation else index query

theorem mark_exact (index : Index Read) (generation : Nat) (read query : Read) :
    visited (mark index generation read) generation query ↔ query = read ∨ visited index generation query := by
  by_cases same : query = read <;> simp [visited, mark, same]

omit [DecidableEq Read] in
/-- A fresh generation makes a reused physical index logically empty. Old
successful visits never authenticate a record in the next build. -/
theorem fresh_is_empty (index : Index Read) (generation : Nat)
    (fresh : ∀ read, index read ≠ some generation) (read : Read) :
    ¬ visited index generation read := fresh read

/-- Receiver registration lives in its original separate index. Reusing only
this traversal workspace cannot change receiver positions or return guards. -/
theorem receiver_unchanged {Receiver : Type} (receivers : Receiver → Option Nat)
    (index : Index Read) (generation : Nat) (read : Read) :
    (mark index generation read, receivers).2 = receivers := rfl

/-- Native primitive allocation count, not a machine-time theorem. -/
theorem table_allocations (builds : Nat) (nonempty : 0 < builds) :
    builds + 1 ≤ 2 * builds := by omega

example (index : Index Nat) (old current read : Nat) (different : old ≠ current)
    (prior : index read = some old) : ¬ visited index current read := by
  simp [visited, prior, different]
end LeanPoo.Object.ReadVisitWorkspace

namespace LeanPoo.Object.ReadVisitWorkspace
variable {Read Error : Type} [DecidableEq Read]

def reference (check : Read → Except Error Unit) : List Read → (Read → Bool) → Except Error (List Read)
  | [], _ => .ok []
  | read :: rest, seen =>
      if seen read then reference check rest seen
      else do
        check read
        let tail ← reference check rest (fun query => if query = read then true else seen query)
        pure (read :: tail)

def stamped (check : Read → Except Error Unit) (generation : Nat) :
    List Read → Index Read → Except Error (List Read)
  | [], _ => .ok []
  | read :: rest, index =>
      if visited index generation read then stamped check generation rest index
      else do
        check read
        let tail ← stamped check generation rest (mark index generation read)
        pure (read :: tail)

/-- Equal first-visit decisions imply the same issued-record order AND first
refusal, not merely equal final membership. -/
theorem stamped_exact (check : Read → Except Error Unit) (generation : Nat)
    (reads : List Read) (index : Index Read) (seen : Read → Bool)
    (same : ∀ read, (visited index generation read) ↔ seen read = true) :
    stamped check generation reads index = reference check reads seen := by
  induction reads generalizing index seen with
  | nil => rfl
  | cons read rest ih =>
    simp only [stamped, reference]
    split
    · next prior =>
      have marked : seen read = true := (same read).mp prior
      simp only [marked, ↓reduceIte]
      exact ih index seen same
    · next prior =>
      have absent : seen read = false := by
        cases value : seen read <;> simp_all
      simp only [absent, Bool.false_eq_true, ↓reduceIte]
      cases check read <;> try rfl
      case ok value =>
        cases value
        have next : ∀ query, visited (mark index generation read) generation query ↔
            (if query = read then true else seen query) = true := by
          intro query
          by_cases equal : query = read
          · simp [visited, mark, equal]
          · simpa [visited, mark, equal] using same query
        simp only [Bind.bind, Except.bind]
        rw [ih (mark index generation read) _ next]
end LeanPoo.Object.ReadVisitWorkspace

namespace LeanPoo.Object.ReadVisitWorkspace
/-- The native frame records its creating thread even before allocating a
workspace. Retiring storage cannot transfer that ownership to a child. -/
def eligible (owner : Option Nat) (caller : Nat) : Bool := owner == some caller

theorem foreign_thread (owner caller : Nat) (different : owner ≠ caller) :
    eligible (some owner) caller = false := by simp [eligible, different]

theorem original_thread (owner : Nat) : eligible (some owner) owner = true := by simp [eligible]
end LeanPoo.Object.ReadVisitWorkspace

namespace LeanPoo.Object.ReadVisitWorkspace
theorem retired (caller : Nat) : eligible none caller = false := by simp [eligible]
end LeanPoo.Object.ReadVisitWorkspace
