import Std

namespace RevisionStream
variable {Owner Revision State Result : Type} [DecidableEq Revision]

-- read is a fixed, total, callback-free field read, not a user-supplied
-- getter. Captured source and revision spines are private proper lists.
def current (read : Owner → Revision) : List Owner → List Revision → Bool
  | [], [] => true
  | owner :: owners, version :: versions =>
      decide (version = read owner) && current read owners versions
  | _, _ => false

theorem current_exact (read : Owner → Revision)
    (owners : List Owner) (versions : List Revision) :
    current read owners versions = decide (versions = owners.map read) := by
  induction owners generalizing versions with
  | nil => cases versions <;> simp [current]
  | cons owner owners ih =>
    cases versions <;> simp [current, ih]

theorem wrong_length_refuses (read : Owner → Revision)
    (owners : List Owner) (versions : List Revision)
    (different : versions.length ≠ owners.length) :
    current read owners versions = false := by
  rw [current_exact]
  apply decide_eq_false
  intro same
  apply different
  simpa using congrArg List.length same

theorem unrelated_change (read next : Owner → Revision)
    (owners : List Owner) (versions : List Revision)
    (unchanged : ∀ owner ∈ owners, next owner = read owner) :
    current next owners versions = current read owners versions := by
  rw [current_exact, current_exact]
  rw [List.map_congr_left unchanged]

-- Admission/refusal continuations can have arbitrary effects or errors. Only
-- the pure field-reading interval changes, never either surrounding boundary.
theorem same_entry (read : Owner → Revision)
    (owners : List Owner) (versions : List Revision)
    (accept refuse : State → Result) (state : State) :
    (if current read owners versions then accept state else refuse state) =
      (if decide (versions = owners.map read) then accept state else refuse state) := by
  rw [current_exact]

-- Count field reads, independently of the machine cost of reading or
-- comparing a revision. A missing counterpart never needs a field read.
def fieldReads (read : Owner → Revision) : List Owner → List Revision → Nat
  | owner :: owners, version :: versions =>
      if version = read owner then 1 + fieldReads read owners versions else 1
  | _, _ => 0

theorem current_reads_all (read : Owner → Revision) (owners : List Owner) :
    fieldReads read owners (owners.map read) = owners.length := by
  induction owners with
  | nil => rfl
  | cons owner owners ih => simp [fieldReads, ih, Nat.add_comm]

theorem mismatch_reads_prefix (read : Owner → Revision)
    (matched : List Owner) (owner : Owner) (suffix : List Owner)
    (stale : Revision) (rest : List Revision) (different : stale ≠ read owner) :
    fieldReads read (matched ++ owner :: suffix) (matched.map read ++ stale :: rest) =
      matched.length + 1 := by
  induction matched with
  | nil => simp [fieldReads, different]
  | cons first matched ih => simp [fieldReads, ih, Nat.add_comm]

#print axioms current_exact
#print axioms wrong_length_refuses
#print axioms unrelated_change
#print axioms same_entry
#print axioms current_reads_all
#print axioms mismatch_reads_prefix
end RevisionStream
