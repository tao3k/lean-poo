import LeanPoo.Proof.Gerbil.GraphColdIndex

namespace FunflowDag

open GraphColdIndex

variable {Key : Type} [DecidableEq Key]

private theorem eraseDups_of_nodup (keys : List Key) (unique : keys.Nodup) :
    keys.eraseDups = keys := by
  induction keys with
  | nil => rfl
  | cons key rest ih =>
    obtain ⟨absent, tailUnique⟩ := List.nodup_cons.mp unique
    have keep : rest.filter (fun next => !next == key) = rest := by
      apply List.filter_eq_self.mpr
      intro next member
      have different : next ≠ key := fun equal => absent (equal ▸ member)
      simp [different]
    rw [List.eraseDups_cons, keep, ih tailUnique]

-- The previous handoff had no Computation for an empty row. A Computation
-- for a nonempty row went through keys!, which removed duplicate providers.
def computationRow (needs : List Key) : List Key :=
  if needs.isEmpty then [] else needs.eraseDups

theorem direct_reads_exact (supported : Key → Bool) (rows : Key → List Key)
    (checked : ∀ key, supported key = true → (rows key).Nodup) :
    admittedRow supported rows =
      admittedRow supported (fun key => computationRow (rows key)) := by
  apply cold_projection_exact
  · intro key found
    simp only [admittedRow, found, ite_true]
    cases h : rows key with
    | nil => rfl
    | cons provider rest =>
      have unique := h ▸ checked key found
      simp [computationRow, eraseDups_of_nodup _ unique]
  · intro key missing
    simp [admittedRow, missing]

-- Both paths use the same DFS. GraphColdIndex.hub_order_exact and
-- admitted_empty_order cover the owned scheduler's two shortcuts.
-- Preserve the whole result, including the first unsupported vertex or cycle.
-- The wave fold still sees the original roster, incoming and outgoing rows.
theorem plan_exact {Failure Plan : Type} (keys : List Key)
    (supported : Key → Bool) (incoming outgoing : Key → List Key)
    (checked : ∀ key, supported key = true → (incoming key).Nodup)
    (order : List Key → Rows Key → Except Failure (List Key))
    (waves : List Key → (Key → List Key) → (Key → List Key) → List Key → Plan) :
    (order keys (admittedRow supported incoming)).map (waves keys incoming outgoing) =
      (order keys (admittedRow supported (fun key => computationRow (incoming key)))).map
        (waves keys incoming outgoing) := by
  rw [direct_reads_exact supported incoming checked]

#print axioms plan_exact

end FunflowDag
