import Std

namespace LeanPoo.Proof.Gerbil.GraphOwnerAcquisition

variable {Key Row Error : Type} [DecidableEq Key]

def replace (read : Key → Except Error Row) (owner : Key)
    (alternate : Except Error Row) : Key → Except Error Row :=
  fun key => if key = owner then alternate else read key

/-- Changing an owner that was never visited cannot change the rows or refusal
observed by that probe. The source can still have changed at that owner. -/
theorem unvisited_change_invisible (read : Key → Except Error Row) (keys : List Key)
    (owner : Key) (alternate : Except Error Row) (absent : owner ∉ keys) :
    keys.mapM (replace read owner alternate) = keys.mapM read := by
  induction keys with
  | nil => rfl
  | cons key rest ih =>
    have distinct : key ≠ owner := fun h => absent (h ▸ List.mem_cons_self)
    have tail : owner ∉ rest := fun h => absent (List.mem_cons_of_mem _ h)
    simp [List.mapM_cons, replace, distinct, ih tail]

omit [DecidableEq Key] in
/-- The ordinary full scan rejects at a given owner even when every prior
owner returned an accepted row. The suffix cannot swallow that refusal. -/
theorem first_refusal (read : Key → Except Error Row) (earlier later : List Key)
    (owner : Key) (cause : Error)
    (acceptedPrefix : ∃ rows, earlier.mapM read = .ok rows)
    (rejected : read owner = .error cause) :
    (earlier ++ owner :: later).mapM read = .error cause := by
  obtain ⟨rows, accepted⟩ := acceptedPrefix
  simp [List.mapM_append, List.mapM_cons, accepted, rejected, Bind.bind, Except.bind]

omit [DecidableEq Key] in
theorem constant_success (row : Row) (keys : List Key) :
    keys.mapM (fun _ => (.ok row : Except Error Row)) = .ok (keys.map (fun _ => row)) := by
  induction keys with
  | nil => rfl
  | cons key rest ih =>
    simp only [List.mapM_cons, List.map_cons, ih]
    rfl

/-- A source may refuse at an unvisited owner while a probe over the other
owners succeeds unchanged. A static row handoff needs separate source
authority. Charging the same owner names is insufficient. -/
theorem missing_owner_can_refuse (row : Row) (cause : Error) (owner : Key)
    (queried tail : List Key) (absent : owner ∉ queried) :
    let stock : Key → Except Error Row := fun _ => .ok row
    let changed := replace stock owner (.error cause)
    queried.mapM changed = queried.mapM stock ∧
      (queried ++ owner :: tail).mapM changed = .error cause := by
  dsimp only
  have unchanged := unvisited_change_invisible (fun _ => .ok row) queried owner (.error cause) absent
  refine ⟨unchanged, ?_⟩
  apply first_refusal
  · rw [unchanged]
    exact ⟨_, constant_success row queried⟩
  · simp [replace]

#print axioms missing_owner_can_refuse

end LeanPoo.Proof.Gerbil.GraphOwnerAcquisition
