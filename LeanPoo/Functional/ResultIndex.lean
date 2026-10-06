import LeanPoo.Functional.ResultView
import Std.Data.DHashMap.Lemmas

/-! Retain a dependent hash index of built values. The exact data/context index
prevents substituting another tuple; duplicate names keep the first value. -/
namespace LeanPoo.Functional.Requirements
universe u v w
variable {Context : Type u} {Key : Type v} {Value : Context → Key → Type w}
variable [BEq Key] [Hashable Key] [LawfulBEq Key] [DecidableEq Key]

private def resultTable {context : Context} : {source : List Key} →
    Results Value context source → Std.DHashMap Key (Value context)
  | [], _ => ∅
  | key :: _, (head, tail) => (resultTable tail).insert key head

private theorem resultTable_present {context : Context} {source : List Key}
    (data : Results Value context source) (key : Key) (member : key ∈ source) :
    (resultTable data).get? key = some (resultAt data key member) := by
  induction source with
  | nil => simp at member
  | cons head rest ih =>
    rcases data with ⟨value, tail⟩
    by_cases same : head = key
    · subst key; simp [resultTable, resultAt]
    · simpa [resultTable, Std.DHashMap.get?_insert, resultAt, same, Ne.symm same] using
        ih tail (by simpa [List.mem_cons, Ne.symm same] using member)

omit [DecidableEq Key] in
private theorem resultTable_absent {context : Context} {source : List Key}
    (data : Results Value context source) (key : Key) (absent : key ∉ source) :
    (resultTable data).get? key = none := by
  induction source with
  | nil => simp [resultTable]
  | cons head rest ih =>
    rcases data with ⟨value, tail⟩
    have different : key ≠ head := by intro same; subst key; simp at absent
    have missing : key ∉ rest := fun h => absent (List.mem_cons_of_mem head h)
    simp [resultTable, Std.DHashMap.get?_insert, Ne.symm different, ih tail missing]

/-- A retained map aligned to one exact built dependent tuple. -/
structure ResultIndex {context : Context} {source : List Key} (data : Results Value context source) where
  entries : Std.DHashMap Key (Value context)
  present : ∀ key member, entries.get? key = some (resultAt data key member)
  absent : ∀ key, key ∉ source → entries.get? key = none

/-- Build once by tail-first insertion so the first source occurrence wins. -/
def ResultIndex.ofResults {context : Context} {source : List Key} (data : Results Value context source) :
    ResultIndex data := ⟨resultTable data, resultTable_present data, resultTable_absent data⟩

variable {context : Context} {source : List Key} {data : Results Value context source}

def ResultIndex.find? (index : ResultIndex data) (key : Key) : Option (Value context key) :=
  index.entries.get? key

theorem ResultIndex.find?_present (index : ResultIndex data) (key : Key) (member : key ∈ source) :
    index.find? key = some (resultAt data key member) := index.present key member

theorem ResultIndex.find?_absent (index : ResultIndex data) (key : Key) (missing : key ∉ source) :
    index.find? key = none := index.absent key missing

/-- A membership proof rules out the missing branch; exactly one hash lookup. -/
def ResultIndex.get (index : ResultIndex data) (key : Key) (member : key ∈ source) : Value context key :=
  match found : index.find? key with
  | some value => value
  | none => False.elim (by have aligned := index.find?_present key member; rw [found] at aligned; cases aligned)

theorem ResultIndex.get_eq (index : ResultIndex data) (key : Key) (member : key ∈ source) :
    index.get key member = resultAt data key member := by
  unfold ResultIndex.get
  split
  · rename_i value found
    exact Option.some.inj (found.symm.trans (index.find?_present key member))
  · rename_i found
    have aligned := index.find?_present key member
    rw [found] at aligned
    cases aligned

/-- Repeated projections reuse this map; requested order/duplicates remain. -/
def ResultIndex.project (index : ResultIndex data) : (keys : List Key) →
    (∀ key ∈ keys, key ∈ source) → Results Value context keys
  | [], _ => PUnit.unit
  | key :: rest, included => (index.get key (included key (by simp)),
      index.project rest (fun key h => included key (by simp [h])))

theorem ResultIndex.project_eq (index : ResultIndex data) (keys : List Key)
    (included : ∀ key ∈ keys, key ∈ source) :
    index.project keys included = projectResults data keys included := by
  induction keys with
  | nil => rfl
  | cons key rest ih =>
    simp only [ResultIndex.project, projectResults, ResultIndex.get_eq]
    exact congrArg (fun tail => (resultAt data key _, tail)) (ih _)

end LeanPoo.Functional.Requirements
