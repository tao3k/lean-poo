import Init

/-! Complete sequential catalog admission before dynamic slot selection.
Host macro alias identity, metadata callbacks and source stability are premises. -/
namespace LeanPoo.Prototype.DescriptorReflection

/-- The public catalog's existing right fold: inspect suffix metadata before
the current entry, preserve source order in the result, and never demand values.
Entries have already undergone most-specific declaration selection. -/
def inspectCatalog (visible : Entry → Except String Bool) : List Entry → Except String (List Entry)
  | [] => .ok []
  | entry :: rest => do
    let tail ← inspectCatalog visible rest
    let includeEntry ← visible entry
    pure (if includeEntry then entry :: tail else tail)

/-- Finish the entire public catalog before resolving or executing a slot.
This models sequential observation; supplied callbacks and source stability are
premises, not proofs of Gerbil expansion, mutable storage or concurrency. -/
def catalogRead (entries : List (String × Entry))
    (visible : (String × Entry) → Except String Bool) (name : String)
    (read : Entry → Except String Result) : Except String Result := do
  let catalog ← inspectCatalog visible entries
  match catalog.find? (fun entry => entry.1 == name) with
  | none => .error "slot is hidden or undeclared"
  | some entry => read entry.2

/-- Pure all-visible metadata retains every entry in source order. -/
theorem inspectCatalog_all_visible (entries : List Entry) :
    inspectCatalog (fun _ => .ok true) entries = .ok entries := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    simp only [inspectCatalog, ih, bind, Except.bind]
    rfl

/-- A failed suffix prevents evaluation of every earlier metadata callback. -/
theorem inspectCatalog_suffix_error (visible : Entry → Except String Bool)
    (entry : Entry) (rest : List Entry) (message : String)
    (failed : inspectCatalog visible rest = .error message) :
    inspectCatalog visible (entry :: rest) = .error message := by
  simp [inspectCatalog, failed, bind, Except.bind]

/-- Catalog failure wins even when the requested name occurs at the front.
An early-exit name lookup is therefore not a valid replacement. -/
theorem catalogRead_metadata_error (entries : List (String × Entry))
    (visible : (String × Entry) → Except String Bool) (name : String)
    (read : Entry → Except String Result) (message : String)
    (failed : inspectCatalog visible entries = .error message) :
    catalogRead entries visible name read = .error message := by
  simp [catalogRead, failed, bind, Except.bind]

/-- Successful reflection delivers the exact selected current entry to the read,
including its original error; no previous successful admission is reused. -/
theorem catalogRead_selected (entries catalog : List (String × Entry))
    (visible : (String × Entry) → Except String Bool) (name : String)
    (read : Entry → Except String Result) (entry : String × Entry)
    (inspected : inspectCatalog visible entries = .ok catalog)
    (selected : catalog.find? (fun entry => entry.1 == name) = some entry) :
    catalogRead entries visible name read = read entry.2 := by
  simp [catalogRead, inspected, selected, bind, Except.bind]

/-- Once most-specific metadata hides a key, no read is selected for that key.
Most-specific deduplication is a separate premise exercised by host regressions. -/
theorem catalogRead_absent (entries catalog : List (String × Entry))
    (visible : (String × Entry) → Except String Bool) (name : String)
    (read : Entry → Except String Result)
    (inspected : inspectCatalog visible entries = .ok catalog)
    (absent : catalog.find? (fun entry => entry.1 == name) = none) :
    catalogRead entries visible name read = .error "slot is hidden or undeclared" := by
  simp [catalogRead, inspected, absent, bind, Except.bind]

/-- Identical frontend lowering gives identical COMPLETE observations, not only
the same catalog. Actual alias resolution and hygiene remain host obligations. -/
theorem catalogRead_congr (entries other : List (String × Entry))
    (visible : (String × Entry) → Except String Bool) (name : String)
    (read : Entry → Except String Result) (same : entries = other) :
    catalogRead entries visible name read = catalogRead other visible name read := by
  subst other
  rfl
end LeanPoo.Prototype.DescriptorReflection
