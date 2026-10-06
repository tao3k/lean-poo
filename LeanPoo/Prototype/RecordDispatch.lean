import LeanPoo.Prototype.Record

/-! A checked, function-valued view of typed records. An absent slot receives
the caller's error for that key, matching the paper's record-as-dispatcher
construction without fixing one error type or message policy. -/

namespace LeanPoo.Prototype

universe u v w

abbrev CheckedRecord (Key : Type u) (Value : Key → Type v)
    (Error : Type w) := (key : Key) → Except Error (Value key)

/-- Turn a typed record into a function that reports missing keys explicitly. -/
def Record.toChecked (record : Record Key Value)
    (missing : Key → Error) : CheckedRecord Key Value Error :=
  fun key => match record.lookup key with
    | some value => .ok value
    | none => .error (missing key)

theorem Record.toChecked_toOption (record : Record Key Value)
    (missing : Key → Error) (key : Key) :
    ((record.toChecked missing) key).toOption = record.lookup key := by
  cases h : record.lookup key <;> simp [Record.toChecked, h] <;> rfl

/-- Forget the error payload while retaining every successful slot. -/
def CheckedRecord.toRecord (source : CheckedRecord Key Value Error) :
    Record Key Value :=
  { lookup := fun key => (source key).toOption }

theorem CheckedRecord.toRecord_lookup
    (source : CheckedRecord Key Value Error) (key : Key) :
    (source.toRecord).lookup key = (source key).toOption := rfl

/-- Conversion back is exact when errors use the declared missing-key policy. -/
theorem CheckedRecord.toChecked_toRecord
    (source : CheckedRecord Key Value Error) (missing : Key → Error)
    (canonical : ∀ key error, source key = .error error → error = missing key) :
    source.toRecord.toChecked missing = source := by
  funext key
  cases h : source key with
  | ok value => simp [CheckedRecord.toRecord, Record.toChecked, h] <;> rfl
  | error error =>
    simp [CheckedRecord.toRecord, Record.toChecked, h, canonical key error h] <;> rfl

/-- A checked source wrapper that overrides one named slot. -/
def CheckedRecord.slot [DecidableEq Key] (key : Key) (value : Value key)
    (inherited : CheckedRecord Key Value Error) : CheckedRecord Key Value Error :=
  fun query =>
    if same : query = key then .ok (same.symm ▸ value)
    else inherited query

/-- A checked source wrapper that modifies an inherited named slot. -/
def CheckedRecord.modify [DecidableEq Key] (key : Key)
    (change : Value key → Value key)
    (inherited : CheckedRecord Key Value Error) : CheckedRecord Key Value Error :=
  fun query =>
    if same : query = key then same.symm ▸ (inherited key).map change
    else inherited query

/-- A checked wrapper whose value is calculated from final self. -/
def CheckedRecord.compute [DecidableEq Key] (key : Key)
    (calculate : CheckedRecord Key Value Error → Value key)
    (self inherited : CheckedRecord Key Value Error) : CheckedRecord Key Value Error :=
  CheckedRecord.slot key (calculate self) inherited

/-- Typed slot override has the same checked observations on every key. -/
theorem Record.toChecked_slot [DecidableEq Key]
    (key : Key) (value : Value key) (self inherited : Record Key Value)
    (missing : Key → Error) :
    ((Record.slot key value) self inherited).toChecked missing =
      CheckedRecord.slot key value (inherited.toChecked missing) := by
  funext query
  by_cases same : query = key
  · subst query
    simp [Record.toChecked, Record.slot, Record.slotGen, CheckedRecord.slot]
  · simp [Record.toChecked, Record.slot, Record.slotGen, CheckedRecord.slot, same]

/-- Typed inherited modification preserves success and missing-key errors. -/
theorem Record.toChecked_modify [DecidableEq Key]
    (key : Key) (change : Value key → Value key)
    (self inherited : Record Key Value) (missing : Key → Error) :
    ((Record.modify key change) self inherited).toChecked missing =
      CheckedRecord.modify key change (inherited.toChecked missing) := by
  funext query
  by_cases same : query = key
  · subst query
    cases h : inherited.lookup key with
    | none => simp [Record.toChecked, Record.modify, Record.slotGen,
        CheckedRecord.modify, h] <;> rfl
    | some value => simp [Record.toChecked, Record.modify, Record.slotGen,
        CheckedRecord.modify, h] <;> rfl
  · simp [Record.toChecked, Record.modify, Record.slotGen,
      CheckedRecord.modify, same]

/-- A final-self slot calculation commutes when the calculations agree on
related self values; inherited errors continue to pass through untouched. -/
theorem Record.toChecked_compute [DecidableEq Key]
    (key : Key) (calculateTarget : Record Key Value → Value key)
    (calculateSource : CheckedRecord Key Value Error → Value key)
    (self inherited : Record Key Value)
    (sourceSelf sourceInherited : CheckedRecord Key Value Error)
    (missing : Key → Error)
    (selfCalculation : calculateTarget self = calculateSource sourceSelf)
    (inheritedExact : inherited.toChecked missing = sourceInherited) :
    ((Record.compute key calculateTarget) self inherited).toChecked missing =
      CheckedRecord.compute key calculateSource sourceSelf sourceInherited := by
  change ((Record.slot key (calculateTarget self)) self inherited).toChecked missing =
    CheckedRecord.slot key (calculateSource sourceSelf) sourceInherited
  simpa only [selfCalculation, inheritedExact] using
    (Record.toChecked_slot key (calculateTarget self) self inherited missing)

end LeanPoo.Prototype
