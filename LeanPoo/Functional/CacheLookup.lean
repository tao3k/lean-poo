import LeanPoo.Functional.Validation

/-! Standard lazy table lookup laws for source-bound construction caches. -/
namespace LeanPoo.Functional.ConstructionCache

/-- A table lookup distinguishes missing keys from present values, including false
or an already materialized absence. The fallback is supplied as a thunk. -/
def lookupOr {Item Fault : Type} (entry : Option Item) (fallback : Unit → Except Fault Item) :
    Except Fault Item :=
  match entry with
  | some value => .ok value
  | none => fallback ()

/-- A cached hit returns the exact stored value independently of the fallback. -/
theorem lookupOr_present {Item Fault : Type} (value : Item) (fallback : Unit → Except Fault Item) :
    lookupOr (some value) fallback = .ok value := rfl

/-- The missing path invokes the supplied fallback without changing its error. -/
theorem lookupOr_missing {Item Fault : Type} (fallback : Unit → Except Fault Item) :
    lookupOr none fallback = fallback () := rfl

/-- Materialized absence is an entry, not an instruction to consult another source. -/
theorem lookupOr_stored_absence {Item Fault : Type}
    (fallback : Unit → Except Fault (Option Item)) :
    lookupOr (some none) fallback = .ok none := rfl

/-- Model standard ensure-ref's commit-after-success rule. The hash/interface
premise supplies a lookup whose equality agrees with the chosen key semantics. -/
def ensureLookup {Name Item Fault : Type} [DecidableEq Name]
    (entries : Name → Option Item) (key : Name) (build : Unit → Except Fault Item) :
    Except Fault Item × (Name → Option Item) :=
  match entries key with
  | some value => (.ok value, entries)
  | none => match build () with
    | .error error => (.error error, entries)
    | .ok value => (.ok value, fun other => if other = key then some value else entries other)

/-- Existing entries preserve the complete table and do not depend on construction. -/
theorem ensureLookup_hit {Name Item Fault : Type} [DecidableEq Name]
    (entries : Name → Option Item) (key : Name) (value : Item) (build : Unit → Except Fault Item)
    (present : entries key = some value) :
    ensureLookup entries key build = (.ok value, entries) := by
  simp [ensureLookup, present]

/-- Failed construction preserves every old entry, enabling a clean retry. -/
theorem ensureLookup_error {Name Item Fault : Type} [DecidableEq Name]
    (entries : Name → Option Item) (key : Name) (error : Fault) (build : Unit → Except Fault Item)
    (missing : entries key = none) (failed : build () = .error error) :
    ensureLookup entries key build = (.error error, entries) := by
  simp [ensureLookup, missing, failed]

/-- Successful construction affects only the requested key. -/
theorem ensureLookup_frame {Name Item Fault : Type} [DecidableEq Name]
    (entries : Name → Option Item) (key other : Name) (value : Item) (build : Unit → Except Fault Item)
    (missing : entries key = none) (built : build () = .ok value) (different : other ≠ key) :
    (ensureLookup entries key build).2 other = entries other := by
  simp [ensureLookup, missing, built, different]

/-- After successful insertion, another ensure returns that same value with no
new construction; this is distinct from approval or semantic-cache eligibility. -/
theorem ensureLookup_repeat {Name Item Fault : Type} [DecidableEq Name]
    (entries : Name → Option Item) (key : Name) (value : Item)
    (build again : Unit → Except Fault Item) (missing : entries key = none)
    (built : build () = .ok value) :
    ensureLookup (ensureLookup entries key build).2 key again =
      (.ok value, (ensureLookup entries key build).2) := by
  apply ensureLookup_hit
  simp [ensureLookup, missing, built]

end LeanPoo.Functional.ConstructionCache
