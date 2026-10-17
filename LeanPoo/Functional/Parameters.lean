import LeanPoo.Prototype.SlotSpec

/-! Positional specialization and lexical construction options lower to the
existing slot model. These are pure source-level laws, not proofs of the Gerbil
macro expander, effects or cache implementation. Metadata must be immutable in use. -/
namespace LeanPoo.Functional.Parameters

/-- A receiver's remaining positional names and current field interpretation. -/
structure Template (Name Value : Type) where
  remaining : List Name
  fields : Name → Option Value

/-- Distinguish malformed declarations from excessive positional arguments. -/
inductive Failure where | declaration | excess
  deriving BEq, DecidableEq, Repr

/-- Persistent prefix writes; no previous receiver is mutated or inherited as self. -/
def bindPrefix [DecidableEq Name] (names : List Name) (values : List Value)
    (fields : Name → Option Value) : Name → Option Value :=
  match names,values with
  | name :: rest,value :: tail => bindPrefix rest tail (fun key => if key = name then some value else fields key)
  | _,_ => fields

/-- Arity checks precede construction. Formula evaluation remains a later consumer. -/
def specialize [DecidableEq Name] (source : Template Name Value) (values : List Value) :
    Except Failure (Template Name Value) :=
  if values.length ≤ source.remaining.length then
    .ok ⟨source.remaining.drop values.length,bindPrefix source.remaining values source.fields⟩
  else .error .excess

/-- The reserved metadata name cannot itself be a positional parameter. -/
def validNames [DecidableEq Name] (reserved : Name) (names : List Name) : Bool :=
  decide (names.Nodup ∧ reserved ∉ names)

/-- Validate declaration metadata before even an empty specialization. -/
def checkedSpecialize [DecidableEq Name] (reserved : Name) (source : Template Name Value) (values : List Value) :=
  if validNames reserved source.remaining then specialize source values else .error .declaration

/-- Zero positional arguments preserve the exact receiver interpretation. -/
theorem specialize_zero [DecidableEq Name] (source : Template Name Value) : specialize source [] = .ok source := by
  cases source
  simp [specialize,bindPrefix]

/-- Excess arguments return no partially bound receiver. -/
theorem specialize_excess [DecidableEq Name] (source : Template Name Value) (values : List Value)
    (excess : source.remaining.length < values.length) : specialize source values = .error .excess := by
  simp [specialize,Nat.not_le.mpr excess]

/-- A successful prefix leaves precisely the unbound suffix in positional order. -/
theorem specialize_remaining [DecidableEq Name] (source : Template Name Value) (values : List Value)
    (fits : values.length ≤ source.remaining.length) :
    (specialize source values).map Template.remaining = .ok (source.remaining.drop values.length) := by
  simp [specialize,fits,Except.map]

/-- Binding two prefixes is the same persistent update as binding their concatenation. -/
theorem bind_append [DecidableEq Name] (names : List Name) (first second : List Value) (fields : Name → Option Value) :
    bindPrefix names (first ++ second) fields =
      bindPrefix (names.drop first.length) second (bindPrefix names first fields) := by
  induction names generalizing first fields with
  | nil => simp [bindPrefix]
  | cons name rest ih =>
    cases first with
    | nil => simp [bindPrefix]
    | cons value tail => simpa [bindPrefix] using ih tail (fun key => if key = name then some value else fields key)

/-- Partial and complete specialization compose without changing final-self fields. -/
theorem specialize_append [DecidableEq Name] (source : Template Name Value) (first second : List Value)
    (fits : first.length + second.length ≤ source.remaining.length) :
    (specialize source first).bind (fun derived => specialize derived second) = specialize source (first ++ second) := by
  have one : first.length ≤ source.remaining.length := by omega
  have two : second.length ≤ source.remaining.length-first.length := by omega
  simp [specialize,one,two,List.length_append,fits,Except.bind,List.drop_drop,bind_append]

/-- Fields outside the bound prefix retain the original value, including absence. -/
theorem bind_frame [DecidableEq Name] (names : List Name) (values : List Value) (fields : Name → Option Value)
    (key : Name) (outside : key ∉ names.take values.length) : bindPrefix names values fields key = fields key := by
  induction names generalizing values fields with
  | nil => rfl
  | cons name rest ih =>
    cases values with
    | nil => rfl
    | cons value tail =>
      simp only [List.length_cons,List.take_succ_cons,List.mem_cons,not_or] at outside
      simpa [bindPrefix,outside.1] using ih tail (fun other => if other = name then some value else fields other) outside.2

/-- Invalid names fail before arity/binding, and return no receiver. -/
theorem invalid_declaration [DecidableEq Name] (reserved : Name) (source : Template Name Value) (values : List Value)
    (invalid : validNames reserved source.remaining = false) : checkedSpecialize reserved source values = .error .declaration := by
  simp [checkedSpecialize,invalid]

/-- Prefix binding leaves another valid, unique declaration for later specialization. -/
theorem valid_drop [DecidableEq Name] (reserved : Name) (names : List Name) (count : Nat)
    (valid : validNames reserved names = true) : validNames reserved (names.drop count) = true := by
  have admitted := of_decide_eq_true valid
  apply decide_eq_true
  exact ⟨(List.drop_sublist count names).nodup admitted.1,
    fun member => admitted.2 (List.mem_of_mem_drop member)⟩

/-- Checked specialization has the same incremental law, including repeated
metadata admission at the partial receiver boundary. -/
theorem checked_append [DecidableEq Name] (reserved : Name) (source : Template Name Value)
    (first second : List Value) (valid : validNames reserved source.remaining = true)
    (fits : first.length + second.length ≤ source.remaining.length) :
    (checkedSpecialize reserved source first).bind (fun derived => checkedSpecialize reserved derived second) =
      checkedSpecialize reserved source (first ++ second) := by
  have one : first.length ≤ source.remaining.length := by omega
  have two : second.length ≤ source.remaining.length-first.length := by omega
  have rest := valid_drop reserved source.remaining first.length valid
  simp [checkedSpecialize,valid,specialize,one,two,rest,List.length_append,fits,
    Except.bind,List.drop_drop,bind_append]

/-- Explicit lexical imports remain selected independently of local-slot inclusion. -/
def bindings [DecidableEq Name] (explicit declared : List Name) (includeLocal : Bool) :=
  (explicit ++ if includeLocal then declared else []).eraseDups

/-- Lexical scope policy has exact membership and introduces no other names. -/
theorem bindings_membership [DecidableEq Name] (explicit declared : List Name) (includeLocal : Bool) (name : Name) :
    name ∈ bindings explicit declared includeLocal ↔ name ∈ explicit ∨ (includeLocal = true ∧ name ∈ declared) := by
  cases includeLocal <;> simp [bindings]

/-- Global/per-slot inherited aliases lower to the same existing delayed slot body. -/
theorem inherited_alias (body : Self → LeanPoo.Prototype.Next Value → Value)
    (self : Self) (inherited : LeanPoo.Prototype.Next Value) :
    (LeanPoo.Prototype.SlotSpec.computed (fun receiver prior => body receiver prior)).eval self inherited = body self inherited := rfl

/-- Canonical optional arguments use the supplied value, including an explicit false. -/
def optional (supplied : Option Value) (default : Unit → Value) : Value :=
  match supplied with | some value => value | none => default ()

/-- Explicit arguments do not demand their default computation. -/
theorem optional_supplied (value : Value) (default : Unit → Value) : optional (some value) default = value := rfl

/-- Absent arguments use exactly their declaration's default result. -/
theorem optional_absent (default : Unit → Value) : optional none default = default () := rfl

/-- Stable first-occurrence selection over exact keys. For syntax, keys stand for
lexical binding identities, not printed names; the host comparator must agree. -/
def uniqueBindings [DecidableEq Key] (key : Entry → Key) (seen : List Key) : List Entry → List Entry
  | [] => []
  | entry :: rest =>
    if key entry ∈ seen then uniqueBindings key seen rest
    else entry :: uniqueBindings key (key entry :: seen) rest

/-- An unseen first representative is retained unchanged, including its payload. -/
theorem uniqueBindings_first [DecidableEq Key] (key : Entry → Key) (seen : List Key)
    (entry : Entry) (rest : List Entry) (fresh : key entry ∉ seen) :
    uniqueBindings key seen (entry :: rest) = entry :: uniqueBindings key (key entry :: seen) rest := by
  simp [uniqueBindings, fresh]

/-- A previously selected key never gets another representative. -/
theorem uniqueBindings_skip [DecidableEq Key] (key : Entry → Key) (seen : List Key)
    (entry : Entry) (rest : List Entry) (present : key entry ∈ seen) :
    uniqueBindings key seen (entry :: rest) = uniqueBindings key seen rest := by
  simp [uniqueBindings, present]

/-- Deduplication preserves first-key lookup. Already selected keys are absent,
so a filtered private override cannot reveal a later public representative. -/
theorem find_uniqueBindings [DecidableEq Key] (key : Entry → Key) (seen : List Key)
    (entries : List Entry) (name : Key) :
    (uniqueBindings key seen entries).find? (fun entry => decide (key entry = name)) =
      if name ∈ seen then none else entries.find? (fun entry => decide (key entry = name)) := by
  induction entries generalizing seen with
  | nil => simp [uniqueBindings]
  | cons entry rest ih =>
    by_cases present : key entry ∈ seen
    · simp only [uniqueBindings, present, ite_true]
      rw [ih]
      by_cases selected : name ∈ seen
      · simp [selected]
      · have different : key entry ≠ name := by intro same; apply selected; simpa [← same] using present
        simp [selected, different]
    · simp only [uniqueBindings, present, ite_false, List.find?_cons]
      by_cases same : key entry = name
      · subst name; simp [present]
      · rw [ih]
        simp [same, Ne.symm same]

/-- With a fresh set, current lookup is exactly the first original declaration. -/
theorem find_freshBindings [DecidableEq Key] (key : Entry → Key) (entries : List Entry) (name : Key) :
    (uniqueBindings key [] entries).find? (fun entry => decide (key entry = name)) =
      entries.find? (fun entry => decide (key entry = name)) := by
  simpa using find_uniqueBindings key [] entries name

/-- Ancestor-first slot inventory is a distinct order from most-specific metadata.
Each ancestor's local order is retained while repeated symbolic keys disappear. -/
def inheritedNames [DecidableEq Key] (groups : List (List Key)) : List Key :=
  uniqueBindings id [] groups.reverse.flatten

/-- Empty inheritance has no invented field names. -/
theorem inheritedNames_empty [DecidableEq Key] : inheritedNames (Key := Key) [] = [] := rfl

end LeanPoo.Functional.Parameters
