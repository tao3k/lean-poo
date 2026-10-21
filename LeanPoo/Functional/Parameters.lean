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


/-- A bound parameter retains descriptor identity and its direct source revision.
Transitive Type/callback semantics remain separate stability premises. -/
structure BoundParameter (Name Descriptor : Type) where
  name : Name
  descriptor : Descriptor
  revision : Nat

/-- The finite source check used before residual inference and after elaboration. -/
def bindingsCurrent [DecidableEq Descriptor] (bindings : List (BoundParameter Name Descriptor))
    (fields : Name → Option Descriptor) (revision : Descriptor → Nat) : Bool :=
  bindings.all fun binding => decide
    (fields binding.name = some binding.descriptor ∧ revision binding.descriptor = binding.revision)

/-- Every accepted bound name keeps both its descriptor and direct revision. -/
theorem bindingsCurrent_sound [DecidableEq Descriptor] (bindings : List (BoundParameter Name Descriptor))
    (fields : Name → Option Descriptor) (revision : Descriptor → Nat)
    (accepted : bindingsCurrent bindings fields revision = true)
    (binding : BoundParameter Name Descriptor) (member : binding ∈ bindings) :
    fields binding.name = some binding.descriptor ∧ revision binding.descriptor = binding.revision := by
  exact of_decide_eq_true ((List.all_eq_true.mp accepted) binding member)

/-- Either an overridden field or an in-place revision change rejects the snapshot. -/
theorem bindingsCurrent_refuses [DecidableEq Descriptor] (bindings : List (BoundParameter Name Descriptor))
    (fields : Name → Option Descriptor) (revision : Descriptor → Nat)
    (binding : BoundParameter Name Descriptor) (member : binding ∈ bindings)
    (changed : fields binding.name ≠ some binding.descriptor ∨ revision binding.descriptor ≠ binding.revision) :
    bindingsCurrent bindings fields revision = false := by
  cases current : bindingsCurrent bindings fields revision with
  | false => rfl
  | true =>
    have same := bindingsCurrent_sound bindings fields revision current binding member
    rcases changed with different | different
    · exact False.elim (different same.1)
    · exact False.elim (different same.2)

/-- A type schema checks the names read by the actual positional binder, then
uses that SAME snapshot. Hosts supply faithful capture and pure admission;
no arbitrary concurrent mutation or descriptor-compiler correctness is asserted. -/
def specializeExpected [DecidableEq Name] (reserved : Name) (expected : List Name)
    (source : Template Name Value) (values : List Value) : Except Failure (Template Name Value) :=
  if source.remaining = expected then checkedSpecialize reserved source values else .error .declaration

/-- A reordered, added or removed name refuses even when the new arity fits. -/
theorem specializeExpected_changed [DecidableEq Name] (reserved : Name) (expected : List Name)
    (source : Template Name Value) (values : List Value) (changed : source.remaining ≠ expected) :
    specializeExpected reserved expected source values = .error .declaration := by
  simp [specializeExpected, changed]

/-- Unchanged metadata reuses the existing checked positional protocol exactly. -/
theorem specializeExpected_same [DecidableEq Name] (reserved : Name)
    (source : Template Name Value) (values : List Value) :
    specializeExpected reserved source.remaining source values = checkedSpecialize reserved source values := by
  simp [specializeExpected]

/-- Success binds values under the original schema order and leaves its exact
suffix; all unbound fields retain the existing persistent interpretation. -/
theorem specializeExpected_sound [DecidableEq Name] (reserved : Name) (expected : List Name)
    (source result : Template Name Value) (values : List Value)
    (accepted : specializeExpected reserved expected source values = .ok result) :
    source.remaining = expected ∧ validNames reserved expected = true ∧
      result.remaining = expected.drop values.length ∧
      result.fields = bindPrefix expected values source.fields := by
  unfold specializeExpected at accepted
  split at accepted
  · rename_i same
    unfold checkedSpecialize at accepted
    split at accepted
    · rename_i valid
      unfold specialize at accepted
      split at accepted
      · have exactResult := Except.ok.inj accepted
        cases exactResult
        exact ⟨same, same ▸ valid, by simp [same], by simp [same]⟩
      · contradiction
    · contradiction
  · contradiction

/-- A changed order cannot weaken ordinary excessive-argument refusal. -/
theorem specializeExpected_excess [DecidableEq Name] (reserved : Name)
    (source : Template Name Value) (values : List Value)
    (valid : validNames reserved source.remaining = true)
    (excess : source.remaining.length < values.length) :
    specializeExpected reserved source.remaining source values = .error .excess := by
  simp [specializeExpected, checkedSpecialize, valid, specialize_excess source values excess]

/-- Checked prefixes compose under the original order and its exact residual
suffix; this reuses the existing incremental law rather than a second binder. -/
theorem specializeExpected_append [DecidableEq Name] (reserved : Name)
    (source : Template Name Value) (first second : List Value)
    (valid : validNames reserved source.remaining = true)
    (fits : first.length + second.length ≤ source.remaining.length) :
    (specializeExpected reserved source.remaining source first).bind
      (fun derived => specializeExpected reserved (source.remaining.drop first.length) derived second) =
        specializeExpected reserved source.remaining source (first ++ second) := by
  have one : first.length ≤ source.remaining.length := by omega
  have two : second.length ≤ source.remaining.length - first.length := by omega
  have rest := valid_drop reserved source.remaining first.length valid
  simp [specializeExpected, checkedSpecialize, valid, specialize, one, two, rest,
    Except.bind, List.length_append, fits, List.drop_drop, bind_append]

/-- Failed source inspection retains its cause before any order/arity check. -/
theorem specializeExpected_error [DecidableEq Name] (inspect : Except Cause (Template Name Value))
    (reserved : Name) (expected : List Name) (values : List Value) (cause : Cause)
    (failed : inspect = .error cause) :
    ((inspect.mapError Sum.inr).bind fun source =>
      (specializeExpected reserved expected source values).mapError Sum.inl) = .error (Sum.inr cause) := by
  simp [failed, Except.mapError, Except.bind]

/-- Compose retained descriptor admission with the EXISTING checked name binder.
The source/fields/revisions are faithful post-getter observations; hosts must
also enforce the final revision fence after construction and disjoint bound names. -/
def specializeCurrent [DecidableEq Name] [DecidableEq Descriptor] (reserved : Name)
    (expected : List Name) (bound : List (BoundParameter Name Descriptor))
    (source : Template Name Descriptor) (revision : Descriptor → Nat) (values : List Descriptor) :
    Except Failure (Template Name Descriptor) :=
  if bindingsCurrent bound source.fields revision then specializeExpected reserved expected source values
  else .error .declaration

/-- Changed retained identity/revision refuses despite unchanged remaining names. -/
theorem specializeCurrent_stale [DecidableEq Name] [DecidableEq Descriptor] (reserved : Name)
    (expected : List Name) (bound : List (BoundParameter Name Descriptor))
    (source : Template Name Descriptor) revision (values : List Descriptor)
    (stale : bindingsCurrent bound source.fields revision = false) :
    specializeCurrent reserved expected bound source revision values = .error .declaration := by
  simp [specializeCurrent, stale]

/-- Stable retained bindings reuse exactly the existing checked positional gate. -/
theorem specializeCurrent_fresh [DecidableEq Name] [DecidableEq Descriptor] (reserved : Name)
    (expected : List Name) (bound : List (BoundParameter Name Descriptor))
    (source : Template Name Descriptor) revision (values : List Descriptor)
    (current : bindingsCurrent bound source.fields revision = true) :
    specializeCurrent reserved expected bound source revision values =
      specializeExpected reserved expected source values := by simp [specializeCurrent, current]

/-- Retained admission cannot hide a change to the remaining parameter order. -/
theorem specializeCurrent_changed [DecidableEq Name] [DecidableEq Descriptor] (reserved : Name)
    (expected : List Name) (bound : List (BoundParameter Name Descriptor))
    (source : Template Name Descriptor) revision (values : List Descriptor)
    (changed : source.remaining ≠ expected) :
    specializeCurrent reserved expected bound source revision values = .error .declaration := by
  cases stable : bindingsCurrent bound source.fields revision <;>
    simp [specializeCurrent, stable, specializeExpected, changed]

/-- A successful receiver has the exact new fields/suffix AND every original
retained descriptor/revision. Disjointness is supplied by the host's existing
binding grammar, so the new prefix cannot overwrite an earlier Type parameter. -/
theorem specializeCurrent_sound [DecidableEq Name] [DecidableEq Descriptor] (reserved : Name)
    (expected : List Name) (bound : List (BoundParameter Name Descriptor))
    (source result : Template Name Descriptor) revision (values : List Descriptor)
    (disjoint : ∀ binding ∈ bound, binding.name ∉ expected)
    (accepted : specializeCurrent reserved expected bound source revision values = .ok result) :
    source.remaining = expected ∧ result.remaining = expected.drop values.length ∧
      result.fields = bindPrefix expected values source.fields ∧
      ∀ binding ∈ bound, result.fields binding.name = some binding.descriptor ∧
        revision binding.descriptor = binding.revision := by
  unfold specializeCurrent at accepted
  split at accepted
  · rename_i current
    obtain ⟨order, _, suffix, fields⟩ := specializeExpected_sound reserved expected source result values accepted
    refine ⟨order, suffix, fields, ?_⟩
    intro binding member
    have stable := bindingsCurrent_sound bound source.fields revision current binding member
    have outside : binding.name ∉ expected.take values.length :=
      fun present => disjoint binding member (List.mem_of_mem_take present)
    exact ⟨by rw [fields, bind_frame expected values source.fields binding.name outside]; exact stable.1, stable.2⟩
  · contradiction

/-- Original getter errors precede all successful binding/name admission. -/
theorem specializeCurrent_error [DecidableEq Name] [DecidableEq Descriptor]
    (inspect : Except Cause (Template Name Descriptor)) (reserved : Name) (expected : List Name)
    (bound : List (BoundParameter Name Descriptor)) revision (values : List Descriptor)
    (cause : Cause) (failed : inspect = .error cause) :
    ((inspect.mapError Sum.inr).bind fun source =>
      (specializeCurrent reserved expected bound source revision values).mapError Sum.inl) = .error (Sum.inr cause) := by
  simp [failed, Except.mapError, Except.bind]

end LeanPoo.Functional.Parameters
