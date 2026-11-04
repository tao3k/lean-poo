import LeanPoo.Functional.WrapperValidation
import LeanPoo.Functional.ByteIO
import LeanPoo.Prototype.ValueStorage

/-! Alignment fixtures for standard byte endpoints and FUN checked carriers.
No parser, host pointer equality, transport rollback or OS cleanup is proved. -/
namespace LeanPoo.Examples.CheckedTransfer
open Functional

/-- Explicit stream state makes already consumed/written prefixes observable. -/
structure Streams where
  input : List UInt8
  output : List UInt8
  deriving DecidableEq, Repr

/-- A finite Reader extracts one span; exact-demand refusal is the shared boundary. -/
def pull (count : Nat) (state : Streams) : Except Bool (List UInt8) × Streams :=
  (.ok (state.input.take count), { state with input := state.input.drop count })

/-- A failing Writer can leave a real prefix; success appends the complete bytes. -/
def push (fail : Bool) (bytes : List UInt8) (state : Streams) : Except Bool Unit × Streams :=
  if fail then (.error false, { state with output := state.output ++ bytes.take 1 })
  else (.ok (), { state with output := state.output ++ bytes })

/-- The reusable action receives a new stream state on every invocation. -/
def copy (count : Nat) (fail : Bool) (state : Streams) : Except Bool (List UInt8) × Streams :=
  ByteIO.transfer (ByteIO.exact (pull count) true count) (push fail) state

-- A short exact read consumes its prefix but never calls the output step.
example : copy 2 false ⟨[7], [99]⟩ = (.error true, ⟨[], [99]⟩) := by rfl
-- Output failure preserves the opaque false cause, consumption and partial output.
example : copy 2 true ⟨[8, 9], [99]⟩ = (.error false, ⟨[], [99, 8]⟩) := by rfl
-- Retrying with fresh endpoints delivers fresh bytes, not a retained failed buffer.
example : copy 2 false ⟨[3, 4], []⟩ = (.ok [3, 4], ⟨[], [3, 4]⟩) := by rfl
-- The span admission gate cannot invoke the Reader for an out-of-bounds request.
example : ByteIO.readSpan (fun count _ => pull count) false 3 4 0 0 ⟨[1], []⟩ =
    (.error false, ⟨[1], []⟩) := by rfl
-- Empty spans perform no transport and keep the original state.
example : ByteIO.readSpan (fun count _ => pull count) false 3 3 0 0 ⟨[1], []⟩ =
    (.ok [], ⟨[1], []⟩) := by rfl

/-- The finite Function descriptor admits nonnegative inputs and outputs. -/
def nonnegative (value : Int) : Except String Int :=
  if value ≥ 0 then .ok value else .error "nonnegative"

/-- Wrapping changes behavior without ever evaluating the source during admission. -/
def boxed (source : Option (Int → Except String Int)) : Except String (Option (Int → Except String Int)) :=
  WrapperValidation.validate Option.isSome
    (fun value => value.getD (fun _ => .error "absent"))
    (fun raw => .ok (FunctionValidation.wrap nonnegative nonnegative raw))
    (fun _ checked => some checked) "outer carrier" source

/-- Observe the admitted function without discarding its input/output checks. -/
def invoke (source : Option (Int → Except String Int)) (argument : Int) : Except String Int :=
  (boxed source).bind fun value =>
    match value with
    | none => .error "absent"
    | some checked => checked argument

example : invoke (some (fun value => .ok (value + 1))) 7 = .ok 8 := by rfl
example : invoke (some (fun value => .ok value)) (-1) = .error "nonnegative" := by rfl
example : invoke (some (fun _ => .ok (-1))) 7 = .error "nonnegative" := by rfl
example : invoke none 7 = .error "outer carrier" := by rfl
-- False is a present payload; it is never confused with absence or validation failure.
example : WrapperValidation.validate Option.isSome (fun value => value.getD true)
    (fun value => Except.ok (ε := String) value) (fun _ value => some value)
    "outer carrier" (some false) = .ok (some false) := by rfl

/-- Runtime strings and keywords are data, not symbolic Slot identities. -/
inductive RuntimeName where
  | symbol : String → RuntimeName
  | text : String → RuntimeName
  | keyword : String → RuntimeName
  | number : Int → RuntimeName

/-- The host interpretation follows the standard symbol-only Slot contract. -/
def admitName : RuntimeName → Except String String
  | .symbol name => .ok name
  | _ => .error "symbol required"

/-- A warmed receiver keeps its one authoritative false cell at ordinal zero. -/
def warmed : Prototype.Representation.View Bool :=
  ⟨1, 4, 9, ["disabled"], fun name => if name = "disabled" then some false else none⟩

/-- Ordinary named access invokes its original fallback only for admitted names. -/
def namedRead (name : String) (view : Prototype.Representation.View Bool) :
    Except String Bool × Prototype.Representation.View Bool :=
  (Prototype.Representation.primaryRead view name (fun _ => .error "missing"), view)

-- Refusal cannot retire a warmed receiver or forge a successful default.
example : Prototype.Representation.withAdmittedName admitName namedRead
    (.number 17) warmed = (.error "symbol required", warmed) := rfl
example : Prototype.Representation.withAdmittedName admitName namedRead
    (.text "disabled") warmed = (.error "symbol required", warmed) := rfl
example : Prototype.Representation.withAdmittedName admitName namedRead
    (.keyword "disabled") warmed = (.error "symbol required", warmed) := rfl
-- Reusing the operation with a valid runtime symbol retains false at offset zero.
example : Prototype.Representation.withAdmittedName admitName namedRead
    (.symbol "disabled") warmed = (.ok false, warmed) := rfl
example : Prototype.Representation.withAdmittedName admitName namedRead
    (.symbol "unknown") warmed = (.error "missing", warmed) := rfl

/-- Callback handles and false-valued fields remain distinct opaque payloads. -/
abbrev SeedPayload := (Nat → Nat) ⊕ Bool

/-- The original finite names and explicit values belong to this invocation. -/
def originalSeedRequest (callback : Nat → Nat) : Prototype.Representation.SeedRequest SeedPayload :=
  ⟨["declared"], [("callback", .inl callback), ("disabled", .inr false)]⟩

/-- A source callback can replace the entire external request without changing
what the current constructor already captured. This is not effect rollback. -/
def rewrittenSeedRequest : Prototype.Representation.SeedRequest SeedPayload :=
  ⟨["late-name"], [("late-callback", .inl (fun _ => 0))]⟩

/-- Discovery and seeding both retain their external effects. The second stage
may refuse with false; a fresh invocation supplies its own Function handle. -/
def seedHandoff (callback : Nat → Nat) (refuse : Bool) :
    Except Bool (List String × List (String × SeedPayload)) ×
      (Nat × Prototype.Representation.SeedRequest SeedPayload) :=
  Prototype.Representation.prepareSeedRequest (originalSeedRequest callback)
    (0, originalSeedRequest callback)
    (fun _ => (.ok ["seed"], (1, rewrittenSeedRequest)))
    (fun names => .ok (names, []))
    (fun _ => ((if refuse then .error false else .ok [("seed", .inr false)]),
      (2, rewrittenSeedRequest)))
    (fun store rows => .ok (store.1, rows))

/-- Neither discovery nor seed effects may install their rewritten field layout. -/
example (callback : Nat → Nat) : (seedHandoff callback false).1 =
    .ok (["declared", "seed", "callback", "disabled"],
      [("seed", .inr false), ("callback", .inl callback), ("disabled", .inr false)]) := rfl

/-- The externally rewritten request and both observed source stages remain visible. -/
example (callback : Nat → Nat) : (seedHandoff callback false).2 =
    (2, rewrittenSeedRequest) := rfl

/-- Exact false refusal is retained alongside already performed source effects. -/
example (callback : Nat → Nat) : seedHandoff callback true =
    (.error false, (2, rewrittenSeedRequest)) := rfl

/-- A failed candidate cannot replace an existing authoritative value store. -/
example (callback : Nat → Nat) (current : List (Option SeedPayload)) :
    Prototype.Representation.publishSeed current
      ((seedHandoff callback true).1.map (fun store => store.2.map (some ∘ Prod.snd))) = current := rfl

/-- Retrying with a fresh invocation preserves the replacement Function itself;
no function equality instance, stale seed or cached refusal is used. -/
example (replacement : Nat → Nat) : (seedHandoff replacement false).1 =
    .ok (["declared", "seed", "callback", "disabled"],
      [("seed", .inr false), ("callback", .inl replacement), ("disabled", .inr false)]) := rfl

/-- Finite query effects distinguish preparation/visibility from delivery. The
name inventory is structural: a false-valued field is still present. -/
structure QueryState where
  names : List String
  prepared : Nat
  visibility : Nat
  delivered : Nat
  deriving DecidableEq, Repr

/-- Presence uses declaration membership, not the truth of a cached payload. -/
def presenceQuery (name : String) (state : QueryState) : Except String Bool × QueryState :=
  (.ok (state.names.contains name),
    {state with prepared := state.prepared + 1, delivered := state.delivered + 1})

/-- Declared reflection may prepare visibility before a valid missing-name
refusal. Malformed names must never reach this supplied interpretation. -/
def reflectedQuery (name : String) (state : QueryState) : Except String Bool × QueryState :=
  let prepared := {state with prepared := state.prepared + 1, visibility := state.visibility + 1}
  if name = "disabled" then (.ok false, {prepared with delivered := prepared.delivered + 1})
  else (.error "hidden or undeclared", prepared)

/-- A warmed finite directory carries explicit receiver and query effects. -/
def warmQueries : QueryState := ⟨["disabled"], 2, 1, 3⟩

-- Both protocols reject malformed runtime names without any new query effect.
example : Prototype.Representation.withAdmittedName admitName presenceQuery
    (.number 17) warmQueries = (.error "symbol required", warmQueries) := rfl
example : Prototype.Representation.withAdmittedName admitName reflectedQuery
    (.text "disabled") warmQueries = (.error "symbol required", warmQueries) := rfl
example : Prototype.Representation.withAdmittedName admitName reflectedQuery
    (.keyword "disabled") warmQueries = (.error "symbol required", warmQueries) := rfl
-- Presence of false and successful delivery of false remain distinct results.
example : Prototype.Representation.withAdmittedName admitName presenceQuery
    (.symbol "disabled") warmQueries = (.ok true, ⟨["disabled"], 3, 1, 4⟩) := rfl
example : Prototype.Representation.withAdmittedName admitName reflectedQuery
    (.symbol "disabled") warmQueries = (.ok false, ⟨["disabled"], 3, 2, 4⟩) := by
  simp [Prototype.Representation.withAdmittedName, admitName, reflectedQuery, warmQueries]
-- A valid absent symbol is false for presence, but an error for public reflection.
example : Prototype.Representation.withAdmittedName admitName presenceQuery
    (.symbol "missing") warmQueries = (.ok false, ⟨["disabled"], 3, 1, 4⟩) := rfl
example : Prototype.Representation.withAdmittedName admitName reflectedQuery
    (.symbol "missing") warmQueries = (.error "hidden or undeclared", ⟨["disabled"], 3, 2, 3⟩) := by
  simp [Prototype.Representation.withAdmittedName, admitName, reflectedQuery, warmQueries]

#print axioms Prototype.Representation.withAdmittedName_failure
#print axioms Prototype.Representation.withAdmittedName_false
#print axioms Prototype.Representation.withAdmittedName_refused_preparation

/-- Growth inserts a true cell at zero and moves the original false cell to one. -/
example :
    let current : Prototype.Representation.View Bool :=
      ⟨1, 4, 9, ["added", "disabled"], fun name => some (name == "added")⟩
    let old : Prototype.Representation.Site := ⟨1, 4, 9, ["disabled"], "disabled", 0, rfl⟩
    let rebound := Prototype.Representation.currentValueSite current "disabled" 1 rfl
    Prototype.Representation.readBoundOffset old current "stale" = .error "stale" ∧
      Prototype.Representation.readBoundOffset rebound current "stale" = .ok (some false) := by
  simp [Prototype.Representation.readBoundOffset, Prototype.Representation.currentValueSite,
    Prototype.Representation.cell]

/-- An in-bounds sibling proposal after growth leaves the old guard intact and
stale. Retrying the named offset reads false from the current layout. -/
example :
    let current : Prototype.Representation.View Bool :=
      ⟨1, 4, 9, ["added", "disabled"], fun name => some (name == "added")⟩
    let old : Prototype.Representation.Site := ⟨1, 4, 9, ["disabled"], "disabled", 0, rfl⟩
    let refused := Prototype.Representation.bindValueOffset (some old) current "disabled" (some 0) "invalid"
    refused = (some old, .error "invalid") ∧
      refused.1.map (fun site => Prototype.Representation.readBoundOffset site current "stale") =
        some (.error "stale") ∧
      (Prototype.Representation.bindValueOffset refused.1 current "disabled" (some 1) "invalid").1.map
        (fun site => Prototype.Representation.readBoundOffset site current "stale") = some (.ok (some false)) := by
  simp [Prototype.Representation.bindValueOffset, Prototype.Representation.currentValueSite,
    Prototype.Representation.readBoundOffset, Prototype.Representation.cell]

#print axioms Prototype.Representation.bindValueOffset_refused
#print axioms Prototype.Representation.bindValueOffset_read

end LeanPoo.Examples.CheckedTransfer
