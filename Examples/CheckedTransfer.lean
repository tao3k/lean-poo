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

end LeanPoo.Examples.CheckedTransfer
