import LeanPoo.Functional.Codec
import LeanPoo.Functional.ContextPullback
import LeanPoo.Functional.StatefulValidation

/-! Validate a request before touching cached dependencies. A decoded request
runs against its exact base snapshot; later refusals retain that read's state. -/
namespace LeanPoo.Functional
universe u v w x y z q r

structure RequestResult (State : Type u) (Output : Type v) (Error : Type w) where
  outcome : Except Error Output
  next : State
  /-- None means execution was refused before attempting a cache read. -/
  reused : Option Bool

def RequestResult.transition (result : RequestResult State Output Error) : Except Error Output × State :=
  (result.outcome, result.next)

namespace Requirements
variable {Context : Type u} {Key : Type v} {Value : Context → Key → Type w}
variable {keys : List Key} {Claim : ∀ c, Results Value c keys → Prop} {ready : Certified keys Claim}
variable {Input : Type x} {Wire : Type y} {Error : Type z} {Output : Type q}
variable [DecidableEq Context]

def ContextSlot.call (slot : ContextSlot ready) (codec : Codec Input Wire Error)
    (project : Input → Context)
    (run : ∀ input, Snapshot ready (project input) → Except Error Output) (wire : Wire) :
    RequestResult (ContextSlot ready) Output Error :=
  match codec.decode wire with
  | .error error => ⟨.error error, slot, none⟩
  | .ok input =>
    let (data, next, reused) := slot.readAlong project input
    ⟨run input data, next, some reused⟩

/-- No read, callback or cache replacement occurs when input admission fails. -/
theorem ContextSlot.call_input_error (slot : ContextSlot ready) (codec : Codec Input Wire Error)
    (project : Input → Context)
    (run : ∀ input, Snapshot ready (project input) → Except Error Output) (wire : Wire) (error : Error) (failed : codec.decode wire = .error error) :
    slot.call codec project run wire = ⟨.error error, slot, none⟩ := by
  simp [ContextSlot.call, failed]

/-- Callback/output errors retain the same next cache as successful execution. -/
theorem ContextSlot.call_input_ok (slot : ContextSlot ready) (codec : Codec Input Wire Error)
    (project : Input → Context)
    (run : ∀ input, Snapshot ready (project input) → Except Error Output) (wire : Wire) (input : Input) (valid : codec.decode wire = .ok input) :
    slot.call codec project run wire =
      ⟨run input (slot.read (project input)).1, (slot.read (project input)).2.1,
        some (slot.read (project input)).2.2⟩ := by
  simp only [ContextSlot.call, valid, ContextSlot.readAlong]

/-- The complete value/error outcome agrees with uncached proof-aware execution. -/
theorem ContextSlot.call_outcome (slot : ContextSlot ready) (codec : Codec Input Wire Error)
    (project : Input → Context)
    (run : ∀ input, Snapshot ready (project input) → Except Error Output) (wire : Wire) :
    (slot.call codec project run wire).outcome =
      match codec.decode wire with
      | .error error => .error error
      | .ok input => run input ⟨build ready.factories (project input), rfl, ready.valid (project input)⟩ := by
  cases found : codec.decode wire with
  | error error => simp [ContextSlot.call, found]
  | ok input =>
    simp only [ContextSlot.call, found, ContextSlot.readAlong]
    exact congrArg (run input) (Subtype.ext (slot.read_value (project input)))

/-- Input transcoding preserves errors, state and the optional read/hit marker. -/
theorem ContextSlot.call_represent {Other : Type r} (slot : ContextSlot ready)
    (codec : Codec Input Wire Error) (project : Input → Context)
    (run : ∀ input, Snapshot ready (project input) → Except Error Output)
    (pack : Wire → Other) (unpack : Other → Wire) (inverse : ∀ wire, unpack (pack wire) = wire)
    (wire : Wire) :
    slot.call (codec.represent pack unpack inverse) project run (pack wire) =
      slot.call codec project run wire := by
  simp only [ContextSlot.call, Codec.represent_decode]

/-- Thread the actual cache state through requests, stopping on the first input,
callback or output refusal. Failure returns the failing call's next cache. -/
def ContextSlot.callBatch (slot : ContextSlot ready) (codec : Codec Input Wire Error)
    (project : Input → Context)
    (run : ∀ input, Snapshot ready (project input) → Except Error Output) (wires : List Wire) :
    Except Error (List Output) × ContextSlot ready :=
  Validation.traverseState (fun slot wire => (slot.call codec project run wire).transition) slot wires

theorem ContextSlot.callBatch_error_iff (slot : ContextSlot ready) (codec : Codec Input Wire Error)
    (project : Input → Context)
    (run : ∀ input, Snapshot ready (project input) → Except Error Output) (wires : List Wire) (error : Error) (final : ContextSlot ready) :
    slot.callBatch codec project run wires = (.error error, final) ↔
      ∃ before wire after outputs next, wires = before ++ wire :: after ∧
        slot.callBatch codec project run before = (.ok outputs, next) ∧
        (next.call codec project run wire).transition = (.error error, final) :=
  Validation.traverseState_error_iff _ _ _ _ _

theorem ContextSlot.callBatch_represent {Other : Type r} (slot : ContextSlot ready)
    (codec : Codec Input Wire Error) (project : Input → Context)
    (run : ∀ input, Snapshot ready (project input) → Except Error Output)
    (pack : Wire → Other) (unpack : Other → Wire) (inverse : ∀ wire, unpack (pack wire) = wire)
    (wires : List Wire) :
    slot.callBatch (codec.represent pack unpack inverse) project run (wires.map pack) =
      slot.callBatch codec project run wires := by
  unfold ContextSlot.callBatch
  rw [Validation.traverseState_map]
  congr 1
  funext slot wire
  rw [ContextSlot.call_represent]

end Requirements
end LeanPoo.Functional
