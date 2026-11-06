import LeanPoo.Functional.StatefulValidation

/-! Finite byte I/O at the standard Reader/Writer boundary. Natural spans model
already admitted nonnegative fixnums. Host reads/writes may change state on error;
this model does not prove port internals, scheduling, flushing or rollback. -/
namespace LeanPoo.Functional.ByteIO

/-- Reader spans are admitted before any effect, including their minimum demand. -/
def validSpan (capacity offset length need : Nat) : Bool :=
  decide (offset ≤ capacity ∧ length ≤ capacity - offset ∧ need ≤ length)

/-- The standard Reader owns partial transport and minimum-input enforcement.
An empty admitted span does not invoke it; refused spans preserve the state. -/
def readSpan (read : Nat → Nat → State → Except Error (List UInt8) × State)
    (bad : Error) (capacity offset length need : Nat) (state : State) :
    Except Error (List UInt8) × State :=
  if validSpan capacity offset length need then
    if length = 0 then (.ok [], state) else read length need state
  else (.error bad, state)

/-- Invalid spans leave both stream state and caller buffers untouched. -/
theorem refused_span (read : Nat → Nat → State → Except Error (List UInt8) × State)
    (bad : Error) (capacity offset length need : Nat) (state : State)
    (invalid : validSpan capacity offset length need = false) :
    readSpan read bad capacity offset length need state = (.error bad, state) := by
  simp [readSpan, invalid]

/-- Zero demand skips transport even when the Reader would fail or consume input. -/
theorem empty_span (read : Nat → Nat → State → Except Error (List UInt8) × State)
    (bad : Error) (capacity offset : Nat) (state : State) (inside : offset ≤ capacity) :
    readSpan read bad capacity offset 0 0 state = (.ok [], state) := by
  simp [readSpan, validSpan, inside]

/-- Exact input rejects a short successful read while retaining its consumed state.
The private partial buffer is not a successful result. -/
def exact (read : State → Except Error (List UInt8) × State)
    (eof : Error) (count : Nat) (state : State) : Except Error (List UInt8) × State :=
  let (outcome, next) := read state
  (outcome.bind (fun bytes => if bytes.length = count then .ok bytes else .error eof), next)

/-- Exact success guarantees the public requested length. -/
theorem exact_length (read : State → Except Error (List UInt8) × State)
    (eof : Error) (count : Nat) (state final : State) (bytes : List UInt8)
    (accepted : exact read eof count state = (.ok bytes, final)) : bytes.length = count := by
  cases h : read state with
  | mk outcome next =>
    cases outcome with
    | error cause => simp [exact, h, Except.bind] at accepted
    | ok raw =>
      by_cases size : raw.length = count
      · simp [exact, h, Except.bind, size] at accepted
        rcases accepted with ⟨rfl, _⟩
        exact size
      · simp [exact, h, Except.bind, size] at accepted

/-- A premature EOF does not roll back already consumed bytes. -/
theorem short_read (read : State → Except Error (List UInt8) × State)
    (eof : Error) (count : Nat) (state next : State) (bytes : List UInt8)
    (readResult : read state = (.ok bytes, next)) (short : bytes.length ≠ count) :
    exact read eof count state = (.error eof, next) := by
  simp [exact, readResult, short, Except.bind]

/-- Existing FUN bind order: read, then write, then return those same bytes.
Failure retains the failing endpoint's state; each invocation takes a fresh state. -/
def transfer (read : State → Except Error (List UInt8) × State)
    (write : List UInt8 → State → Except Error Unit × State) (state : State) :
    Except Error (List UInt8) × State :=
  let (outcome, next) := read state
  match outcome with
  | .error cause => (.error cause, next)
  | .ok bytes =>
    let (written, final) := write bytes next
    (written.map (fun _ => bytes), final)

/-- Input refusal suppresses output and preserves the exact input failure state. -/
theorem input_error (read : State → Except Error (List UInt8) × State)
    (write : List UInt8 → State → Except Error Unit × State)
    (state next : State) (cause : Error) (failed : read state = (.error cause, next)) :
    transfer read write state = (.error cause, next) := by simp [transfer, failed]

/-- Output failure retains both prior input consumption and output's failing state. -/
theorem output_error (read : State → Except Error (List UInt8) × State)
    (write : List UInt8 → State → Except Error Unit × State)
    (state next final : State) (bytes : List UInt8) (cause : Error)
    (ready : read state = (.ok bytes, next)) (failed : write bytes next = (.error cause, final)) :
    transfer read write state = (.error cause, final) := by
  simp [transfer, ready, failed, Except.map]

/-- Successful delivery publishes exactly the bytes read and the final sink state. -/
theorem delivered (read : State → Except Error (List UInt8) × State)
    (write : List UInt8 → State → Except Error Unit × State)
    (state next final : State) (bytes : List UInt8)
    (ready : read state = (.ok bytes, next)) (sent : write bytes next = (.ok (), final)) :
    transfer read write state = (.ok bytes, final) := by
  simp [transfer, ready, sent, Except.map]
end LeanPoo.Functional.ByteIO
