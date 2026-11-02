# Slot observation scopes

This advances the generalized prototype protocol proposed as future work. The
Scheme implementation remains independent of this Lean checkout.

One standard Gerbil dynamic parameter carries the existing frame, observers and
prechecks. Disabled observation uses false. Capture alone retains its original
frame directly; an observer scope records the same frame and the ordered callback
lists. `parameterize` owns nested restoration, exceptions, continuations and the
runtime's ordinary thread inheritance. There is no shared mutable process cache.

The disabled `without-observation` path calls its action directly. The active
path suppresses all three channels together. Observers and prechecks run in their
original inner-before-outer order, with observation disabled during callbacks.
Storage deduplication never deduplicates delivery. Frames, checked Functions,
exact failure objects and callback effects are not reconstructed or replayed.

`LeanPoo/Object/SlotObservation.lean` reuses `Prototype.DictionaryBridge`: unpacking
a packed scope restores every original payload, including arbitrary function
values without decidable equality. Its canonical representation rules out a
second allocated empty scope. Capture-only packing contains precisely the original
frame. Arbitrary interpreted results retain errors and event traces and leave the
caller's lexical scope unchanged. `Examples/SlotObservation.lean` covers nested
approval/source/converter observers, exact refusal payloads and capture reuse.

The cost law prices dynamic lookups/bindings, tag tests, field reads and context
allocation explicitly. Under explicit primitive-price hypotheses, disabled calls and delivery
are bounded by the earlier operations. The full bound retains the additional
capture-entry premium, including context allocation under existing observers.
The example with expensive capture preparation refutes an unconditional gain. Frame allocation, backend work, callback termination,
physical GC, host continuations and wall latency are not proved by this model.
The executable Scheme regressions separately exercise disabled calls, multivalues,
exact errors, nested prechecks, continuation reentry and independently created
thread scopes under the ordinary runtime.

The paired study preserves all collection phases and 219 summaries. Runtime
process-statistics wall time remains the original system clock; a separate runtime
monotonic duration is appended to observation history. The original five result
columns are unchanged. A difference between these clocks is diagnostic, not a
speedup. GC realtime, CPU and wall-minus-CPU residuals do not by themselves prove
collector pauses, scheduler interference, IO stalls or clock correction. Complete
entry wall time and tails must pass independently of primitive-count laws.

## Complete-workflow evidence

The [Scheme receipt](https://github.com/tao3k/gerbil-poo/blob/3f32a10/doc/slot-observation.md)
retains the matched source identities, original 219-summary suite, rejected module
split, initial consumer rebuild and every adverse observation. Two final
benchmark-target-cold complete-entry pairs were 74.34→71.26 and 58.52→53.87 seconds;
non-GC CPU fell 4.360 / 3.757 seconds. The maximum of those two complete entries
also fell, but there is no consistent compiler-wall improvement and no stable
all-tail guarantee. All original Scheme heap/deadline constraints remain.

The large residual was reproduced and partitioned. Of about 31.361 seconds,
22.234 occurred inside measured batches with no major faults; GC wall minus CPU
explained only about 3.128 seconds overall. A fast control also reported 58 major
faults. A candidate B/B control retained a 0.018971 CPU / 0.150661 wall-second call
with zero major faults. Neither fault nor switch counts identify pause duration.
The optimization does not claim to eliminate that physical off-CPU tail. These
runtime observations qualify the source-cost model; they are not its conclusions.

The new top-level example is registered in the existing full inventory, increasing
it from 343 to 344 independent Lean files. It uses the existing strict 30-second,
2 GiB and heartbeat-limited policy. The inventory regression checks all original
files and budget arguments, including the additional bounded example. There is
no compiler, C++, scheduler or runtime verification claim.
