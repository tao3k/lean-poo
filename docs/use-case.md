# Use case: build and run a prototype object

LeanPoo's primary job is to implement PO: compose object declarations, resolve
inheritance with C4, and run the resulting slots with a shared lazy instance.
Faré's POOF model and Gerbil-POO implementation guide this translation. The
library does not require a new proof of why POO works before an object can run.

## Declare behavior

An `Object.Declaration` contains direct slot methods and defaults. A slot can
be a constant, a thunk, a function of the final self, or a computation over an
inherited result. The inherited result stays delayed until the method calls
it. Lean uses `Value : Key → Type` to keep each key's value type explicit.

`Examples/TypedSlots.lean` shows a `Bool` slot and a `Nat` slot in one object.
The computed `Nat` slot can read final self and its inherited value without a
runtime type descriptor.

## Compose an object

`LeanPoo.mix` creates a declaration with ordered parents. `LeanPoo.extend`
adds one layer over a parent. `LeanPoo.plus` applies an override object's own
declaration and parents over a base; `LeanPoo.clone` copies a declaration and
topology while replacing selected direct values. These operations compile a
`Plan` through the C4 linearizer. The plan carries the schema, root, and
precedence used for all subsequent slot resolution.

`Examples/LayeredObject.lean` is a small executable path: a base declares
`retries = 2`; a child calls its inherited computation and adds one. The
resulting memoized object reads `retries = 3`. This configuration example is
only a compact way to show the object mechanics; the same PO operations apply
to behavior-bearing slots. The executable child can then be cloned with a
direct `retries = 8` value, producing a new object while the original remains
available. A `Memoized` object also exposes `extend`, `mix`, and `plus` for
further composition from its stored prototype. `Memoized.mixWith` combines
two independently built object families after checking that their graph node
names do not collide. The example combines a retry object and a timeout
object, then reads both slots from the result.

For a shared-base diamond, the example builds `Left` and `Right` over `Base`,
then mixes them as `Diamond`. C4 yields `Diamond → Left → Right → Base`;
the inherited computations produce `13` from the base value `2`.

## Run and inspect it

`Plan.memoize` ties one shared lazy thunk table for the object's declared
slots. `Memoized.read` probes a slot and `Memoized.ref` reports a missing
required slot. `LeanPoo.hasSlots` checks a finite set of required keys;
`LeanPoo.allSlots` derives declaration order from the C4 chain.
`Memoized.foldSlots` visits every declared typed value in that order, while
`Memoized.values` materializes the key/value pairs.

`Memoized` uses Lean thunks to share lazy values. The explicit immutable
`Cache.peek` interface is used when a caller needs to inspect an already
cached value without forcing a computation.

`Memoized.reviseSlot` and `reviseDefault` return new executable objects from
recompiled prototype declarations. In the example, an old object still reads
`2` after a revised object starts reading `5`. This is the persistent Lean
counterpart of editing a prototype; it does not mutate an existing instance.

The lower-level `Plan.resolve` accepts an explicit final self. `Prepared` and
`Cache` keep assembled slot methods and evaluated values separately. These
operations serve the same PO object model; they do not define another
inheritance or slot evaluator.

## Proof objects are a later layer

`Proof.Patch`, `Proof.pending`, and `CertifiedObject` are available for clients
that need to carry obligations across object changes. They do not define PO
composition and are not required for ordinary `mix`, `extend`, `memoize`, or
slot reads. A concrete policy integration would provide its own propositions
and certificates; no Cedar policy semantics are implemented here.
