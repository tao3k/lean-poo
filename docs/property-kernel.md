# Using the property-testing modules

The generic library is a standard Gerbil project at `testing/core/`. Its
`gerbil.pkg` declares `clan/property-testing`; it imports no POO modules.
From that directory, use the ordinary `gerbil build` command. The POO root
build invokes this same standard build before compiling typed consumers.

Import the modules you use directly:

```scheme
(export arithmetic-test)
(import :std/test
        (prefix-in :clan/property-testing/generator generator.)
        (prefix-in :clan/property-testing/property property.))

;; Draw and shrink signed integers with one explicit random source.
(def integers
  (generator.make-generator
    (lambda (random size) (- (random (+ (* 2 size) 1)) size))
    generator.integer-shrinks))
;; Domain admission and shrink measure are supplied by this application.
(def integer-domain
  (property.make-specification exact-integer? abs))

;; Standard Gerbil TestSuite discovery owns execution.
(def arithmetic-test
  (test-suite "integer arithmetic"
    (test-case "addition identity"
      (check (property.report-status
        (property.check-property integers (lambda (x) (= (+ x 0) x))
          integer-domain seed: 42 cases: 100 size: 50))
        => 'passed))))
```

The example is exported as a normal `*-test` suite for `gerbil test` discovery.
See `examples/property-kernel.ss` for dependent packets, non-injective maps,
lazy bounded shrinking, source invalidation and a model with logical handles.
`testing/core/model.ss` owns model execution and repair; it does not instantiate
a POO object or prescribe an application representation.

POO users import `:clan/poo/testing/type` for descriptor-driven generators and
reports, `:clan/poo/testing/function` for signature derivation, and
`:clan/poo/testing/recursive-generation` for bounded recursive derivation.
Those modules own Type validation, wrapping and revision observations. They
supply these operations to the generic library through explicit callbacks.
There is no `api.ss` forwarding module or alternative dynamic import mechanism.

A generator's shrink callbacks must preserve its intermediate domain. The final
specification additionally checks domain admission, a natural-valued measure and
strict Boolean properties. Reports distinguish failure, errors, stale sources
and exhausted generation. Shrink fuel counts forced proposals, including rejected
ones; zero fuel does not invoke a shrink callback. A minimum refers only to an
observed exhausted immediate neighborhood, not a globally smallest value.

Seed replay regenerates under the recorded configuration; concrete replay checks
the retained witness without drawing or shrinking. Mutable callback dependencies
must be declared through accurate source observers. The isolated regression builds
the actual generic package and executes twelve cases without any POO modules in
its package directory, under the existing heap and timeout limits.

Model normalization is an explicit boundary: `check-trace` first prepares the
entire command list and executes exactly those normalized objects. Its mismatch
report carries the prepared command. A late domain/precondition refusal or
normalization exception opens no fixture. `valid-trace?` projects the same
preparation; do not use it as a substitute for `check-trace`'s own preflight.
The POO facade supplies already-wrapped commands with identity normalization.

Interrupted shrink reports retain the last confirmed witness and charged work.
A returned proposal counts even when admission, cost, property or source checks
fail; EOF and an iterator exception produce no proposal. The error's cause is
retained, `minimal?` is false, and concrete replay requires a `failed` report.
A diagnostic reduced value on an `error` or `stale` report is not certified evidence.

## Composable generator proof boundary

`LeanPoo.Functional.PropertyTesting` now also has the functionally separated
`LeanPoo/Functional/PropertyGenerators.lean` module. `weightedChoice_member` and
`weightedChoice_exists` cover positive-weight membership and all valid finite
offsets; they do not establish a host random distribution. `scheduledSamples_size`
and `scheduledSamples_length` retain actual size/trial ownership. The
`resolveDelayed_budget` law bounds callback requests, conditional on each pure
step returning. `shrinkProposals_budget` and `shrinkProposals_preserves` charge
pruned proposals while retaining the last valid false witness.

The top-level `Examples/PropertyGenerators.lean` checks weighted boundaries,
size schedules, zero fuel and pruned-child accounting. Existing mapped-preimage,
dependent-selection and stale-observation laws remain the provenance premises.
These are finite source laws; runtime PRNGs, callbacks and backend representations
still require their own executable admission. Scheme imports no Lean checkout.
