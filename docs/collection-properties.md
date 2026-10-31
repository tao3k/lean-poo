# Complex model-driven collection properties

Gerbil-POO’s `examples/collection-properties.ss` is a runnable `:std/test` example, not a
second property-testing framework. Its `collection-properties-test` suite is
re-exported by the checked `t/collection-testing-test.ss` module, so normal local
and CI checks run it alongside the reusable trace-protocol controls.

From the Gerbil-POO checkout, use the existing guarded build and test entries:

```sh
just build test-program
just test-file t/collection-testing-test.ss
```

The complete workflow remains `just _check-collections 2 1 4`. No Lean checkout,
custom loader, extra environment variable or alternate test runner is required.
Downstream projects can copy the example's domain model/fixture pattern into a
local test module and export an ordinary `*-test` suite. Package imports and
configuration follow [the PBT RFC](pbt-design-rfc.md#downstream-scheme-integration).

## Scenarios

| Example | Required behavior | Deliberately broken implementation |
| --- | --- | --- |
| `handoff` | Two staged receipts cannot independently exchange unique owners; deletion and re-staging recover; an inverse may itself conflict with the new owner | Publish primary data after index approval failed |
| `rolling-upgrade` | Pending receipts outlive two source revisions as data, but old installation/inversion refuses; newly staged receipts recover and release conflicting owners | Report stale receipt installation as successful |
| `optimistic-aba` | A/B/A restores the old value and permits the receipt in the same epoch; a source revision still rejects that receipt even if values agree | Ignore the source epoch while retaining the expected value |

The first example concerns independent single-receipt installation. It does not
claim that the library's existing atomic multi-key delta cannot exchange owners.
The ABA example intentionally does not impose serializability or reject every
historical touch: the actual delta contract compares expected old values within
a captured source epoch. Tests must preserve that distinction.

## What makes these property tests

Each example declares a typed `Scenario` Record. `collection-model` normalizes
and owns the command prefix, rejects disabled prefixes before creating a real
fixture, and changes only the existing model's draw policy. A copied prefix
cannot be changed by mutating the caller's scalar command vectors.

A scenario uses the same sampler across both RationalDict and trie, seeds 7, 41
and 83, four trials per seed/backend, and 48 commands per trial. Required prefixes
are followed by state-dependent random suffixes; these are not just fixed scripts.
Normal runs compose `property-action` with a report consumer through the existing
Reader/FUN boundary. Every trial creates a fresh backend/index family.

Every step compares the result, complete canonical primary bindings and complete
unique-index ownership against the independent list oracle. Refusal must preserve
both primary and indexes. Exceptions and malformed adapter outputs remain errors.

For each backend the example then injects its known fault, requires a `failed`
report without an exception cause, checks that dependency-preserving shrinking
produces a shorter valid witness, and reproduces it through both concrete-witness
and seeded replay. A diagnostic must identify the expected result/state phase.
Invalid, stale or error reports cannot masquerade as discovered counterexamples.
The shrink budget is 96 attempts; no global-minimality claim is made.

## State-derived logical handles

A custom prefix can already contain receipt 2 before step 2. Using a step number
as the next producer ID would eventually propose an invalid duplicate producer.
`next-ticket` folds over current retained tickets and chooses at least one more
than every retained ID. It preserves the step count only as a lower bound.
This also covers receipts retained across source epochs.

The dedicated control uses a short prefix with receipt 2, repeatedly selects the
new-producer alternative and requires every generated operation to be enabled.
It also checks caller mutation isolation and rejection of a missing producer or
malformed command before fixture effects. Handle selection is linear in retained
receipt count; constant-time bignum arithmetic or arbitrary host callback costs
are not claimed.

## Formal scope

`LeanPoo.Functional.PropertyTesting.freshHandle_lower`, `freshHandle_gt` and
`freshHandle_not_mem` prove the maximum-fold freshness rule for arbitrary finite
retained ID lists. The existing draw, retirement, shrink and replay laws continue
to apply; no second generator or recursion engine is introduced.

Top-level `Examples/CollectionTesting.lean` adds concrete same-epoch ABA versus
cross-epoch refusal controls alongside the existing complete finite index oracle.
These are finite kernel-checked laws and examples. Runtime adapter fidelity,
callback termination and concurrency/serializability remain explicit boundaries.
The Scheme differential tests independently exercise the actual two backends.
