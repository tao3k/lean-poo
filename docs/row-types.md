# Controlled recursive types and row polymorphism

This advances the original type-system **future work**, particularly “Types for
Objects” and the Appendix C/D Self/Super constraints. The paper explicitly calls
out subtyping, variance, fixed points and row polymorphism while warning that an
unrestricted combination may be undecidable. The implementation below admits a
finite protocol; it is not attributed to the original Racket listings.

## Object rows and field replacement

The existing type expression language now includes:

```scheme
Never
(Maybe T)
(Object ((name Type) ...) open)
(Object ((name Type) ...) closed)
(Object ((name Type) ...) (Row Extra))
(Mu Node 3 (Object ((value UInt) (children (List Node))) closed))
```

Field names are unique symbols and are **literal labels**, even if spelled like a
type variable. Substitution only transforms field Types. Open rows require their
listed fields and allow undeclared fields. Closed rows require exactly their
listed names, independent of order. Only declared fields are validated/wrapped;
open extras remain unrestricted values and may themselves contain arbitrary data.

An object source replaces an open target when every target field exists in the
source and the corresponding source field Type replaces its target field Type.
A closed target additionally requires a closed source with no extra names. Thus
width subtyping works for open interfaces, while exact closed contracts reject
extras. Field replacement is covariant for **observations/validation**, including
Function argument contravariance and result covariance. Mutable field writes are
not made covariant by this rule, and prototype ancestry implies no such relation.

Object expressions compile through the existing `ObjectContract.` responsibilities
and its reject/delegate policies; Function and container fields retain recursive
normalization. No alternative object engine or weakening of unknown-field checks
is introduced. Maybe uses the existing absent-value convention, not false.

## Row substitution and inference

`prototype-type` retains the existing explicit `.parameters` API. A row tail such
as `(Row Extra)` references an ordinary declared outer Type variable. Its ground
assignment must normalize to an Object Type. Explicit fields and the extension's
fields must be disjoint; extension order and open/closed tail are retained. Row
variables are not implicit wildcards or existential values. The receiver receives
ordinary Type descriptors through persistent `specialize` as before.

`infer-prototype` reuses the same complete finite Cartesian search. Each assignment
must normalize the body and satisfy every bound/query. A scalar in a row position
or an overlapping extension is an invalid assignment. Those precise `bounds`
refusals are filtered; unsupported syntax, malformed declarations, work exhaustion
and unexpected exceptions still escape. They never become `no-solution`.
Explicit instantiation exposes the same wrong-kind/overlap as a typed bounds refusal.

Unique completed search alone constructs an instance. Multiple row extensions
remain ambiguous; an empty completed candidate search yields no solution. The
solver does not invent fields, fresh row variables, principal types or unbounded
candidate universes. Source syntax is captured strictly before lazy schema fields
are constructed, and public metadata is revalidated on every request.

## Finite recursive closure

`(Mu X n F)` denotes **exactly n applications** of the guarded body F to Never.
Never has no values. At depth one, a node with an empty children List can conform;
a child requiring the depth-zero Never cannot. A rejected deeper/cyclic value is
outside this finite Type, not evidence that the corresponding unbounded recursive
Type is empty or divergent. Increasing n constructs a new descriptor and requires
fresh admission/evidence. No active-pair comparison can succeed coinductively.

The binder must be fresh and guarded through a List, Tuple, Maybe or Object field.
Occurrences in any Function argument, recursive row tails, nested Mu binders and
unguarded aliases are unsupported. Independent Mu expressions may be composed in
other Types. Mutual recursive type equations and general equirecursive inference
remain outside this protocol. Function-valued positive fields are still wrapped
and checked when called; finite unfolding proves no host callback termination.

`recursive-types.ss` uses the existing Interaction map/request/solve interface.
One request decreases the numeric unfolding depth, and substitution copies only
checked finite syntax. Shared work is charged during parsing, substitution,
unfolding, row normalization, subtype comparison, inference and compilation. No
recursive memo or previously admitted descriptor is reused as proof of a new one.
Shared runtime graph nodes can be checked at several occurrences; graph identity
preservation or cycle acceptance is not promised by normalization.

## Bounds and failure semantics

| Boundary | Exact meaning |
| --- | --- |
| Mu depth | Explicit integer 0..16; zero is Never, not a pending successful Type |
| Syntax/expanded pair depth | Maximum 64, including list spines, before unsafe traversal |
| Shared work | Default 8192; allowed 1..1048576; no reset between inference and construction |
| `malformed` TypeRefusal | Duplicate/non-symbol fields, invalid row grammar/binder/depth |
| `unsupported` TypeRefusal | Unguarded, nested, negative-position or row-tail recursion |
| `bounds` TypeRefusal | Wrong row kind or overlapping row extension; invalid search candidate |
| `exhausted` TypeRefusal | Syntax/expanded depth or actual shared work incomplete; no partial instance |
| Existing TypeError | Value outside a completed finite descriptor, including recursive cutoff |
| Existing callback error | Original cause propagates, without overload/search fallback |

A larger caller-chosen work allowance can retry an exhausted request. A deeper
finite Type can admit a previously too-deep value, with a new descriptor/context
for exact evidence binding. Neither action converts old evidence into new approval.
The quota bounds bookkeeping visits, not primitive bytes/GC or arbitrary computed
slot effects. Stable Type definitions and metadata during a sequential request,
and terminating declared getters/consumers, remain premises. Existing watchdogs,
thread limits and heap caps remain enabled; no machine/compiler verification is claimed.

## Concentrated acceptance and proof scope

`examples/row-services.ss` combines inferred audit rows, a higher-order handler,
shared recursive service trees and nested Function fields. Existing FUN checked
admission runs before `refine`; exact subject/descriptor/context publication uses
`bind-evidence`. Tests cover disjoint/wrong-kind/colliding row candidates, unique/
ambiguous/empty search, field names matching variable names, width/depth/Function
variance, closed-key rejection, shared nodes, cyclic/deeper cutoff rejection,
negative nested outputs, stale evidence and failed-budget retry.

Lean `Functional.RowTypes` proves named lookup membership, checked shape/field
replacement, semantic observation replacement under explicit field-behavior
premises, row disjointness, exact splice result/lookup preservation and validity
of unique finite assignments through the existing inference theorem. Its field
relation is parameterized so existing Type/Function laws and nested row laws can
compose; arbitrary host predicate implications are not silently assumed.

`Functional.RecursiveTypes` proves exact equality of finite expansion with the
existing safe recursive interpreter at n+1 observation steps, the unfolding law,
conditional monotonicity of successive approximants, incomplete-budget refusal and
exact successful bounded results. The budget theorem is an abstract complete-work
boundary; it is not an exact cost/heap theorem for Gerbil syntax expansion.
`Examples/RowTypes.lean` remains in the top-level Examples tree.

Racket motivation, Lean semantic premises and Gerbil execution are separate
receipts. This is not proof of the Gerbil compiler or all recursive/row type
inference. No Scheme source, example or test requires a Lean checkout. Full existing
checks are retained alongside the focused protocol suite.

## Record and Object carrier replacement

Explicit finite Record and Object rows now use the same complete named-field
replacement protocol in either direction. Both denote POO objects: Record
compiles through Class/RecordSlot and Object through ObjectContract. The public
dispatcher previously selected their shared rule only for identical constructor
kinds; it now admits either pair before the same-kind container cases. No second
field solver, wrapper engine, namespace or descriptor conversion is introduced.

Record-to-Object requires every Object field to have a required source field
and readable child inclusion. Object-to-Record treats Object fields as required;
a missing optional Record field is safe only for a closed Object source, which
establishes absence. Open sources cannot hide unchecked values at missing optional
names. Closed targets still require a closed source and reject every extra
declared key, including optional ones. Field order and original descriptor kinds
remain captured metadata, not normalization targets. Nested Function variance,
List/Map values and prefix-specialized declarations use the existing child rule.
Map keys and direct ordered Union bounds remain invariant. No Any is synthesized.

The bridge applies to admitted literal Record/Object syntax, not opaque captured
Class/Schema tokens, arbitrary ancestry, custom Slot callbacks or implicit
layout discovery. Initialization/defaults/hooks and receiver-bound wrapping stay
with their original validators; the relation does not grant covariant writes,
normalizer effect equivalence, serialization conversion or approval reuse.
Missing coverage is false; malformed/unsupported metadata and shared budget
exhaustion retain their original typed failures. Optional absence creates no
field/default, and successful input validation does not excuse invalid outputs.

infer-worker-service composes an inherited worker Record, structural interface,
UInt-indexed Map/List Function fields, complete inference, parameter-prefix
specialization and qualified declarations. Existing descriptor-service-action
sequences FUN/IO, refine and exact bind-evidence. Regressions cover both publication
directions, inherited defaults, optional absence, callback rejection, policy
retry, genuine cross-kind candidate ambiguity and opaque-token refusal. A closed
Object output still rejects an optional input field retained by the host operation.

RowTypes.requiredRow is an observation-only required-presence projection. Its
lookup and admission equivalence laws connect Object reads to the existing Slot
protocol; recordToObject_sound/objectToRecord_sound then reuse recordCheck_sound.
DeclarativeMetadata.inferRowView_sound retains the exact captured signature,
candidate/layout artifact and universal target observations after one complete
unique solve. Top-level Examples/RowTypes.lean composes field Function variance,
closure/presence refusals and declaration provenance. Host projection and child
behavior remain explicit premises; these are not compiler or arbitrary callback
proofs. This advances the article's type-protocol future work, consistent with
its element-inclusion definition of subtyping, rather than attributing finite
inference to the reference Racket implementation.
