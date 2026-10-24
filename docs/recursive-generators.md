# Automatic guarded recursive generators

This advances the original Type Descriptors discussion of pseudo-random value
generators and value compressors. It is future-work implementation, not a claim
that these APIs already appear in the paper's Racket listings.

## Closed protocol

`generator` discovers a finite descriptor graph by identity. Shared descriptors
have one graph node. It derives List, Tuple, Pair, Union, Maybe and OrFalse, plus
Bool, Integer, UInt, String, Exactly and Enum leaves. Custom `.generator` callbacks
remain supported with explicit dependency declarations. Unsupported opaque Types
require such a callback. No unsafe host recursive knot or Lean checkout is used.

Cycles must cross a List/Tuple/Pair carrier. Transparent Union/Maybe/OrFalse alias
cycles are refused before any recursive `.element?` call. The minimum-cost table
reads only the preceding unfolding-depth row and saturates at `node-budget + 1`.
Each draw chooses an inhabitable alternative within its allowance. Mandatory
siblings reserve their minima once; unused child quota is restored without
repeated suffix construction. Random choices and child seeds are consumed before
returning the local Interaction, so continuations capture no shared PRNG state.

The existing `recursive.solve` interprets generation, bounded membership and
shrinking requests. Each invocation owns its explicit seed and remaining quota;
random results never reuse a cross-run recursive memo. Recognition uses finite
private derivations, handles cyclic carriers without native recursive Type calls,
and enforces the configured unfolding/node subdomain. It does not claim that a
value outside that bounded subdomain is outside its unbounded Type.

## Bounds and outcomes

| Setting | Meaning | Default / admitted range |
| --- | --- | --- |
| `depth:` | Maximum descriptor unfolding along a generated/recognized path; leaves count one | 32 / 0–64 |
| `node-budget:` | Total emitted grammar nodes, including transparent wrappers | 256 / 0–65536 |
| `descriptor-budget:` | Root plus every discovered descriptor-edge occurrence, including shared edges | 256 / 1–1024 |
| `search-budget:` | Request visits for each membership or shrink traversal, including failed alternatives; also a returned-candidate cap | 8192 / 1–1048576 |
| `size:` | Integer/string size and maximum List width, still constrained by available nodes | Existing nonnegative bound |
| `shrink-budget:` | Existing global proposal attempts, including rejected candidates | Existing nonnegative bound |

`passed` requires every trial to return Boolean true with current dependencies.
`failed` retains a valid false witness. `exhausted` retains a typed
`generation-refusal-kind` such as depth/nodes/descriptors/search/candidates;
it never means pass, divergence or a globally empty Type. `unsupported` identifies
transparent alias cycles. `stale` rejects changed compiled sources. Callback
exceptions remain `error` with the exact cause and never trigger branch fallback.
Invalid configuration is rejected. No callback exception is converted to false.

A failed compilation has no complete graph snapshot: its report has
`replayable? = #f`, and replay explicitly refuses it. Runtime depth/quota exhaustion
and false witnesses from a completed graph are replayable with the same sampler,
seed and limits, provided all captured sources and callbacks remain stable.
Reports preserve effective sampler limits when a custom sampler is supplied.
A new compilation is required after descriptor revision; an old sampler cannot
acquire authority by capturing a newer test-start snapshot.

Shrinking is branch preserving for Union, structural for List/Tuple/Pair and
absence reducing for Maybe/OrFalse. It uses the same bounded membership and
strict natural measure descent as the previous testing protocol. `minimal?`
only describes the supplied immediate neighbourhood; incomplete/error/exhausted
runs do not certify it. Host callbacks must terminate and return finite data.
Opaque callbacks must keep their supplied PRNG local and return stable values;
retained mutable PRNG closures are outside the replay premise.
Grammar visit quotas do not prove primitive execution time or byte allocation;
existing process watchdogs and heap limits remain necessary.

## Three-way evidence

| Paper / Scheme concern | Gerbil implementation | Lean evidence |
| --- | --- | --- |
| Descriptor-driven generators/compressors | `generation-graph.ss`, `recursive-generation.ss`, existing property runner | `Functional.RecursiveGeneration` finite production grammar |
| Finite recursive requests | Existing Interaction bind/solve, explicit quota and seed inputs | `program_observation` identifies explicit requests with the bounded DFS result |
| Successful construction and total quota | Depth rows, reserved sibling costs, guarded branches | `construct_checked`, `construct_budget`, `restore_budget`, `saturation_feasible` |
| Failed choice/callback and exhausted depth | Distinct report outcomes and original causes | `depth_refusal`, `choice_refusal`, `callback_refusal` |
| Shrinking and replay | Same sampler, bounded derivations and compilation source stamps | `shrink_checked`, `replay_choices`; existing source-admission laws |

The Lean trace model independently checks the proposed finite productions; it is
not extraction or a machine-level verification of Gerbil's dynamic-program table,
compiler, arbitrary scalar callbacks, PRNG distribution or heap identity.
`Examples/RecursiveGenerators.lean` supplies finite shared-tree, partial-trace,
quota, callback and source-depth controls. Scheme `examples/recursive-trees.ss`
combines mutually recursive Message/Batch descriptors, shared children, safe
service evaluation, Reader/FUN testing, counterexample shrinking and replay.
General recursive carrier laws, arbitrary closure synthesis and type inference
remain open. This closes the supported automatic finite-data protocol.
