# Shared compilation and disjoint test artifacts

The preceding Scheme CI run built 281 distinct modules and executed 627 distinct
backend jobs. No repeated module or backend job was found. In the timestamped
log, compilation spent about 42 seconds before the first module, 36 seconds
lowering modules, then 168 seconds executing backend jobs. The released Linux
compiler drains backend jobs after graph construction, so those phases did not
overlap. The complete build job took 262 seconds; its compilation step took about
246 seconds. These are different timing boundaries.

The repository consumes the verified, already compiled Gerbil release. It neither
builds that compiler nor adds Bazel. `std/make` continues to own dependency order,
module compilation and backend scheduling. This change splits the existing work:

1. Compile the full shared non-test graph once and publish the current run's
   source-bound artifact.
2. Compile each disjoint functional test group on a separate CI runner against
   that shared graph. Each writes only its own test roots to a separate output
   directory. All previous source inputs and all tests remain covered.
3. Execute every independent test with the existing harness and limits.
4. Require the complete group inventory and current revision stamps, merge the
   admitted outputs, and run every test again in one bounded process.

Shared compilation has an exact cache key for the release, host compiler/linker,
platform and every non-test/build input. Test-only changes preserve this key.
Group caches additionally bind the exact shared-library byte generation, the
complete test-source snapshot and group source key. Gerbil generates timestamped
internal binding identities, so a rebuild of identical source is not assumed to
match an older compiled group. This deliberately invalidates all test groups on any test edit, covering
possible cross-group macro dependencies without assuming independence of source
semantics. Compilation ownership is disjoint; semantic dependencies need not be.
No prefix fallback, timestamp repair or approval based only on producer SHA is
used. A hit skips compilation, never test execution. Original producer and current
admitted revision remain distinct.

`Functional/BuildCache.lean`, in the existing ConstructionCache namespace, proves
source/revision admission, test/shared identity separation, complete and unique
assembly, and a symbolic parallel critical-path inequality. `Examples/BuildCache.lean`
is in the top-level example inventory. Identities are supplied exact-source keys;
these laws do not establish hash collision resistance, Actions storage trust,
compiler correctness, actual worker overlap, memory bounds or measured speed.
Queueing, artifact transfer and process startup must be measured separately.

Native Scheme controls exercise group coverage, changed source identities,
malformed receipts, missing interfaces, stale run stamps and unexpected artifact
groups. Temporary admission fixtures are not executable artifacts. Full cold and
warm CI receipts, rather than a subset build's duration alone, qualify any speedup.

Independent compiler processes may reload shared expansion metadata. This can
increase aggregate runner work even when the critical path falls. The symbolic
bound compares the same supplied task costs, not a claim of equal CPU work
between the monolithic and distributed implementations.

The Lean gate retains automatic worker selection and every source-owned deadline.
Ordinary atoms run with the automatically selected worker count. After that pool
joins, the 42 explicitly deadline-bound stress atoms run exclusively in a separate
phase. Both a shared pool and a two-worker isolated stress pool produced deadline
failures on the local host, while the original isolated QueueSelection control
passed. Ordinary proofs retain automatic concurrency; stress tests cannot compete
with ordinary elaboration or with one another. The phase boundary occurs
before launch and does not consume a test's timeout. All commands remain in the
same complete inventory, including after an earlier phase's failure; deadlines,
failure status and process-group cancellation are unchanged. Actual phase starts
report their inventory and worker count in the progress stream.

The atom runner defaults to one Lean thread per file; independent files retain
automatic parallel workers. A local QueueSelection control completed with `-j1`
in 11.595 s while the same isolated `-j2` command hit its original 30 s deadline.
This is a host observation, not a universal runtime speedup claim. The original
memory/allocation/deadline budgets and complete source inventory remain intact;
`--lean-threads` still permits explicit controlled comparisons. The public
inventory regression checks the default thread budget for every selected file.

The complete local gate supervises ordinary atoms and exclusive stress atoms as
separate units, each with the existing 300 s phase ceiling. The latter starts
after the ordinary checks have joined, even if an ordinary check failed. This
increases the aggregate time available compared with putting both sequential
units under one 300 s clock; it does not extend any individual stress deadline.
A regression verifies disjoint, complete coverage of the canonical inventory and
failure propagation. When `LEAN_POO_ATOM_RECEIPT` is set, the gate writes separate
`.atoms.json` and `.stress.json` receipts under that prefix; standalone atom-runner
receipt behavior is unchanged. Phase progress and process-group cleanup remain
active throughout both units.
