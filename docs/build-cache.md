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
Explicitly deadline-bound stress atoms have at most two concurrent workers, with
the rest reserved for ordinary atoms. All commands remain in the same complete
inventory; no deadline is extended and failure/cancellation status is preserved.
This avoids bunching stress cases into an oversubscribed tail of the file list.
