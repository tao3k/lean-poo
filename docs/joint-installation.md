# Installation after joint approval

See [joint-receipts.md](joint-receipts.md) for ordered attempts by multiple approved
receipts, shared proposed-policy invalidation and six SCC lifecycle rounds.

This advances generalized-prototype future work, reusing original Racket Appendix B
`$lens-gen` (pin `9affa8fbbb4f12cbd98cb97f8b8b84474fc39429`, lines 2108–2133).
The paper provides lens-based composition, not these multi-service transactions.

## Opaque approval receipts

Native `joint-publication.approve` now performs the existing complete FUN revision
construction, all local admissions and final joint admission, then returns TWO
values: a private receipt and `#f`, or `#f` and a failure. It leaves the authoritative
snapshot unchanged. The receipt contains the exact staged request and candidate;
its constructor/accessors are not exported. Candidates that failed admission
cannot be turned into installable receipts through this API.

`install!` accepts only a receipt for that owner. Under the existing short mutex it
rechecks all old/proposed approval and source guards, then the expected whole
snapshot, before installing one bundle pointer. Failure returns the ACTUAL current
bundle and a failure, including when both head and metadata changed. Receipts are
not automatically refreshed, and replay after successful installation is stale.
`submit!` composes these two operations with standard `call-with-values`, retaining
the existing one-call current-bundle/failure convention.

For example, existing native component declarations can prepare two approvals:

```scheme
;; Both candidates use the same current graph, with different endpoint additions.
(defvalues (left left-error)
  (joint.approve owner (service.stage-current owner
    [(cons 'a (.cc service.Change. phase: 'merge))] 24 36 builder)))
(defvalues (right right-error)
  (joint.approve owner (service.stage-current owner
    [(cons 'b (.cc service.Change. phase: 'merge))] 24 36 builder)))
;; After checking both errors are #f, install the rival first. left is then stale.
(defvalues (winner installed-error) (joint.install! owner right))
(defvalues (held stale-error) (joint.install! owner left))
```

## Actual post-approval controls

`t/joint-installation-test.ss` uses returned receipts as deterministic phase
boundaries. Both local and joint approval have RETURNED before any interference;
no timing-dependent sleep or side-effecting approval callback is required.

- Two approved candidates independently add bridges/merge SCCs at different
  endpoints. The rival installs first; late installation returns that exact whole
  winner. Fresh staging combines A's merge with B's endpoint deletion/split,
  then A splits and both restore compact support. Old receipts remain stale after
  equal-valued policy/support round trips; independent feedback receipts are reused.
- Another approved candidate merges both services with total budget 48. Only its
  UNINSTALLED proposed shared policy changes to 49, which still admits 24+24.
  Installation fails by revision drift. Changing it back to 48 also refuses:
  equal values do not restore an old object revision. Reapproving the old staged
  request refuses; explicit new staging captures the new revision and succeeds.
  Subsequent component deletions/splits and restoration complete the lifecycle.
- A combined case drifts one approved candidate's proposed metadata while another
  independently approved candidate installs. The late receipt returns the rival's
  exact current graph/policy, then fresh staging continues from that topology.
- Foreign receipts, raw staged requests, `#f`, and jointly refused candidates cannot
  be installed. A foreign-owner attempt does not consume the receipt for its owner.

## Lean model and limits

`Functional.JointPublication.installChecked` reuses the existing component checked
installation decision for the ENTIRE universe-polymorphic bundle.
`checked_requirements` extracts current head identity, true earlier approval and
unchanged registered revision from accepted decisions. Whole-bundle, stale head,
metadata drift, exact commit and explicit fresh-revision retry laws are proved.
`Examples/JointInstallation` uses actual typed component sources, discovered SCC
graphs and successful resolver-equation receipts for asymmetric competing merges,
shared revision drift, split/merge restaging and final component erasure.

Finite declared components, lawful lenses, correct explicit dependencies, immutable
installed metadata, fresh snapshot identities and faithful pure locally total
callbacks remain premises. The abstract revision carrier represents ALL registered
guards; native object revisions must faithfully implement that premise. Diagnostic
writes affect only uninstalled proposed policies BETWEEN phases. The guard checks
are not a proof of synchronization with arbitrary concurrent writes inside a
supported object's internals or after the final revision read; production policies
remain immutable. Readers capture one whole bundle. No arbitrary effect rollback,
general recursive convergence, distributed/durable atomicity, runtime/compiler
correctness or performance claim is made.
