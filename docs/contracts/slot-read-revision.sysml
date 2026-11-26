package SlotReadRevision {
    private import ScalarValues::*;
    requirement def CoveredOrigin {
        doc /* Allocate the existing store privately; derive writer/reference
               coverage. Use actual fresh source identity and the existing
               issuer. A caller flag or public raw-vector epoch is insufficient.
               ReadRevision.untracked_write_counterexample forbids that shortcut. */
    }
    requirement def PerCellObservation {
        doc /* Values and versions project the SAME existing cells. Covered
               writes advance the changed cell version and owner generation.
               admitted_cell_exact and renewed_cell_exact preserve observations;
               unaffected_cell_remains_live avoids whole-owner invalidation.
               Snapshot maps are ghost witnesses, not copied runtime tables. */
    }
    requirement def RetirementAndExposure {
        doc /* changed_cell_stays_retired covers arbitrary later transitions,
               including ABA, same-value writes and deletion/reinsertion. Retain
               tombstones. Revoke before raw handoff; raw writes need not bump
               epochs. exposed_cell_stays_refused prevents silent reactivation. */
    }
    requirement def ExistingGraphAndEffects {
        doc /* Graph owns affected-consumer indexing and publication snapshots.
               ConstructionCache retains resolver/dependency equations. Preserve
               structural observations, original errors and independent checks
               across expansion/author callbacks. Unknown sources use actual-
               field validation. Native atomicity and exposure correspondence
               remain gates; no Scheme shortcut or QNT result is inferred. */
    }
}
