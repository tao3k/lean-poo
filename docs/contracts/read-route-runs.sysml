package ReadRouteRuns {
    private import ScalarValues::*;
    requirement def ReceiverRouteMarkers {
        doc /* marked_eq_serial preserves ordered issuance/key/route/live
               refusal. Mark only the first non-bootstrap read in the existing
               receiver index. route_markers_unique covers interleaved owners.
               Markers describe structure, not successful validation results. */
    }
    requirement def FixedAndEffectBoundaries {
        doc /* native_fixed_refusals_exact retains complete preflight.
               native_marked_callback_exact keeps repeated entry issuance,
               the author action and independent return marker checks.
               Ordinary observers never receive a scoped checker. */
    }
    requirement def ActualReceiverState {
        doc /* Check every actual value, revision, instance and registration.
               Authenticate topology/marker identity on each acquisition.
               Fixed-oracle/native correspondence remains a gate. Raw-vector
               epoch-only admission stays disabled. Preserve weak ownership
               and the original Module/downstream budgets. */
    }
}
