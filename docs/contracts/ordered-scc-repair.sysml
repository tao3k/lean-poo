package OrderedSccRepair {
    private import ScalarValues::*;
    requirement def RetainedDirection {
        attribute ownedRoster : Boolean;
        attribute capturedDirection : Boolean;
        attribute exactRowReplacement : Boolean;
        attribute survivingDirection : Boolean;
        require constraint { ownedRoster and capturedDirection
            and exactRowReplacement and survivingDirection }
        doc /* Reuse existing positions and packed-capture direction bits.
               Self edges do not merge distinct owners. Changed rows must
               preserve one certified direction before reusing SCC maps. */
    }
    requirement def RetainedComponents {
        attribute certifiedOldOwnerIndex : Boolean;
        attribute exactEffectiveEdgeDifference : Boolean;
        attribute additionsInsideOldComponents : Boolean;
        attribute removalsExternalOrSelf : Boolean;
        attribute cycleCertificateRetired : Boolean;
        require constraint { certifiedOldOwnerIndex and exactEffectiveEdgeDifference
            and additionsInsideOldComponents and removalsExternalOrSelf
            and cycleCertificateRetired }
        doc /* Preserve SCC equivalence and share old owner/member indices.
               Update adjacency and ordinary invalidation separately. A chord
               preserves membership but not the one-successor certificate.
               This classification grants no source or publication approval. */
    }
    requirement def SnapshotAndFallback {
        attribute oldSnapshotUnchanged : Boolean;
        attribute unsupportedRefused : Boolean;
        attribute fallbackWhenUncertified : Boolean;
        attribute noCurrentnessApproval : Boolean;
        require constraint { oldSnapshotUnchanged and unsupportedRefused
            and fallbackWhenUncertified and noCurrentnessApproval }
        doc /* Share old singleton owner/member maps, edit persistent adjacency
               indices and retain quotient/invalidation/publication checks.
               Unknown sources keep full validation. Full groups/order are
               explicit output work, never hidden inside a local edit. */
    }
}
