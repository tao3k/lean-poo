package ReadRouteSharing {
    private import ScalarValues::*;
    requirement def PureSweep {
        attribute fixedWorld : Boolean;
        attribute noCallbacksOrWriters : Boolean;
        attribute routeOperationsAdmitted : Boolean;
        attribute freshLocalIndex : Boolean;
        attribute identityConversionOrOriginalPath : Boolean;
        require constraint {
            fixedWorld and noCallbacksOrWriters and routeOperationsAdmitted and
            freshLocalIndex and identityConversionOrOriginalPath
        }
    }
    requirement def OrderedRejection {
        attribute issuancePerRecord : Boolean;
        attribute keyGrammarPerRecord : Boolean;
        attribute liveStatePerRecord : Boolean;
        attribute checkedReceiversOnly : Boolean;
        attribute bootstrapDoesNotCertifyTables : Boolean;
        require constraint {
            issuancePerRecord and keyGrammarPerRecord and liveStatePerRecord and
            checkedReceiversOnly and bootstrapDoesNotCertifyTables
        }
    }
    requirement def IndependentEffects {
        attribute noEntryIndexAtReturn : Boolean;
        attribute unknownUsesOriginal : Boolean;
        attribute topologyHasNoApprovalFlags : Boolean;
        require constraint {
            noEntryIndexAtReturn and unknownUsesOriginal and topologyHasNoApprovalFlags
        }
    }
    requirement def BoundPositions {
        attribute originalReadOrder : Boolean;
        attribute receiverIndexPreservedOnExtension : Boolean;
        attribute recordAuthenticatedBeforeBinding : Boolean;
        attribute sharedPositionsHaveNoApproval : Boolean;
        require constraint {
            originalReadOrder and receiverIndexPreservedOnExtension and
            recordAuthenticatedBeforeBinding and sharedPositionsHaveNoApproval
        }
    }
}
