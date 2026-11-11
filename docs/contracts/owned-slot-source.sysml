package OwnedSlotSource {
    private import ScalarValues::*;
    requirement def PrivateRecipeStorage {
        attribute generatedStockConstructor : Boolean;
        attribute rawObjectsAbsent : Boolean;
        attribute privateCaptureUnchanged : Boolean;
        require constraint {
            generatedStockConstructor and rawObjectsAbsent and privateCaptureUnchanged
        }
        doc /* A flag over already allocated mutable SlotSpecs is insufficient.
               Unknown or caller-owned sources use ordinary complete capture. */
    }
    requirement def ExposureBeforeHandoff {
        attribute exposureCommitted : Boolean;
        attribute ticketSourceMatches : Boolean;
        attribute ticketEpochMatches : Boolean;
        attribute pendingIndexMatches : Boolean;
        require constraint {
            exposureCommitted and ticketSourceMatches and ticketEpochMatches and pendingIndexMatches
        }
        doc /* Reserve before construction/callbacks. Success retires the
               ticket; failure never restores private capture eligibility. */
    }
    requirement def RawWriteAndSnapshot {
        doc /* Raw field writes need an allocated record and do not notify
               source metadata. Old captured recipes remain unchanged.
               New capture after exposure reads actual raw fields. */
    }
    requirement def ExistingPublicationBoundary {
        doc /* Raw allocation tickets do not certify current raw contents or
               replace POO publication/read authority. Preserve independent
               Gerbil expansion and author callback entry/return checks. */
    }
}
