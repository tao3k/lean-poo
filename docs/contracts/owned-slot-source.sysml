package OwnedSlotSource {
    private import ScalarValues::*;
    requirement def PrivateRecipeStorage {
        attribute generatedStockConstructor : Boolean;
        attribute rawReferencesUnpublished : Boolean;
        attribute privateCaptureUnchanged : Boolean;
        require constraint {
            generatedStockConstructor and rawReferencesUnpublished and privateCaptureUnchanged
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
        doc /* Reserve before reference handoff/callbacks. Success retires the
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
    requirement def CaptureReturnFence {
        attribute sourceMatches : Boolean;
        attribute epochMatches : Boolean;
        attribute stillPrivate : Boolean;
        attribute canonicalBinding : Boolean;
        attribute presentedStampCopied : Boolean;
        require constraint {
            sourceMatches and epochMatches and stillPrivate and canonicalBinding and presentedStampCopied
        }
        doc /* Check independently before and after the author action. Failure
               before entry calls no action; failure at return preserves effects
               and rejects new publication. Preserve the original body exception
               and successful result arity; never hold the source mutex across it.
               Retained immutable cuts do not authorize new publication. */
    }
    requirement def GeneratedThunkInstallation {
        doc /* After canonical generated-source admission, chronological direct
               installation equals ordinary independent-thunk compilation at
               every key, including duplicate and missing keys. Preserve the
               actual functions, ordinary C4 and the sole method/value stores.
               Parents, hooks, defaults, declarations, overrides, unknown or
               exposed sources retain full preparation. No body is evaluated. */
    }
}
