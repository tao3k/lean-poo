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
    requirement def InternalReferenceDomain {
        attribute registeredFieldsMatch : Boolean;
        attribute sourceReceiver : Boolean;
        attribute sourcePurpose : Boolean;
        require constraint {
            registeredFieldsMatch and sourceReceiver and sourcePurpose
        }
        doc /* Reference.sourceControl uses the existing issuer before control
               extraction. Copied or changed records do not dispatch. Internal
               source/map references are not business reads. No administrative
               POO object, second authority or result cache is introduced.
               Identity does not replace live epoch checks across callbacks.
               Gerbil constructor/layout correspondence remains a native gate. */
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
    requirement def SameCallMapFrame {
        attribute liveLayoutChecked : Boolean;
        attribute issuerAndRouteChecked : Boolean;
        attribute canonicalFieldsChecked : Boolean;
        require constraint {
            liveLayoutChecked and issuerAndRouteChecked and canonicalFieldsChecked
        }
        doc /* Reference.MapFrame shares repeated layout decisions only in one
               fixed read-only interval with no intervening metadata writes.
               Keep first-refusal order and false owner probes. The private
               marker is not stored or exported. Standalone calls and checks
               after author effects obtain a fresh live layout decision.
               This is not a proof of concurrent writer synchronization. */
    }
    requirement def GeneratedThunkInstallation {
        doc /* After canonical generated-source admission, chronological direct
               installation equals ordinary independent-thunk compilation at
               every key, including duplicate and missing keys. Preserve the
               actual functions, ordinary C4 and the sole method/value stores.
               Parents, hooks, defaults, declarations, overrides, unknown or
               exposed sources retain full preparation. No body is evaluated. */
    }
    requirement def ClosedNativeInstallation {
        attribute standardWriterCurrent : Boolean;
        attribute exactOwnerView : Boolean;
        attribute sourceGateHeld : Boolean;
        attribute noAuthorCall : Boolean;
        require constraint {
            standardWriterCurrent and exactOwnerView and sourceGateHeld and noAuthorCall
        }
        doc /* ClosedInstallation preserves results and errors for the fixed
               index-to-method installation program. Exposure and installation
               serialize on the existing source gate. Exposure first declines;
               installation first retains immutable cuts. General author calls
               still unlock and independently authenticate/admit at return.
               The gate does not certify arbitrary concurrent metadata writes.
               Unknown writers and protocols retain ordinary preparation. */
    }
}
