package SourceExposure {
    private import ScalarValues::*;
    requirement def PreserveConstructionPoint {
        doc /* Stock records may be allocated at the original constructor
               point. Keep their addresses private; do not move observable
               constructor calls into reflection or replace record identity. */
    }
    requirement def PrivateFieldFrame {
        attribute sourcePrivate : Boolean;
        attribute rawReferencesUnpublished : Boolean;
        attribute fieldsEqualCapture : Boolean;
        require constraint {
            sourcePrivate implies (rawReferencesUnpublished and fieldsEqualCapture)
        }
        doc /* Derive this from supported allocation, exposure and raw writes.
               A raw writer needs a reference, not a cooperative epoch bump. */
    }
    requirement def IndependentEligibility {
        doc /* Source-storage read authenticity binds the live control value.
               It does not certify that exposure never occurred. Check live
               eligibility on each new capture; old cuts remain immutable. */
    }
    requirement def GeneratedProducerAdmission {
        doc /* Stage the functional producer only for nonempty symbolic keys,
               absent parents/defaults, stock source/reference/object
               construction and no author observation callbacks. Otherwise
               retain original rows and ordinary construction/preparation.
               Preserve the actual compiled constructor route, not an assumed
               method-table dispatch count. Native correspondence and consumer
               gates precede release; this is not a VM-effects theorem. */
    }
    requirement def NameAndValueViews {
        doc /* Name/index metadata and missing lookup publish no raw address.
               A successful value lookup commits exposure before delivering the
               original record. Authenticate the actual view and dispatcher
               through the existing issuer; copied receipts refuse. Explicit
               raw edits retain the full ordinary admission path. */
    }
}
