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
}
