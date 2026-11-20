package FixedFieldLayout {
    private import ScalarValues::*;
    requirement def CurrentOffsetAdmission {
        attribute sameClass : Boolean;
        attribute sameFieldOffset : Boolean;
        attribute payloadCurrent : Boolean;
        require constraint { sameClass and sameFieldOffset and payloadCurrent }
        doc /* Class identity does not freeze a mutable runtime field map.
               Check the current offset before using the pinned accessor.
               A field move refuses before metadata method dispatch. */
    }
    requirement def IndependentReturn {
        attribute entryAdmitted : Boolean;
        attribute returnAdmitted : Boolean;
        require constraint { entryAdmitted and returnAdmitted }
        doc /* A callback may change the layout after entry. The entry
               result never certifies that later layout or slot state. */
    }
    requirement def SignedRecordFields {
        attribute finalConstructorFieldsOwnTheSignature : Boolean;
        attribute issuerAndWalkerUseSameFields : Boolean;
        attribute symbolicMapCannotRedirectParents : Boolean;
        attribute publicStructuralInspectorsStillCopy : Boolean;
        require constraint {
            finalConstructorFieldsOwnTheSignature and issuerAndWalkerUseSameFields and
            symbolicMapCannotRedirectParents and publicStructuralInspectorsStillCopy
        }
        doc /* This is a different authority from reflective HashTable routes.
               A signed record's fields come from its declaring module's
               generated operations; a mutable inspection map is not its DAG. */
    }
    requirement def IssuerFactoryFieldBinding {
        attribute reuseDeclaringModuleOperations : Boolean;
        attribute avoidRecaptureAfterDisplayEdits : Boolean;
        attribute keepWriterAndRawFieldsInternal : Boolean;
        require constraint {
            reuseDeclaringModuleOperations and avoidRecaptureAfterDisplayEdits and
            keepWriterAndRawFieldsInternal
        }
    }
}
