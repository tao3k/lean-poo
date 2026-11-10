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
}
