// SPDX-License-Identifier: Apache-2.0 AND LGPL-2.1-or-later
package NativeReadCurrentness {
    private import ScalarValues::*;
    requirement def BorrowedView {
        attribute nativeFieldsAdmitted : Boolean;
        attribute validIndexAccess : Boolean;
        attribute sameRevisionAndInstance : Boolean;
        attribute sameReadsIndicesAndCells : Boolean;
        attribute bootstrapUsesLiveAnchor : Boolean;
        attribute originalGuardPrefix : Boolean;
        attribute freshViewAfterEffects : Boolean;
        require constraint { nativeFieldsAdmitted and validIndexAccess
            and sameRevisionAndInstance and sameReadsIndicesAndCells
            and bootstrapUsesLiveAnchor and originalGuardPrefix
            and freshViewAfterEffects }
        doc /* Conditional field-query equivalence. Neither retained views
               across callbacks nor a performance guarantee follows. */
    }
}
