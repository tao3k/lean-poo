// SPDX-License-Identifier: Apache-2.0 AND LGPL-2.1-or-later
package FreshReadRoots {
    private import ScalarValues::*;
    requirement def FreshSupportCollection {
        attribute exactRecordIdentity : Boolean;
        attribute beforeParentIssuance : Boolean;
        attribute sameFirstVisitOrder : Boolean;
        attribute originalDeliveries : Boolean;
        attribute sameFailure : Boolean;
        require constraint { exactRecordIdentity and beforeParentIssuance
            and sameFirstVisitOrder and originalDeliveries and sameFailure }
        doc /* The stock authoring Interface producer uses POO's existing
               unique-root collector. It forwards original issued records.
               A new parent is signed normally after construction. Never
               rewrite an already issued read or deduplicate by owner/slot. */
    }
    requirement def IndependentEffectChecks {
        attribute entryAuthenticated : Boolean;
        attribute returnAuthenticated : Boolean;
        attribute noApprovalReuse : Boolean;
        require constraint { entryAuthenticated and returnAuthenticated and noApprovalReuse }
        doc /* Canonical root storage does not certify live source state.
               Gerbil expansion, author callbacks and return keep their
               independent checks. No business scope is constructed. */
    }
}
