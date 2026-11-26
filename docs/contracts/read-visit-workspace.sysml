// SPDX-License-Identifier: Apache-2.0 AND LGPL-2.1-or-later
package ReadVisitWorkspace {
    private import ScalarValues::*;
    requirement def FreshTraversal {
        attribute freshGeneration : Boolean;
        attribute sameIssuedRecordOrder : Boolean;
        attribute sameFirstRefusal : Boolean;
        attribute sameReceiverIndex : Boolean;
        require constraint { freshGeneration and sameIssuedRecordOrder
            and sameFirstRefusal and sameReceiverIndex }
        doc /* Reuse physical traversal storage, never a validation verdict.
               Every new binding logically starts with an empty visited set. */
    }
    requirement def ScopeAndEffects {
        attribute creatorThreadOnly : Boolean;
        attribute retiredOnExit : Boolean;
        attribute observerFallback : Boolean;
        attribute independentReturnCheck : Boolean;
        require constraint { creatorThreadOnly and retiredOnExit
            and observerFallback and independentReturnCheck }
        doc /* Native capture owns the workspace. Bound projections do not.
               Authored callbacks retain their independent live checks. */
    }
}
