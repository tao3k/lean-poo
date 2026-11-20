// SPDX-License-Identifier: Apache-2.0 AND LGPL-2.1-or-later
package ReadSweepSizing {
    private import ScalarValues::*;
    requirement def SizingBoundary {
        attribute liveNativeQualification : Boolean;
        attribute foreignDelegateRunsOnce : Boolean;
        attribute reauthenticateAfterForeignSizing : Boolean;
        attribute originalFirstRefusal : Boolean;
        attribute independentReturnCheck : Boolean;
        require constraint { liveNativeQualification and foreignDelegateRunsOnce
            and reauthenticateAfterForeignSizing and originalFirstRefusal
            and independentReturnCheck }
        doc /* Preflight is reusable only across the qualified native sizing
               interval. Interface sizing is an effect boundary otherwise. */
    }
}
