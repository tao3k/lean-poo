package SourceReadWindow {
    private import ScalarValues::*;
    requirement def ClosedObservationWindow {
        attribute closedOwner : Boolean;
        attribute compatibleReadScope : Boolean;
        attribute originalConstructor : Boolean;
        attribute noSourceObserver : Boolean;
        require constraint { closedOwner and compatibleReadScope
            and originalConstructor and noSourceObserver }
        doc /* Metadata and byte queries may share the EXISTING observation
               table only inside one reader check. All checks still execute.
               Query identity retains procedure, arguments and collectors. */
    }
    requirement def ForeignCallback {
        attribute clearedBefore : Boolean;
        attribute freshInside : Boolean;
        attribute clearedAfter : Boolean;
        require constraint { clearedBefore and freshInside and clearedAfter }
        doc /* Unknown location procedures use the existing callback boundary.
               Returning void does not confer purity. No stale enclosing table
               is reinstated after a callback or independent check. */
    }
}
