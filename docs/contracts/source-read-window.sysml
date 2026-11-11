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
    requirement def QueryWork {
        attribute fixedWorld : Boolean;
        attribute completeQueryIdentity : Boolean;
        require constraint { fixedWorld and completeQueryIdentity }
        doc /* Count actual oracle calls, including failed misses. Repeated
               successful same-key requests in ONE admitted window issue once;
               cached hits issue zero. First refusal stops later requests.
               Independent worlds issue independently. No elapsed-time, Graph
               complexity or Module capacity claim follows from these counts. */
    }
}
