// SPDX-License-Identifier: Apache-2.0 AND LGPL-2.1-or-later
package LocalSccRegion {
    private import ScalarValues::*;
    requirement def AdmittedEditEnvelope {
        attribute oldEdgesIncluded : Boolean;
        attribute newEdgesIncluded : Boolean;
        attribute changedRowsCoveredByRoots : Boolean;
        attribute fixedOwnerUniverse : Boolean;
        require constraint { oldEdgesIncluded and newEdgesIncluded
            and changedRowsCoveredByRoots and fixedOwnerUniverse }
        doc /* The owned source supplies complete row replacements. The walk
               envelope retains old edges and adds admitted new edges. An
               arbitrary source does not inherit this premise: use full checks. */
    }
    requirement def ExactLocalReplacement {
        attribute localAndColdMembershipAgree : Boolean;
        attribute outsideComponentsPreserved : Boolean;
        attribute oldSnapshotPreserved : Boolean;
        require constraint { localAndColdMembershipAgree
            and outsideComponentsPreserved and oldSnapshotPreserved }
        doc /* Region is forward-from-roots intersect reverse-to-roots in
               the union envelope. Recompute induced successor SCCs there;
               retain predecessor SCC membership elsewhere. Lean proves the
               first two properties. Native persistent-index controls remain
               responsible for snapshot representation and alias isolation. */
    }
}
