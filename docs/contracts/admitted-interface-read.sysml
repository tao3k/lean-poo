package AdmittedInterfaceRead {
    private import ScalarValues::*;
    requirement def IdentityConversion {
        attribute sameReceiver : Boolean;
        attribute sameWorld : Boolean;
        attribute noConversionEffects : Boolean;
        attribute stableGuardBodyInterval : Boolean;
        require constraint {
            sameReceiver and sameWorld and noConversionEffects and stableGuardBodyInterval
        }
        doc /* Runtime body retains missing/default/error behavior. Abstract
               equality does not prove native scheduler or primitive correspondence. */
    }
    requirement def EffectBoundary {
        attribute freshEntryAdmission : Boolean;
        attribute freshReturnAdmission : Boolean;
        attribute unsupportedUsesOriginalPath : Boolean;
        require constraint {
            freshEntryAdmission and freshReturnAdmission and unsupportedUsesOriginalPath
        }
    }
}
