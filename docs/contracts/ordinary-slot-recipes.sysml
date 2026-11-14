package OrdinarySlotRecipes {
    private import ScalarValues::*;
    requirement def ExistingChronologicalBinding {
        doc /* RecipeRows.install_equals_compile reuses the original C4
               schedule and all four generated forms. Bind final self and
               retain delayed sup. Preserve duplicates and missing keys. */
    }
    requirement def CompilerOwnedSelfSource {
        doc /* Initially admit only generated parentless default-free self
               forms. Preserve lexical aliases, actual constructor birth and
               empty compact defaults. Reuse the existing source, ordinal
               index and method table; do not evaluate a business body. */
    }
    requirement def EffectAndExposureBoundaries {
        doc /* Derive source ownership from existing birth/exposure checks.
               Changed constructors, hooks and unknown input remain ordinary.
               Preserve full capture before author hooks and original errors.
               Algebra alone does not certify VM correspondence or capacity. */
    }
    requirement def ActualFactoryAndCostGate {
        doc /* The first self adapter regressed small complete constructions
               and was withdrawn. Core runtime factories use make-object
               directly; a macro-only speedup is not Module acceptance.
               No source, consumer pin or budget promotion follows. */
    }
    requirement def BorrowedInheritedTail {
        doc /* newest_equals_original and newest_append preserve newer raw
               prefixes above captured parent methods. Only generated
               independent forms discard older tails. Bind final child self.
               Borrow through the existing source fences and ordinal index;
               public iteration still exposes raw records. Publish only the
               complete method table and retain raw refusal/effect order. */
    }
}
