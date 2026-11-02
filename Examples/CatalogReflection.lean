import LeanPoo.Object.CatalogReflection
import LeanPoo.Object.MethodCompilation

/-! One retained method program observes current complete metadata on each call.
Gerbil regressions additionally exercise actual brace aliases, lexical receivers,
source invalidation and callback effects; these examples do not prove expansion. -/
namespace LeanPoo.Examples.DeclaredMethods
open LeanPoo.Prototype.DescriptorReflection LeanPoo.Object.MethodCombination

/-- The effective catalog already selected the most-specific declarations. -/
def serviceCatalog : List (String × Nat) := [("charge", 10), ("audit", 0)]

/-- Metadata approval is supplied per invocation, not captured as an old result. -/
def inspectedCharge (visible : (String × Nat) → Except String Bool) :
    SubMethod Nat (Except String) Nat := fun _ units =>
  catalogRead serviceCatalog visible "charge" (fun rate => .ok (rate * units))

/-- An unrelated suffix's metadata failure precedes the requested method read. -/
example : catalogRead serviceCatalog
    (fun entry => if entry.1 == "audit" then .error "approval revoked" else .ok true)
    "charge" (fun rate => .ok (rate * 2)) = .error "approval revoked" := rfl

/-- The identical compiled method shape accepts a fresh visible catalog. -/
example : composeContinuations
    [methodContinuation (inspectedCharge (fun _ => .ok true))]
    (fun _ => .error "no primary") 2 = .ok 20 := rfl

/-- Hidden most-specific metadata refuses before execution; no ancestor is added. -/
example : composeContinuations
    [methodContinuation (inspectedCharge (fun entry => .ok (entry.1 != "charge")))]
    (fun _ => .error "no primary") 2 = .error "slot is hidden or undeclared" := rfl

/-- Restoring current approval retries through the same retained code constructor. -/
example (visible : (String × Nat) → Except String Bool) (units : Nat) :
    composeContinuations [methodContinuation (inspectedCharge visible)]
      (fun _ => .error "no primary") units =
    catalogRead serviceCatalog visible "charge" (fun rate => .ok (rate * units)) := rfl

#print axioms inspectCatalog_suffix_error
#print axioms catalogRead_metadata_error
#print axioms catalogRead_selected
#print axioms catalogRead_absent
end LeanPoo.Examples.DeclaredMethods
