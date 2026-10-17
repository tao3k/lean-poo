import LeanPoo.Functional.DeclarativeMetadata
import LeanPoo.Object.SlotReflection

/-! Shared Reader-style nonlocal expansion, followed here by record publication.
Expansion is generic in its entry type; record callbacks emit Slot descriptors.
Catalogs observe metadata without demanding private instance values. Future work. -/
namespace LeanPoo.Functional.DeclarativeMetadata
universe u v
open Prototype.DescriptorReflection
/-- One callback may contribute multiple slots using the same immutable context. -/
abbrev Expansion (Context α : Type) := Context → Except String (List (String × SlotDeclaration α))
/-- Common Reader expansion for record AND non-record entries. Elaborate in
source order; the first failure prevents all later callbacks. -/
def expandForms {Context : Type u} {Entry : Type v}
    (forms : List (Context → Except String (List Entry))) (context : Context) :
    Except String (List Entry) :=
  match forms with
  | [] => .ok []
  | first :: rest => do
    let front ← first context
    let back ← expandForms rest context
    return front ++ back
/-- Suffix expansion is selected only after the first successful fragment. -/
theorem expandForms_cons {Context : Type u} {Entry : Type v}
    (first : Context → Except String (List Entry)) (rest) (context : Context) :
    expandForms (first :: rest) context = (first context).bind (fun front =>
      (expandForms rest context).map (fun back => front ++ back)) := rfl
/-- Unknown/failed declarations cannot be repaired by a later side-effecting form. -/
theorem expandForms_refused {Context : Type u} {Entry : Type v}
    (first : Context → Except String (List Entry)) (rest) (context : Context) (message : String)
    (failed : first context = .error message) :
    expandForms (first :: rest) context = .error message := by simp [expandForms, failed, bind, Except.bind]
/-- Incremental fragment composition is ordinary ordered declaration composition. -/
theorem expandForms_append {Context : Type u} {Entry : Type v}
    (first second : List (Context → Except String (List Entry))) (context : Context) :
    expandForms (first ++ second) context = (expandForms first context).bind (fun front =>
      (expandForms second context).map (fun back => front ++ back)) := by
  induction first with
  | nil =>
      cases result : expandForms second context <;> simp [expandForms, result, bind, Except.bind, Except.map]
  | cons head rest ih =>
    simp only [List.cons_append, expandForms_cons, ih]
    cases head context <;> simp [bind, Except.bind, Except.map]
    case ok front =>
      cases expandForms rest context <;> simp [bind, Except.bind, Except.map]
      case ok back =>
        cases expandForms second context <;> simp [Except.map, List.append_assoc]
/-- Reserved catalog metadata cannot be shadowed by an expanded user declaration. -/
def declarationNamesValid (entries : List (String × SlotDeclaration α)) : Prop :=
  (entries.map Prod.fst).Nodup ∧
    ".public-slots" ∉ entries.map Prod.fst ∧ ".private-slots" ∉ entries.map Prod.fst
instance (entries : List (String × SlotDeclaration α)) : Decidable (declarationNamesValid entries) :=
  inferInstanceAs (Decidable ((entries.map Prod.fst).Nodup ∧
    ".public-slots" ∉ entries.map Prod.fst ∧ ".private-slots" ∉ entries.map Prod.fst))
/-- The complete user declarations and their nonlocal public/private catalogs. -/
structure Catalog (α : Type) where
  entries : List (String × SlotDeclaration α)
  valid : declarationNamesValid entries
/-- Public names come only from visible metadata, never instance values. -/
def Catalog.publicNames (catalog : Catalog α) := (publicSlots catalog.entries).map Prod.fst
/-- Private names are equally inspectable without demanding private values. -/
def Catalog.privateNames (catalog : Catalog α) :=
  (catalog.entries.filter (fun entry => entry.2.hidden)).map Prod.fst
/-- A finalizer can contribute nonlocal declarations but cannot bypass final checks.
Native catalog meta-slots are installed only after this same validation boundary. -/
def elaborate (forms : List (Expansion Context α)) (context : Context)
    (finalize : Context → List (String × SlotDeclaration α) → Except String (List (String × SlotDeclaration α))) :
    Except String (Catalog α) := do
  let expanded ← expandForms forms context
  let entries ← finalize context expanded
  if valid : declarationNamesValid entries then return ⟨entries, valid⟩
  else throw "duplicate or reserved declaration name"
/-- Successful publication comes from the whole ordered expansion and the
finalizer at the SAME context, not a prefix or an earlier context's catalog. -/
theorem elaborate_source (forms : List (Expansion Context α)) (context : Context) (finalize)
    (catalog : Catalog α) (accepted : elaborate forms context finalize = .ok catalog) :
    ∃ expanded, expandForms forms context = .ok expanded ∧ finalize context expanded = .ok catalog.entries := by
  cases expanded : expandForms forms context with
  | error message => simp [elaborate, expanded, bind, Except.bind] at accepted
  | ok front =>
    cases finalized : finalize context front with
    | error message => simp [elaborate, expanded, finalized, bind, Except.bind] at accepted
    | ok entries =>
      by_cases valid : declarationNamesValid entries
      · simp [elaborate, expanded, finalized, valid, bind, Except.bind, pure, Except.pure] at accepted
        subst catalog
        exact ⟨front, rfl, finalized⟩
      · simp [elaborate, expanded, finalized, valid, bind, Except.bind, throw, throwThe] at accepted
/-- Any published catalog has distinct names and preserves the reserved meta slots. -/
theorem Catalog.names_valid (catalog : Catalog α) : declarationNamesValid catalog.entries := catalog.valid
/-- Publication returns the original version on expansion/finalizer/admission refusal. -/
def publishDeclarations (old : Catalog α) (candidate : Except String (Catalog α)) : Catalog α :=
  match candidate with | .error _ => old | .ok next => next
/-- No partial expanded prefix replaces the caller's previously published catalog. -/
theorem publishDeclarations_refused (old : Catalog α) (message : String) :
    publishDeclarations old (.error message) = old := rfl
end LeanPoo.Functional.DeclarativeMetadata
