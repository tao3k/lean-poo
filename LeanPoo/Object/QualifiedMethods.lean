import LeanPoo.Object.Schema

/-!
POOF section 9 user-defined method combinations. Lean's dependent key family
types each qualifier's method body; the existing ordered `Entry` representation
stores its C4-accumulated contributions. A user-defined Lean function chooses
how and when to execute the qualified groups.
-/

namespace LeanPoo.Object

universe u v w

/-- Each qualifier selects the type of its method bodies. Its list is ordered
most-specific-first by the same C4 slot composition used by ordinary fields. -/
structure QualifiedMethods (Qualifier : Type u)
    (Body : Qualifier → Type v) where
  groups : List (Entry Qualifier (fun qualifier => List (Body qualifier))) := []

def QualifiedMethods.lookup {Qualifier : Type u}
    {Body : Qualifier → Type v}
    (methods : QualifiedMethods Qualifier Body) (qualifier : Qualifier) :
    List (Body qualifier) :=
  (Entry.lookup methods.groups qualifier).getD []

/-- A new contribution precedes inherited methods of the same qualifier;
other qualifier groups keep their first declaration position. -/
def QualifiedMethods.prepend {Qualifier : Type u}
    {Body : Qualifier → Type v} [DecidableEq Qualifier]
    (methods : QualifiedMethods Qualifier Body) (qualifier : Qualifier)
    (body : Body qualifier) : QualifiedMethods Qualifier Body :=
  { groups := Entry.replace methods.groups qualifier
      (body :: methods.lookup qualifier) }

/-- Interpret an ordered sequence of qualified contributions. Earlier
contributions remain ahead of later ones within each qualifier. -/
def QualifiedMethods.prependAll {Qualifier : Type u}
    {Body : Qualifier → Type v} [DecidableEq Qualifier]
    (contributions : List (Sigma Body))
    (methods : QualifiedMethods Qualifier Body) :
    QualifiedMethods Qualifier Body :=
  contributions.foldr
    (fun contribution accumulated =>
      accumulated.prepend contribution.1 contribution.2) methods

/-- A contribution batch composes in the same order as two successive
inheritance layers. -/
theorem QualifiedMethods.prependAll_append {Qualifier : Type u}
    {Body : Qualifier → Type v} [DecidableEq Qualifier]
    (front back : List (Sigma Body))
    (methods : QualifiedMethods Qualifier Body) :
    QualifiedMethods.prependAll (front ++ back) methods =
      QualifiedMethods.prependAll front
        (QualifiedMethods.prependAll back methods) := by
  simp [QualifiedMethods.prependAll]

/-- Install heterogeneous qualified methods from one prototype as an
ordinary delayed slot specification. Their source order is preserved. -/
def QualifiedMethods.specifications {Self : Type w}
    {Qualifier : Type u} {Body : Qualifier → Type v}
    [DecidableEq Qualifier] (contributions : List (Sigma Body)) :
    Prototype.SlotSpec Self (Option (QualifiedMethods Qualifier Body)) :=
  .computed fun _ inherited =>
    some <| QualifiedMethods.prependAll contributions
      ((inherited ()).getD {})

/-- A single contribution is still a first-class specification. -/
def QualifiedMethods.specification {Self : Type w}
    {Qualifier : Type u} {Body : Qualifier → Type v}
    [DecidableEq Qualifier] (qualifier : Qualifier) (body : Body qualifier) :
    Prototype.SlotSpec Self (Option (QualifiedMethods Qualifier Body)) :=
  QualifiedMethods.specifications [⟨qualifier, body⟩]

theorem QualifiedMethods.specification_eval {Self : Type w}
    {Qualifier : Type u} {Body : Qualifier → Type v}
    [DecidableEq Qualifier] (qualifier : Qualifier) (body : Body qualifier)
    (self : Self)
    (inherited : Prototype.Next
      (Option (QualifiedMethods Qualifier Body))) :
    (QualifiedMethods.specification qualifier body).eval self inherited =
      some (((inherited ()).getD {}).prepend qualifier body) := rfl

end LeanPoo.Object
