import LeanPoo.Functional.Parameters

/-! First-effective declaration selection precedes public visibility.
Host C4 and identifier equality are premises; this is not an expander/runtime proof.
-/
namespace LeanPoo.Prototype.DescriptorReflection

/-- Select current metadata before exposing its payload. A hidden override blocks
all later ancestors even when an ancestor's metadata is public. -/
def publicDeclaration [DecidableEq Name] (name : Name) (entries : List (Name × Bool × Value)) : Option Value :=
  match entries.find? (fun entry => decide (entry.1 = name)) with
  | none => none
  | some entry => if entry.2.1 then none else some entry.2.2

/-- Standard first-key deduplication is transparent to the public lookup policy. -/
theorem publicDeclaration_unique [DecidableEq Name] (name : Name) (entries : List (Name × Bool × Value)) :
    publicDeclaration name (Functional.Parameters.uniqueBindings Prod.fst [] entries) =
      publicDeclaration name entries := by
  simp only [publicDeclaration, Functional.Parameters.find_freshBindings]

/-- Visibility filtering cannot fall through a private child to a public parent. -/
theorem publicDeclaration_hidden [DecidableEq Name] (name : Name) (value : Value)
    (parents : List (Name × Bool × Value)) :
    publicDeclaration name ((name,true,value) :: parents) = none := by
  simp [publicDeclaration]

/-- Visible first metadata retains its exact payload, including legitimate false values. -/
theorem publicDeclaration_first [DecidableEq Name] (name : Name) (value : Value)
    (parents : List (Name × Bool × Value)) :
    publicDeclaration name ((name,false,value) :: parents) = some value := by
  simp [publicDeclaration]
end LeanPoo.Prototype.DescriptorReflection
