import LeanPoo.Functional.FeedbackCache

/-! Complete equations share the existing generalized lens compiler and bounded
feedback closure. Internal reads use one cooked self; external inputs are fixed. -/
namespace LeanPoo.Prototype.Generalized
variable {Key Raw Cooked Method : Type} [DecidableEq Key]

/-- Compile one complete component with its selected lens and the common cooked
self. External reads are already closed predecessors, never partial cache slots. -/
def componentFragment (focus : Key → MonoLens Raw Method)
    (equation : Key → (Key → Method) → Method) (selfRef : Key → Cooked → Method)
    (external : Key → Method) (members : List Key) (key : Key) : Fragment Raw Cooked :=
  ⟨Method,Unit,focus key,fun _ self _ =>
    equation key (fun dep => if dep ∈ members then selfRef dep self.get else external dep),()⟩

/-- Build all members of a discovered group with the existing fragment protocol. -/
def componentParts (focus : Key → MonoLens Raw Method)
    (equation : Key → (Key → Method) → Method) (selfRef : Key → Cooked → Method)
    (external : Key → Method) (members : List Key) : List (Fragment Raw Cooked) :=
  members.map (componentFragment focus equation selfRef external members)

/-- Every selected component occurs in the exact family checked by group closure. -/
theorem componentParts_member (focus : Key → MonoLens Raw Method)
    (equation : Key → (Key → Method) → Method) (selfRef : Key → Cooked → Method)
    (external : Key → Method) (members : List Key) (key : Key) (member : key ∈ members) :
    componentFragment focus equation selfRef external members key ∈
      componentParts focus equation selfRef external members := List.mem_map.mpr ⟨key,member,rfl⟩

/-- Any returned actual group certifies EACH selected complete equation. This
reuses its existing residual proof and introduces no new equality oracle. -/
theorem componentGroup_equation (focus : Key → MonoLens Raw Method)
    (equation : Key → (Key → Method) → Method) (selfRef : Key → Cooked → Method)
    (external : Key → Method) (cook : Raw → Cooked) (base : Raw)
    (group : Functional.FeedbackCache.Group (componentParts focus equation selfRef external) cook base)
    (key : Key) (member : key ∈ group.input) :
    (componentFragment focus equation selfRef external group.input key).feedbackEquation cook base
      group.result.closed.raw :=
  group.equations _ (componentParts_member focus equation selfRef external group.input key member)
end LeanPoo.Prototype.Generalized
