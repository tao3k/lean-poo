import LeanPoo.Object.Subjective
import LeanPoo.Object.Memo

namespace LeanPoo.Tests.SubjectiveDispatch

abbrev Payload : String → Type := fun _ => Nat
abbrev Subject := Object.Plan String Payload
abbrev Item := Object.Plan String Payload

def plans : Except C4.Error (Subject × Subject × Item) := do
  let empty : Object.Schema String Payload :=
    { graph := { nodes := [] }, declaration := fun _ => none }
  let base ← LeanPoo.mix empty "BaseCtx" [] Object.Declaration.empty
  let audit ← LeanPoo.extend base.schema "Audit" "BaseCtx"
    Object.Declaration.empty
  let emergency ← LeanPoo.extend audit.schema "Emergency" "Audit"
    Object.Declaration.empty
  let root ← LeanPoo.mix emergency.schema "BaseItem" []
    Object.Declaration.empty
  let item ← LeanPoo.extend root.schema "Critical" "BaseItem"
    Object.Declaration.empty
  return (base, emergency, item)

/-- The same logical method declarations are indexed differently according
to the subject's lexicographic position. -/
def path (position : Object.Subjective.Position)
    (subject item : Object.Specializer) : List Object.Specializer :=
  match position with
  | .first => [subject, item]
  | .last => [item, subject]

def generic (position : Object.Subjective.Position) :
    Object.Multimethod (Subject × Item) String (List String) :=
  Object.Subjective.generic position 1
    (fun subject => subject.precedence)
    (fun item => [item.precedence])
    (fun methods _ => methods.toList)

def registered (position : Object.Subjective.Position) :
    Except Object.MultimethodError
      (Object.Multimethod (Subject × Item) String (List String)) := do
  let g ← (generic position).register
    (path position (.prototype "BaseCtx") (.prototype "BaseItem"))
    "base"
  let g ← g.register
    (path position (.prototype "Audit") .any) "subject"
  g.register (path position .any (.prototype "Critical")) "item"

/-- A nested ReaderT scope changes the subject without passing it to each
call. StateT keeps candidate caches for both context shapes. -/
def scopedCall : Except String
    (List String × List String × List String × Nat) := do
  let (base, emergency, item) ← plans.mapError
    (fun _ => "invalid C4 graph")
  let g ← (registered .first).mapError (fun _ => "invalid method arity")
  let action : Object.Subjective.Scope Subject Item String
      (List String) (List String × List String × List String) := do
    let initial ← Object.Subjective.call item
    let nested ← Object.Subjective.withSubject emergency
      (Object.Subjective.call item)
    let restored ← Object.Subjective.call item
    return (initial, nested, restored)
  let ((initial, nested, restored), updated) ←
    (Object.Subjective.run action base g).mapError
      (fun _ => "invalid call arity")
  return (initial, nested, restored, updated.cache.size)

#guard match scopedCall with
  | .ok (initial, nested, restored, 2) =>
    initial == ["base", "item"] &&
    nested == ["subject", "base", "item"] &&
    restored == initial
  | _ => false

/-- Moving the implicit subject to the last slot reverses its priority
relative to a method specialized on the explicit item. -/
def lowPriority : Except String (List String × Nat) := do
  let (_, emergency, item) ← plans.mapError
    (fun _ => "invalid C4 graph")
  let g ← (registered .last).mapError (fun _ => "invalid method arity")
  let (methods, updated) ← (g.call (emergency, item)).mapError
    (fun _ => "invalid call arity")
  return (methods, updated.cache.size)

#guard match lowPriority with
  | .ok (["item", "base", "subject"], 1) => true
  | _ => false

end LeanPoo.Tests.SubjectiveDispatch
