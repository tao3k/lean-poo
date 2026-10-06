import LeanPoo.Prototype.MetaPrototype

namespace LeanPoo.Prototype.MetaPrototype

/-- Prepared metadata/functions whose retained caches were compared with C3
on this registry's graph. The constructor is private; reuse across base values
requires no second graph traversal. Function/supers/order are frozen together. This is checked data, not a kernel C3 proof. -/
structure Prepared (α : Type) where private mk ::
  order : List String
  private metadata : Meta α
  private layers : List (Layer α)
  private parents : List String
  private own : Layer α

private def require (value : Option α) (message : String) : Except String α :=
  match value with | some item => .ok item | none => .error message

/-- Verify every retained parent cache against the declared registry graph.
The paper's special base has an empty cache; ordinary objects must retain the
exact C3 order. Unknown names/cycles/duplicates and altered caches are refused. -/
def prepareChecked (name : String) (metadata : Meta α) (registry : Registry α) :
    Except String (Prepared α) := do
  let parents ← require (metadata.value.lookup .supers) "missing metadata supers"
  let rows ← registry.mapM fun (parent,object) => do return (parent, ← supers object)
  let graph := (name,parents) :: rows
  let names := name :: registry.map Prod.fst
  let orders ← (C3.linearizeMany graph names).mapError (fun _ => "invalid C3 registry graph")
  let some order := orders.head? | throw "missing root order"
  for ((parent,object),expected) in registry.zip orders.tail do
    let retained ← precedence object
    let wanted := if object.metadata.isNone then [] else expected
    unless retained == wanted do throw s!"retained precedence differs from C3: {parent}"
  let own ← require (metadata.value.lookup .function) "missing metadata function"
  let inherited ← order.tail.mapM fun parent => do
    let some entry := registry.find? (fun entry => entry.1 == parent) | throw s!"unknown super: {parent}"
    function entry.2
  return ⟨order,metadata,own :: inherited,parents,own⟩

/-- Instantiate an admitted registry plan repeatedly with different base data. -/
unsafe def Prepared.instantiate (prepared : Prepared α) (base : α) : Instance α :=
  let combined := DelayedProto.composeAll prepared.layers
  let fields := DelayedProto.compose
    (Object.recordSlotGen .function (fun _ _ => some prepared.own))
    (DelayedProto.compose (Object.recordSlotGen .supers (fun _ _ => some prepared.parents))
      (Object.recordSlotGen .precedence (fun _ _ => some prepared.order)))
  let cached := prepared.metadata.extend fields
  { value := DelayedProto.instantiate combined (Thunk.pure base)
    metadata := some cached
    baseFunction := fun _ parent => parent.get }

unsafe def instantiateChecked (name : String) (metadata : Meta α) (registry : Registry α)
    (base : α) : Except String (Instance α) := do
  return (← prepareChecked name metadata registry).instantiate base

end LeanPoo.Prototype.MetaPrototype
