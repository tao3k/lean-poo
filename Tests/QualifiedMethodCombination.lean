import LeanPoo.Object.QualifiedMethods
import LeanPoo.Object.MethodCombination
import LeanPoo.Object.Memo

namespace LeanPoo.Tests.QualifiedMethodCombination

structure Request where
  quantity : Nat

inductive Phase where
  | normalize
  | authorize
  | execute
  deriving DecidableEq

/-- A phase determines which capabilities its contributions receive. -/
abbrev Body : Phase → Type
  | .normalize => Request → Request
  | .authorize => Request → Except String Unit
  | .execute => Object.MethodCombination.SubMethod
      Request (Except String) Nat

inductive Key where
  | handlers
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable

abbrev Value : Key → Type
  | .handlers => Object.QualifiedMethods Phase Body

def baseExecute : Body .execute :=
  fun _ request => .ok request.quantity

def addOne : Body .normalize :=
  fun request => { request with quantity := request.quantity + 1 }

def checkLimit : Body .authorize :=
  fun request =>
    if request.quantity <= 10 then .ok () else .error "quantity exceeds limit"

def addBonus : Body .execute :=
  fun next _ => do
    return (← next ()) + 100

/-- The combination chooses its own phase order; C4 only orders methods
within each phase. `execute` retains the ordinary next-method chain. -/
def evaluate (methods : Object.QualifiedMethods Phase Body)
    (request : Request) : Except String Nat := do
  let request := (methods.lookup .normalize).foldl
    (fun current normalize => normalize current) request
  for authorize in methods.lookup .authorize do
    authorize request
  Object.MethodCombination.callChain (methods.lookup .execute)
    (fun _ => .error "no executor") request

def base : Object.Declaration Key Value :=
  Object.Declaration.empty |>.withSlot .handlers
    (Object.QualifiedMethods.specification .execute baseExecute)

def normalized : Object.Declaration Key Value :=
  Object.Declaration.empty |>.withSlot .handlers
    (Object.QualifiedMethods.specification .normalize addOne)

def checked : Object.Declaration Key Value :=
  Object.Declaration.empty |>.withSlot .handlers
    (Object.QualifiedMethods.specifications [
      ⟨.authorize, checkLimit⟩,
      ⟨.execute, addBonus⟩])

def result : Except C4.Error
    (List String × Except String Nat × Except String Nat) := do
  let empty : Object.Schema Key Value :=
    { graph := { nodes := [] }, declaration := fun _ => none }
  let root ← LeanPoo.mix empty "Base" [] base
  let left ← LeanPoo.extend root.schema "Normalize" "Base" normalized
  let right ← LeanPoo.extend left.schema "CheckAndBonus" "Base" checked
  let final ← LeanPoo.mix right.schema "Final"
    ["Normalize", "CheckAndBonus"] Object.Declaration.empty
  let methods := (final.memoize.read .handlers).getD {}
  return (final.precedence, evaluate methods ⟨9⟩, evaluate methods ⟨10⟩)

#guard match result with
  | .ok (order, .ok 110, .error "quantity exceeds limit") =>
    order == ["Final", "Normalize", "CheckAndBonus", "Base"]
  | _ => false

end LeanPoo.Tests.QualifiedMethodCombination
