import LeanPoo.Object.SimpleCombinationSemantics

/-! Independent loops compare complete effects and failures. The oracle does
not use policy reduction, the combiner, or the operational derivation. -/
namespace LeanPoo.Tests.AlternativeCombination
open Object.MethodCombination
variable {Item Acc Result : Type}
abbrev Action := EStateM String (List Nat)
structure Summary where
  result : Except String String
  trace : List Nat
  deriving Repr
instance : BEq Summary where
  beq left right := (match left.result, right.result with
    | .ok a, .ok b => a == b
    | .error a, .error b => a == b
    | _, _ => false) && left.trace == right.trace
def summarize (showValue : α → String) : EStateM.Result String (List Nat) α → Summary
  | .ok value trace => ⟨.ok (showValue value), trace⟩
  | .error error trace => ⟨.error error, trace⟩

def actual (policy : SimplePolicy Item Acc Result) (convert : Nat → Item)
    (showValue : Result → String) (values : List Nat) (failure : Nat) : Summary :=
  let methods := values.zipIdx |>.map fun (value, index) (_ : Unit) => do
    modify (· ++ [index])
    if index == failure then throw "failed"
    return convert value
  let around : SubMethod Unit Action Result := fun next _ => do
    modify (· ++ [1000])
    let result ← next ()
    modify (· ++ [1001])
    return result
  summarize showValue ((simpleEffective policy { items := methods, around := [around] } ()).run [])

def output (kind : Nat) (values : List Nat) : String := Id.run do
  match kind with
  | 0 =>
    let mut total := 0
    for value in values do total := total+value
    return toString total
  | 1 => return reprStr values
  | 2 =>
    let mut items := []
    for value in values do items := items ++ [value, value+10]
    return reprStr items
  | 3 | 4 =>
    let mut best : Option Nat := none
    for value in values do
      best := some (match best with | none => value | some old => if kind == 3 then max old value else min old value)
    return reprStr best
  | 5 => return reprStr values.getLast?
  | 6 => return toString (values.all (· > 0))
  | _ => return toString (values.any (· > 0))

def expected (kind : Nat) (values : List Nat) (failure : Nat) : Summary := Id.run do
  let mut retained := []
  let mut trace := [1000]
  let mut index := 0
  for value in values do
    trace := trace ++ [index]
    if index == failure then return ⟨.error "failed", trace⟩
    retained := retained ++ [value]
    index := index+1
    if (kind == 6 && value == 0) || (kind == 7 && value > 0) then break
  return ⟨.ok (output kind retained), trace ++ [1001]⟩

def check (values : List Nat) (failure : Nat) : Bool :=
  actual (SimplePolicy.sum Nat) id toString values failure == expected 0 values failure &&
  actual (SimplePolicy.collect Nat) id reprStr values failure == expected 1 values failure &&
  actual (SimplePolicy.append Nat) (fun n => [n,n+10]) reprStr values failure == expected 2 values failure &&
  actual (SimplePolicy.maximum Nat) id reprStr values failure == expected 3 values failure &&
  actual (SimplePolicy.minimum Nat) id reprStr values failure == expected 4 values failure &&
  actual (SimplePolicy.last Nat) id reprStr values failure == expected 5 values failure &&
  actual SimplePolicy.all (· > 0) toString values failure == expected 6 values failure &&
  actual SimplePolicy.any (· > 0) toString values failure == expected 7 values failure

def sequences : Nat → List (List Nat)
  | 0 => [[]]
  | n+1 => [[]] ++ (sequences n).flatMap (fun rest => [0,1,2,3].map (· :: rest))
def cases := (sequences 3).flatMap (fun values => (List.range 5).map (values, ·))
#guard cases.length == 425
#guard cases.all (fun (values, failure) => check values failure)

-- A successful around shortcut leaves every item unexecuted.
partial def omitted : Action Bool := fun state => omitted state
def bypass : Action Bool := simpleEffective SimplePolicy.all
  { items := [fun (_ : Unit) => omitted], around := [fun _ _ => pure false] } ()
#guard (match bypass.run [] with | .ok false [] => true | _ => false)
-- Short circuiting also leaves a genuinely divergent suffix untouched.
#guard (match (simpleEffective SimplePolicy.any
    { items := [(fun (_ : Unit) => pure true), (fun _ => omitted)] } ()).run [] with
  | .ok true [] => true | _ => false)

#print axioms simpleEffective_reference
#print axioms runSimpleTail_iff
#print axioms simpleEffective_first_error
#print axioms simpleEffective_tail
#print axioms SimplePolicy.maximum_nat_bounds
#print axioms SimplePolicy.minimum_nat_bounds
#print axioms SimplePolicy.append_flatten
#print axioms SimplePolicy.maximum_values
#print axioms SimplePolicy.minimum_values
#print axioms SimplePolicy.last_values
#print axioms SimplePolicy.sum_nat
#print axioms SimplePolicy.collect_order
#print axioms SimplePolicy.all_values
#print axioms SimplePolicy.any_values
end LeanPoo.Tests.AlternativeCombination
