import LeanPoo.Object.MultimethodCombination
import LeanPoo.Object.SimpleCombinationSemantics

/-! Alternative combinations over the same ordered pricing fragments.
Warm dispatch rechecks amount predicates; different result policies retain
ordered effects, while approval/eligibility short circuit their own groups. -/
namespace LeanPoo.Examples.PolicyDispatch
open Object Object.MethodCombination
variable {Acc Result : Type}

structure Request where
  account : String
  channel : String
  amount : Nat
abbrev Action := EStateM String (List String)
def shape (request : Request) := [[request.account, "Account"], [request.channel, "Channel"]]
def path (account channel : String) : List Specializer := [.prototype account, .prototype channel]
def item (name : String) (value : Nat) : SimpleContribution Request Action Nat Result :=
  .item fun request => do
    modify (· ++ [name])
    if request.amount == 999 && name == "base" then throw "unpriced"
    return value

def pricing (policy : SimplePolicy Nat Acc Result) := do
  let initial := Multimethod.simple (M := Action) 2 shape policy
  let base ← initial.register (path "Account" "Channel") (item "base" 2)
  let member ← base.register (path "Member" "Channel") (item "member" 5)
  member.registerWhen (path "Member" "Card") (·.amount > 100) (item "risk" 3)

def prices (policy : SimplePolicy Nat Acc Result) : Except MultimethodError (List (EStateM.Result String (List String) Result)) := do
  let generic ← pricing policy
  let (first, warm) ← generic.call ⟨"Member", "Card", 10⟩
  let (second, warm) ← warm.call ⟨"Member", "Card", 150⟩
  let (failed, _) ← warm.call ⟨"Member", "Card", 999⟩
  return [first.run [], second.run [], failed.run []]

#guard (match prices (SimplePolicy.sum Nat) with
  | .ok [.ok 7 ["member", "base"], .ok 10 ["risk", "member", "base"], .error "unpriced" ["risk", "member", "base"]] => true
  | _ => false)
#guard (match prices (SimplePolicy.collect Nat) with
  | .ok [.ok [5,2] _, .ok [3,5,2] _, .error "unpriced" _] => true | _ => false)
#guard (match prices (SimplePolicy.maximum Nat) with
  | .ok [.ok (some 5) _, .ok (some 5) _, .error "unpriced" _] => true | _ => false)
#guard (match prices (SimplePolicy.minimum Nat) with
  | .ok [.ok (some 2) _, .ok (some 2) _, .error "unpriced" _] => true | _ => false)
#guard (match prices (SimplePolicy.last Nat) with
  | .ok [.ok (some 2) _, .ok (some 2) _, .error "unpriced" _] => true | _ => false)

def decision (policy : SimplePolicy Bool Bool Bool) (first : Bool) : Action Bool :=
  simpleEffective policy {
    items := [
    (fun _ => do modify (· ++ ["local"]); return first),
    (fun _ => do modify (· ++ ["remote"]); throw "remote unavailable")],
    around := [fun next _ => do
      modify (· ++ ["enter"])
      let value ← next ()
      modify (· ++ ["exit"])
      return value]} ()

#guard (match (decision SimplePolicy.all false).run [] with
  | .ok false ["enter", "local", "exit"] => true | _ => false)
#guard (match (decision SimplePolicy.any true).run [] with
  | .ok true ["enter", "local", "exit"] => true | _ => false)
#guard (match (decision SimplePolicy.all true).run [] with
  | .error "remote unavailable" ["enter", "local", "remote"] => true | _ => false)

-- Ordered collected contributions are exactly the input, for every list.
theorem collected_in_order (values : List Nat) :
    simpleEffective (SimplePolicy.collect Nat)
      { items := values.map (fun value (_ : Unit) => (pure value : Id Nat)) } () = values := by
  rw [simpleEffective_pure, SimplePolicy.collect_order]

#print axioms simpleEffective_reference
#print axioms runSimpleTail_iff
#print axioms collected_in_order
end LeanPoo.Examples.PolicyDispatch
