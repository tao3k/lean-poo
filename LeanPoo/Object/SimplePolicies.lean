import LeanPoo.Object.MethodCombination

/-! Typed policies for Appendix B's alternative method combinations.
Methods arrive most-specific-first. Empty extrema and last-result groups
return `none`; no artificial extremum or last result is invented.
`append` is persistent list concatenation, not destructive CLOS `nconc`. -/
namespace LeanPoo.Object.MethodCombination.SimplePolicy
variable {Item Acc Result : Type}

def sum (α : Type) [OfNat α 0] [Add α] : SimplePolicy α α α where
  stop := fun _ => false
  empty := 0
  first := id
  step := fun value accumulated => accumulated + value
  finish := id

/-- Collect in dispatch order; reverse once at the boundary. -/
def collect (α : Type) : SimplePolicy α (List α) (List α) where
  stop := fun _ => false
  empty := []
  first := fun value => [value]
  step := List.cons
  finish := List.reverse

def append (α : Type) : SimplePolicy (List α) (List α) (List α) where
  stop := fun _ => false
  empty := []
  first := id
  step := fun value accumulated => accumulated ++ value
  finish := id

def all : SimplePolicy Bool Bool Bool where
  stop := not
  empty := true
  first := id
  step := fun value accumulated => accumulated && value
  finish := id

def any : SimplePolicy Bool Bool Bool where
  stop := id
  empty := false
  first := id
  step := fun value accumulated => accumulated || value
  finish := id

/-- Execute every method and retain the last result (`progn` style). -/
def last (α : Type) : SimplePolicy α (Option α) (Option α) where
  stop := fun _ => false
  empty := none
  first := some
  step := fun value _ => some value
  finish := id

def maximum (α : Type) [Max α] : SimplePolicy α (Option α) (Option α) where
  stop := fun _ => false
  empty := none
  first := some
  step := fun value accumulated => some (accumulated.map (max · value) |>.getD value)
  finish := id

def minimum (α : Type) [Min α] : SimplePolicy α (Option α) (Option α) where
  stop := fun _ => false
  empty := none
  first := some
  step := fun value accumulated => some (accumulated.map (min · value) |>.getD value)
  finish := id

/-- Pure ordered reference for policy reduction, including short circuiting. -/
def reduceTail (policy : SimplePolicy Item Acc Result) : Acc → List Item → Acc
  | acc, [] => acc
  | acc, value :: rest =>
    if policy.stop acc then acc else reduceTail policy (policy.step value acc) rest

def reduce (policy : SimplePolicy Item Acc Result) (values : List Item) : Result :=
  policy.finish (match values with
    | [] => policy.empty
    | value :: rest => reduceTail policy (policy.first value) rest)

end LeanPoo.Object.MethodCombination.SimplePolicy
