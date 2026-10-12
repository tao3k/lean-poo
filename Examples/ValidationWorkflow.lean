import LeanPoo.Functional.Assembly

/-! Validate independent readings at a shared limit. A context selects strict
validation or explicit clamping; a report retains all per-reading errors. -/
namespace LeanPoo.Examples.ValidationWorkflow
open Functional

structure Limits where
  maximum : Nat
  clamp : Bool

abbrev Checked (limits : Limits) := {value : Nat // value ≤ limits.maximum}

def validate (reading : Nat) : Factory Limits (fun limits => Except String (Checked limits)) :=
  fun limits => if allowed : reading ≤ limits.maximum then .ok ⟨reading, allowed⟩
    else .error s!"above limit: {reading}"

def policy (reading : Nat) : Factory Limits (fun limits => Except String (Checked limits)) :=
  Factory.choose (·.clamp)
    (Factory.recover (validate reading) fun _ limits => .ok ⟨limits.maximum, by omega⟩)
    (validate reading)

def readings := [3, 8, 13].map policy
def checked := Factory.sequence readings

structure Report where
  accepted : List Nat := []
  errors : List String := []
  deriving Repr, BEq

def summarize : Factory Limits (fun _ => Report) :=
  Factory.fold (fun _ report result => match result with
    | .ok value => {report with accepted := report.accepted ++ [value.val]}
    | .error message => {report with errors := report.errors ++ [message]})
    (fun _ => {}) readings

#guard summarize ⟨10, false⟩ == ⟨[3, 8], ["above limit: 13"]⟩
#guard summarize ⟨10, true⟩ == ⟨[3, 8, 10], []⟩
#guard summarize ⟨5, false⟩ == ⟨[3], ["above limit: 8", "above limit: 13"]⟩
#guard ((checked ⟨10, true⟩).map fun result => result.toOption.map (·.val)) ==
  [some 3, some 8, some 10]

#eval do
  for limits in [Limits.mk 10 false, ⟨10, true⟩, ⟨5, false⟩] do
    IO.println s!"limit={limits.maximum}, clamp={limits.clamp}: {repr (summarize limits)}"

end LeanPoo.Examples.ValidationWorkflow
