import LeanPoo.Functional.View
import LeanPoo.Functional.RegistryPatch

/-! Prepare a broad family once, then retain a named reader and a narrow
monitoring consumer. The monitor works independently of a missing label. -/
namespace LeanPoo.Examples.PreparedViews
open Functional

structure Reading where
  source : String
  sample : Nat
  limit : Nat

inductive Capability where
  | source | sample | alarm
  deriving DecidableEq, Repr

def Value (reading : Reading) : Capability → Type
  | .source => String
  | .sample => {value : Nat // value = reading.sample}
  | .alarm => Bool

def provider : Provider Reading Capability Value
  | .source => some (·.source)
  | .sample => some fun reading => ⟨reading.sample, rfl⟩
  | .alarm => some fun reading => decide (reading.sample > reading.limit)

abbrev requested : List Capability := [.source, .alarm, .sample]
abbrev monitored : List Capability := [.sample, .alarm]

def render (retained : Requirements.Factories Reading Value monitored) :
    Factory Reading (fun _ => String) :=
  Factory.map (fun _ data =>
    s!"{data.1.val}: {cond data.2.1 "alarm" "normal"}") (Requirements.build retained)

def monitor (retained : Requirements.Factories Reading Value requested) :
    Factory Reading (fun _ => String) :=
  let narrow := Requirements.project retained monitored (by
    intro key member
    cases key <;> simp_all [requested, monitored])
  render narrow

def scenario : Except Capability (List (String × String)) := do
  let retained ← Requirements.prepare provider requested
  let name := Requirements.factoryAt (keys := requested) retained .source (by simp [requested])
  let observe := monitor retained
  return [Reading.mk "east" 2 5, ⟨"west", 7, 5⟩].map fun reading =>
    (name reading, observe reading)

#guard scenario.toOption == some [("east", "2: normal"), ("west", "7: alarm")]

def withoutSource := Provider.patchKey provider .source none
#guard (Requirements.prepare withoutSource requested).toOption.isNone
#guard (Requirements.prepare withoutSource monitored).toOption.isSome

def unlabelled : Except Capability String := do
  let retained ← Requirements.prepare withoutSource monitored
  return render retained ⟨"west", 7, 5⟩

#guard unlabelled.toOption == some "7: alarm"

#eval do
  IO.println s!"shared prepared readers: {repr scenario.toOption}"
  IO.println s!"without source label: broad={
    (Requirements.prepare withoutSource requested).toOption.isSome}, monitor={
    repr unlabelled.toOption}"

end LeanPoo.Examples.PreparedViews
