import LeanPoo.Prototype.DynamicDescriptorCompleteness
import LeanPoo.Prototype.DynamicSchema

open LeanPoo.Prototype.Dynamic
namespace LeanPoo.Tests.DynamicDescriptorCompleteness

private def registry : Registry :=
  { descriptors := [("Loop", ⟨"Loop", .named "Loop", []⟩),
      ("Recovering", ⟨"Recovering", .union (.named "Loop") .integer, []⟩)] }

private theorem integers_admitted (value : Int) : Accepted registry (.named "Recovering") (.integer value) :=
  .named rfl (.unionRight .integer)

/-- Recognition covers all these values despite the nonproductive left branch. -/
example (value : Int) : ∃ bound, ∀ fuel, bound ≤ fuel →
    accepts registry fuel (.named "Recovering") (.integer value) = .ok true :=
  accepts_complete (integers_admitted value)

private def checks : IO Unit := do
  for fuel in List.range 101 do
    unless (accepts registry (fuel + 3) (.named "Recovering") (.integer 42)).toOption == some true &&
        (accepts registry (fuel + 3) (.union .integer (.named "Loop")) (.integer 42)).toOption == some true do
      throw (IO.userError "recursive union hid a successful branch")
  unless (accepts registry 20 (.named "Recovering") (.text "no") matches .error .budgetExhausted) &&
      (accepts registry 20 (.union (.named "missing") .integer) (.integer 42)).toOption == some true &&
      (accepts registry 20 (.union (.named "missing") .integer) (.text "no") matches
        .error (.unknownDescriptor "missing")) &&
      (accepts registry 0 .integer (.integer 42) matches .error .budgetExhausted) do
    throw (IO.userError "unresolved union branch became a fabricated refusal")
  let schema : RecordSchema := ⟨"ActualWire", [⟨"x", "Recovering", none, true⟩], true⟩
  let value ← IO.ofExcept ((schema.construct registry 20 [("x", .integer 42)]).mapError reprStr)
  let wire ← IO.ofExcept ((schema.encodeText registry 20 value).mapError reprStr)
  let decoded ← IO.ofExcept ((schema.decodeText registry 20 wire).mapError reprStr)
  unless decoded == value do throw (IO.userError "recursive union/schema wire admission")
  IO.println "DYNAMIC-DESCRIPTOR-COMPLETE-OK finiteMembership=recognized recursiveUnion=branchFair depths=101 schemaWire=connected"

#eval checks
#print axioms accepts_sound
#print axioms accepts_complete
#print axioms accepted_iff_recognized
end LeanPoo.Tests.DynamicDescriptorCompleteness
