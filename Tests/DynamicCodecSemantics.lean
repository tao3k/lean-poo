import LeanPoo.Prototype.DynamicCodecSemantics

open LeanPoo.Prototype.Dynamic
namespace LeanPoo.Tests.DynamicCodecSemantics

/-- Universal reconstruction includes arbitrary duplicate ordered entries. -/
example (entries : List (String × Value)) :
    Value.decodeJson ((Value.object entries).wireDepth) (Value.object entries).encodeJson =
      .ok (.object entries) :=
  Value.decodeJson_encodeJson _ _ (Nat.le_refl _)

/-- The exact admitted value and proof re-enter the same registry wire gate. -/
example (descriptor : Descriptor) (registry : Registry) (value : Value) (fuel : Nat)
    (admitted : Admitted registry descriptor.contract)
    (checked : descriptor.validate registry fuel value = .ok admitted)
    (bound : value.wireDepth ≤ fuel) :
    descriptor.encodeJson registry fuel value = .ok value.encodeJson ∧
      descriptor.decodeJson registry fuel value.encodeJson = .ok admitted :=
  descriptor.json_roundTrip registry fuel value admitted checked bound

private def checks : IO Unit := do
  let value : Value := .dictionary [(.integer (-123456789012345678901234567890),
    .object [("λ", .list [.unit, .text "类型"]), ("λ", .boolean false)])]
  let decoded ← IO.ofExcept ((Value.decodeJson value.wireDepth value.encodeJson).mapError reprStr)
  unless decoded == value do throw (IO.userError "structural inversion control")
  IO.println "DYNAMIC-CODEC-SEMANTICS-OK structuralJson=universal inverseBudget=explicit admissionProof=preserved"

#eval checks
#print axioms Value.decodeJson_encodeJson
#print axioms Descriptor.json_roundTrip
end LeanPoo.Tests.DynamicCodecSemantics
