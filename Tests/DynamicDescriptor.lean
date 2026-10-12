import LeanPoo.Prototype.DynamicDescriptorSemantics
import LeanPoo.Prototype.FiniteFix

open LeanPoo.Prototype
open LeanPoo.Prototype.Dynamic
namespace LeanPoo.Tests.DynamicDescriptor

private def natural : Descriptor := ⟨"Natural", .integerRange 0 100000, []⟩
private def fn := Descriptor.functionOf natural natural
private def registry : Registry :=
  { descriptors := [("Natural", natural), ("Descriptor", descriptorType),
      ("Nested", ⟨"Nested", .union .integer (.listOf (.named "Nested")), []⟩)]
    functions := [("increment", fun value => match value with
      | .integer n => .ok (.integer (n + 1))
      | _ => .error (.functionError "integer required")),
      ("bad-result", fun _ => .ok (.text "wrong")),
      ("type-constructor", fun _ => .ok (.descriptor "Natural"))] }

#guard (fn.call registry 10 (.function "increment") (.integer 41)).toOption == some (.integer 42)
#guard fn.call registry 10 (.function "increment") (.integer (-1)) matches .error (.argumentRejected _)
#guard fn.call registry 10 (.function "bad-result") (.integer 0) matches .error (.resultRejected _)
#guard fn.accepts registry 10 (.integer 1) matches .ok false
#guard fn.accepts registry 10 (.function "missing") matches .ok false
#guard fn.call registry 10 (.function "missing") (.integer 1) matches .error (.unknownFunction _)
#guard descriptorType.accepts registry 10 (.descriptor "Natural") matches .ok true
#guard descriptorType.accepts registry 10 (.descriptor "missing") matches .ok false
#guard (registry.inspect (.descriptor "Natural")).toOption == some natural.describe
#guard registry.inspect (.descriptor "missing") matches .error (.unknownDescriptor "missing")
#guard natural.describe.slot? "contract" == some (.object [("constructor", .text "integerRange"),
  ("lower", .integer 0), ("upper", .integer 100000)])
#guard (Contract.objectOf [("items", .listOf (.named "Nested"))]).describe.slot? "slots" ==
  some (.object [("items", .object [("constructor", .text "listOf"),
    ("element", .object [("constructor", .text "named"), ("identity", .text "Nested")])])])
#guard accepts registry 20 (.named "Nested")
  (.list [.integer 1, .list [.list [.integer 2]], .list []]) matches .ok true
#guard accepts registry 1 (.named "Nested") (.integer 1) matches .error (.budgetExhausted)
#guard accepts registry 10 (.dictionaryOf .text .integer)
  (.dictionary [(.text "x", .integer 1), (.text "y", .integer 2)]) matches .ok true
#guard accepts registry 10 (.dictionaryOf .text .integer)
  (.dictionary [(.integer 1, .integer 2)]) matches .ok false
#guard accepts registry 10 (.objectOf [("x", .integer), ("data", .listOf .text)])
  (.object [("x", .integer 1), ("data", .list [.text "a"])]) matches .ok true
#guard accepts registry 10 (.objectOf [("missing", .integer)]) (.object []) matches .ok false

private def typeConstructor : Descriptor := Descriptor.functionOf descriptorType descriptorType
#guard (typeConstructor.call registry 10 (.function "type-constructor") (.descriptor "Descriptor")).toOption ==
  some (.descriptor "Natural")

-- A class remains an open-recursive prototype for a dynamic descriptor.
private def classPrototype : Class := compose (Class.withSlot "kind" (fun self => .text self.name))
  (Class.withContract (.listOf .integer))
private def classValue : Descriptor :=
  (FiniteFix.certified classPrototype natural natural 1 (by rfl)).val
#guard classValue.accepts registry 10 (.list [.integer 1]) matches .ok true
#guard classValue.describe.slot? "kind" == some (.text "Natural")

private theorem admitted : Accepted registry (.integerRange 0 100000) (.integer 42) :=
  Descriptor.call_sound fn registry 10 _ _ rfl "increment" (.integer 41) (.integer 42)
    (by simp [fn, Descriptor.functionOf, Descriptor.call, natural, registry,
      Registry.function?, accepts, bind, Except.bind, pure, Except.pure]) |>.2

#eval IO.println "POOF-DYNAMIC-DESCRIPTOR-OK recursiveValues=true namedTypes=true functionBoundaries=true selfDescription=true classes=true"
#print axioms accepts_sound
#print axioms Descriptor.call_sound
#print axioms admitted
end LeanPoo.Tests.DynamicDescriptor
