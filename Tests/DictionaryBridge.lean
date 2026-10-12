import LeanPoo.Deriving.DictionaryCompiler

namespace LeanPoo.Tests.DictionaryBridge
open Prototype
universe u v w x y z

example (self : Prototype.DictionaryBridge A AFields) (parent : Prototype.DictionaryBridge B BFields)
    (result : Prototype.DictionaryBridge C CFields) (prototype : Proto A B C) :
    Prototype.DictionaryBridge.fromPrototype self parent result
      (Prototype.DictionaryBridge.toPrototype self parent result prototype) = prototype :=
  Prototype.DictionaryBridge.from_toPrototype self parent result prototype

example (self : Prototype.DictionaryBridge A AFields) (parent : Prototype.DictionaryBridge B BFields)
    (prototype : Proto A B A) (base : B) (seed : A) (depth : Nat) :
    FiniteFix.iterate (Prototype.DictionaryBridge.toPrototype self parent self prototype)
      (parent.toFields base) (self.toFields seed) depth = self.toFields (FiniteFix.iterate prototype base seed depth) :=
  Prototype.DictionaryBridge.iterate_toPrototype self parent prototype base seed depth

class Counter where
  value : Nat
  apply : Nat → Nat
  law : ∀ n, apply n = n+value
derive_dictionary Counter

private abbrev counter (n : Nat) : Counter := ⟨n, fun x => x+n, fun _ => rfl⟩
private abbrev parent : Proto Counter Counter Counter := fun _ inherited => counter (inherited.value+2)
private abbrev child : Proto Counter Counter Counter := fun self inherited => counter (self.value+inherited.value)
private abbrev delayedParent : DelayedProto Counter Counter Counter := fun _ inherited => counter (inherited.get.value+2)
private abbrev delayedChild : DelayedProto Counter Counter Counter := fun self inherited => counter (self.get.value+inherited.get.value)
private partial def diverge (seed : Nat) : Nat := diverge seed

private def descriptor (bound : Nat) : Descriptor Counter :=
  { name := s!"Counter {bound}"
    accepts := fun value => value.value <= bound
    display := fun value => toString value.value
    prototypeValue := some (counter 0)
    json := some {
      encode := fun value => Lean.toJson value.value
      decode := fun raw => (raw.getNat?).map counter } }

private def sameJson : Except String Lean.Json → Except String Lean.Json → Bool
  | .ok a, .ok b => a.compress == b.compress
  | .error a, .error b => a == b
  | _, _ => false

example (self inherited : Counter) :
    (Prototype.DictionaryBridge.toPrototype Counter.dictionaryBridge Counter.dictionaryBridge
      Counter.dictionaryBridge (compose child parent)) (Counter.toFields self) (Counter.toFields inherited) =
      Counter.toFields (compose child parent self inherited) :=
  Prototype.DictionaryBridge.toPrototype_apply _ _ _ _ _ _

#eval do
  IO.println "DICTIONARY-BRIDGE-START"
  let bridge := Counter.dictionaryBridge
  let source := compose child parent
  let compiled := Prototype.DictionaryBridge.toPrototype bridge bridge bridge source
  let separate := compose (Prototype.DictionaryBridge.toPrototype bridge bridge bridge child)
    (Prototype.DictionaryBridge.toPrototype bridge bridge bridge parent)
  let restored := Prototype.DictionaryBridge.fromPrototype bridge bridge bridge compiled
  let delayed := Prototype.DictionaryBridge.toDelayedPrototype bridge bridge bridge
    (DelayedProto.compose delayedChild delayedParent)
  let separatelyDelayed := DelayedProto.compose
    (Prototype.DictionaryBridge.toDelayedPrototype bridge bridge bridge delayedChild)
    (Prototype.DictionaryBridge.toDelayedPrototype bridge bridge bridge delayedParent)
  let mut calls := 0
  let mut iterations := 0
  for n in List.range 16 do
    for m in List.range 16 do
      let self := counter n
      let inherited := counter m
      let expected := n+m+2
      let values := [Counter.fromFields (compiled (Counter.toFields self) (Counter.toFields inherited)),
        Counter.fromFields (separate (Counter.toFields self) (Counter.toFields inherited)),
        restored self inherited,
        Counter.fromFields (delayed (Thunk.pure (Counter.toFields self)) (Thunk.pure (Counter.toFields inherited))),
        Counter.fromFields (separatelyDelayed (Thunk.pure (Counter.toFields self)) (Thunk.pure (Counter.toFields inherited)))]
      for value in values do
        letI : Counter := value
        unless Counter.value == expected && Counter.apply 7 == 7+expected do
          throw (IO.userError "compiled self/super composition changed dictionary dispatch")
        calls := calls+1
      for depth in List.range 9 do
        let value := Counter.fromFields (FiniteFix.iterate compiled (Counter.toFields inherited) (Counter.toFields self) depth)
        unless value.value == n+depth*(m+2) && value.apply 7 == 7+n+depth*(m+2) do
          throw (IO.userError "compiled finite self unfolding changed")
        iterations := iterations+1
  let unavailable := Thunk.mk fun _ => counter (diverge 0)
  let terminal := Prototype.DictionaryBridge.toDelayedPrototype bridge bridge bridge (DelayedProto.constant (counter 17))
  let badParent : DelayedProto Counter Counter Counter := fun _ _ => counter (diverge 0)
  let terminalOverBad := Prototype.DictionaryBridge.toDelayedPrototype bridge bridge bridge
    (DelayedProto.compose (DelayedProto.constant (counter 17)) badParent)
  let final := unavailable.map bridge.toFields
  unless (Counter.fromFields (terminal final final)).value == 17 &&
      (Counter.fromFields (terminalOverBad final final)).value == 17 do
    throw (IO.userError "dictionary conversion forced delayed self or overridden parent")
  let mut accepted := 0
  let mut refused := 0
  for bound in List.range 8 do
    let original := descriptor bound
    let fields := bridge.descriptor original
    for n in List.range 10 do
      let encoded := fields.encodeJson (Counter.toFields (counter n))
      unless sameJson encoded (original.encodeJson (counter n)) &&
          fields.display (Counter.toFields (counter n)) == toString n do
        throw (IO.userError "descriptor validation/display/encoding changed")
      match fields.decodeJson (Lean.toJson n), original.decodeJson (Lean.toJson n) with
      | .ok converted, .ok value =>
        let restored := Counter.fromFields converted
        unless restored.value == value.value && restored.apply 3 == 3+n do
          throw (IO.userError "descriptor decoder lost callable/proof fields")
        accepted := accepted+1
      | .error a, .error b =>
        unless a == b do throw (IO.userError "descriptor refinement errors changed")
        refused := refused+1
      | _, _ => throw (IO.userError "descriptor admission changed")
    let .error a := fields.decodeJson (.str "wrong") | throw (IO.userError "wrong JSON accepted")
    let .error b := original.decodeJson (.str "wrong") | throw (IO.userError "source wrong JSON accepted")
    unless a == b do throw (IO.userError "codec source errors changed")
  let noCodec : Descriptor Counter := {name := "no-codec", accepts := fun _ => true, display := fun _ => "counter"}
  unless sameJson ((bridge.descriptor noCodec).encodeJson (Counter.toFields (counter 0))) (noCodec.encodeJson (counter 0)) do
    throw (IO.userError "missing codec error changed")
  unless calls == 1280 && iterations == 2304 && accepted == 36 && refused == 44 do
    throw (IO.userError "compiled prototype/descriptor coverage changed")
  IO.println s!"DICTIONARY-BRIDGE-OK calls={calls} iterations={iterations} admitted={accepted} refused={refused} lazy-overrides=2"

#print axioms LeanPoo.Prototype.DictionaryBridge.from_toPrototype
#print axioms LeanPoo.Prototype.DictionaryBridge.toPrototype_compose
#print axioms LeanPoo.Prototype.DictionaryBridge.iterate_toPrototype
#print axioms LeanPoo.Prototype.DictionaryBridge.toDelayedPrototype_compose
#print axioms LeanPoo.Prototype.DictionaryBridge.descriptor_decodeJson
end LeanPoo.Tests.DictionaryBridge
