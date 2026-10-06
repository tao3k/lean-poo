import LeanPoo.Prototype.DictionaryRecord
open LeanPoo.Prototype

private unsafe def run : IO Unit := do
  let order := OrderOps.instantiate (DelayedProto.compose OrderOps.compareMixin OrderOps.string)
  let base : DictionaryRecord String Int := DictionaryRecord.fromOrder order
  let layer := DelayedProto.compose (DictionaryRecord.compute "sum" fun self => do
      return (← self.get "x") + (← self.get "y"))
    (DelayedProto.compose (DictionaryRecord.modify "x" (· * 2))
      (DelayedProto.compose (DictionaryRecord.slot "x" 3) (DictionaryRecord.slot "y" 2)))
  let original := DictionaryRecord.instantiate layer base
  unless (← IO.ofExcept (original.get "x")) == 6 && (← IO.ofExcept (original.get "sum")) == 8 do
    throw (IO.userError "AVL record self/inherited slot case")
  let derived := DictionaryRecord.instantiate (DelayedProto.compose (DictionaryRecord.slot "x" 10) layer) base
  unless (← IO.ofExcept (derived.get "sum")) == 12 && (← IO.ofExcept (original.get "sum")) == 8 do
    throw (IO.userError "AVL record final-self rebinding or old snapshot")
  unless !(original.get "missing").isOk do throw (IO.userError "unbound slot admitted")
  let missing := DictionaryRecord.instantiate (DictionaryRecord.modify "missing" (· + 1)) base
  unless !(missing.get "missing").isOk do throw (IO.userError "unbound inherited slot admitted")
  let cold := DictionaryRecord.instantiate (DelayedProto.compose
    (DictionaryRecord.compute "unused" (fun _ => .error "must stay cold")) (DictionaryRecord.slot "x" 1)) base
  unless (← IO.ofExcept (cold.get "x")) == 1 do throw (IO.userError "unrequested slot forced")
  for size in List.range 33 do
    let slots := (List.range size).map fun n => DictionaryRecord.slot (toString n) (Int.ofNat n)
    let record := DictionaryRecord.instantiate (DelayedProto.composeAll slots) base
    for n in List.range size do
      unless (← IO.ofExcept (record.get (toString n))) == Int.ofNat n do
        throw (IO.userError "AVL record differs from scalar slot model")
  IO.println "POOF-DICTIONARY-RECORD-OK contexts=33 reads=528 finalSelf=true inherited=true coldSlot=true"
#eval run
