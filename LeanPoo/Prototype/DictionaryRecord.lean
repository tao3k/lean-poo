import LeanPoo.Prototype.AVL

/-! POOF's alternate dictionary-backed record representation. Entries retain
delayed slot computations; prototypes reuse the AVL node-only extension. -/
namespace LeanPoo.Prototype

structure DictionaryRecord (Key Value : Type) where
  dictionary : Dictionary Key (Thunk (Except String Value)) Unit
  entries : Except String (Tree Key (Thunk (Except String Value)))

def DictionaryRecord.lookup (record : DictionaryRecord Key Value) (key : Key) :
    Except String (Option Value) := do
  let tree ← record.entries
  match ← record.dictionary.ref tree key with
  | none => return none
  | some cell => return some (← cell.get)

def DictionaryRecord.get (record : DictionaryRecord Key Value) (key : Key) : Except String Value := do
  let some value ← record.lookup key | throw "unbound slot"
  return value

/-- Keep the constructor delayed and pass the final record and inherited slot. -/
def DictionaryRecord.slotGen (key : Key)
    (body : Thunk (DictionaryRecord Key Value) → Thunk (Except String (Option Value)) → Except String Value) :
    DelayedProto (DictionaryRecord Key Value) (DictionaryRecord Key Value) (DictionaryRecord Key Value) :=
  fun self inherited =>
    let parent := inherited.get
    let old := Thunk.mk fun _ => parent.lookup key
    let cell := Thunk.mk fun _ => body self old
    { parent with entries := do
        let tree ← parent.entries
        parent.dictionary.acons key cell tree }

def DictionaryRecord.slot (key : Key) (value : Value) :
    DelayedProto (DictionaryRecord Key Value) (DictionaryRecord Key Value) (DictionaryRecord Key Value) :=
  slotGen key (fun _ _ => .ok value)

def DictionaryRecord.compute (key : Key) (calculate : DictionaryRecord Key Value → Except String Value) :
    DelayedProto (DictionaryRecord Key Value) (DictionaryRecord Key Value) (DictionaryRecord Key Value) :=
  slotGen key (fun self _ => calculate self.get)

def DictionaryRecord.modify (key : Key) (change : Value → Value) :
    DelayedProto (DictionaryRecord Key Value) (DictionaryRecord Key Value) (DictionaryRecord Key Value) :=
  slotGen key (fun _ inherited => do
    let some value ← inherited.get | throw "unbound inherited slot"
    return change value)

unsafe def DictionaryRecord.fromOrder (order : OrderOps Key) : DictionaryRecord Key Value :=
  { dictionary := Dictionary.instantiate order
      (DelayedProto.compose Dictionary.avlRebalance Dictionary.binaryTree)
    entries := .ok .empty }

unsafe def DictionaryRecord.instantiate
    (prototype : DelayedProto (DictionaryRecord Key Value) (DictionaryRecord Key Value) (DictionaryRecord Key Value))
    (base : DictionaryRecord Key Value) : DictionaryRecord Key Value :=
  (DelayedProto.instantiate prototype (Thunk.pure base)).get

end LeanPoo.Prototype
