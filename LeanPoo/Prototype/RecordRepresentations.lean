import LeanPoo.Prototype.DictionaryRecord
import LeanPoo.Prototype.KeyedPrototype

/-! Correspondence of the concrete function, AVL dictionary and key-list
representations. Slot bodies remain arbitrary delayed self/super functions;
the relation compares their actual observations, including missing slots and
errors. Dictionary insertion is the certified structural source solution. -/
namespace LeanPoo.Prototype
variable {Key Value : Type} [DecidableEq Key]

abbrev FunctionRecord (Key Value : Type) := Record Key (fun _ => Except String Value)

def FunctionRecord.observation : Option (Except String Value) → Except String (Option Value)
  | none => .ok none
  | some (.error message) => .error message
  | some (.ok value) => .ok (some value)

def FunctionRecord.observe (record : FunctionRecord Key Value) (key : Key) :
    Except String (Option Value) := observation (record.lookup key)

def FunctionRecord.slotGen (key : Key)
    (body : Thunk (FunctionRecord Key Value) → Thunk (Except String (Option Value)) → Except String Value) :
    DelayedProto (FunctionRecord Key Value) (FunctionRecord Key Value) (FunctionRecord Key Value) :=
  Object.recordSlotGen key (fun self old => some (body self
    (Thunk.mk fun _ => observation old.get)))

def DictionaryRecord.Valid (order : OrderOps Key) (lt : Key → Key → Prop)
    (record : DictionaryRecord Key Value) : Prop :=
  record.dictionary = Dictionary.avl order ∧ ∃ tree, record.entries = .ok tree ∧
    tree.ValidAVL ∧ tree.Sorted lt

def DictionaryRecord.Related (dictionary : DictionaryRecord Key Value)
    (function : FunctionRecord Key Value) : Prop :=
  ∀ key, dictionary.lookup key = function.observe key

theorem DictionaryRecord.fromOrder_valid (order : OrderOps Key) (lt : Key → Key → Prop) :
    (fromOrder (Value := Value) order).Valid order lt :=
  ⟨rfl, .empty, rfl, trivial, by simp [Tree.Sorted, Tree.inorder]⟩

theorem DictionaryRecord.fromOrder_related (order : OrderOps Key) :
    (fromOrder (Value := Value) order).Related Record.empty := by
  intro key; rfl

theorem DictionaryRecord.slotGen_valid (order : OrderOps Key) (lt : Key → Key → Prop)
    (laws : order.Laws lt) (self inherited : Thunk (DictionaryRecord Key Value))
    (key : Key) (body) (valid : inherited.get.Valid order lt) :
    (slotGen key body self inherited).Valid order lt := by
  obtain ⟨dictionary, tree, entries, avl, sorted⟩ := valid
  let cell := Thunk.mk fun _ => body self (Thunk.mk fun _ => inherited.get.lookup key)
  obtain ⟨output, inserted, balanced, _, _⟩ := tree.avl_insert_complete order laws.total key cell avl
  refine ⟨dictionary, output, ?_, balanced, ?_⟩
  · simp [slotGen, entries, dictionary, Dictionary.avl, Dictionary.structural,
      cell, inserted, bind, Except.bind]
  · exact tree.avl_insert_sorted order lt laws output key cell sorted inserted

theorem DictionaryRecord.slotGen_observe (order : OrderOps Key) (lt : Key → Key → Prop)
    (laws : order.Laws lt) (self inherited : Thunk (DictionaryRecord Key Value))
    (key query : Key) (body) (valid : inherited.get.Valid order lt) :
    (slotGen key body self inherited).lookup query =
      if query = key then (body self (Thunk.mk fun _ => inherited.get.lookup key)).map some
      else inherited.get.lookup query := by
  obtain ⟨dictionary, tree, entries, avl, sorted⟩ := valid
  let cell := Thunk.mk fun _ => body self (Thunk.mk fun _ => inherited.get.lookup key)
  obtain ⟨output, inserted, _, _, _⟩ := tree.avl_insert_complete order laws.total key cell avl
  have lookup := Dictionary.avl_insert_lookup (Acc := Unit) order lt laws tree output key query cell sorted inserted
  have newEntries : (slotGen key body self inherited).entries = .ok output := by
    simp only [slotGen, entries, dictionary, bind, Except.bind]
    exact inserted
  simp only [DictionaryRecord.lookup, newEntries, show (slotGen key body self inherited).dictionary =
    Dictionary.avl order from dictionary, bind, Except.bind]
  rw [lookup]
  by_cases same : query = key
  · simp only [ite_eq_left same]
    change (do return some (← body self (Thunk.mk fun _ => inherited.get.lookup key))) =
      (body self (Thunk.mk fun _ => inherited.get.lookup key)).map some
    cases body self (Thunk.mk fun _ => inherited.get.lookup key) <;> rfl
  · simp only [ite_eq_right same]
    simp only [DictionaryRecord.lookup, entries, dictionary, bind, Except.bind]

theorem FunctionRecord.slotGen_observe (self inherited : Thunk (FunctionRecord Key Value))
    (key query : Key) (body) :
    (slotGen key body self inherited).observe query =
      if query = key then (body self (Thunk.mk fun _ => inherited.get.observe key)).map some
      else inherited.get.observe query := by
  by_cases same : query = key
  · subst query
    simp only [slotGen, Object.recordSlotGen, observe, dite_true, ite_true]
    change observation (some (body self (Thunk.mk fun _ => inherited.get.observe key))) =
      (body self (Thunk.mk fun _ => inherited.get.observe key)).map some
    cases body self (Thunk.mk fun _ => inherited.get.observe key) <;> rfl
  · simp [slotGen, Object.recordSlotGen, observe, same]

/-- Related final selves and parents stay related after arbitrary corresponding
slot bodies; lazy inherited reads, user errors and all other keys are retained. -/
theorem DictionaryRecord.slotGen_related (order : OrderOps Key) (lt : Key → Key → Prop)
    (laws : order.Laws lt)
    (dictionarySelf dictionaryParent : Thunk (DictionaryRecord Key Value))
    (functionSelf functionParent : Thunk (FunctionRecord Key Value))
    (key : Key) (dictionaryBody functionBody)
    (valid : dictionaryParent.get.Valid order lt)
    (parents : dictionaryParent.get.Related functionParent.get)
    (bodies : dictionaryBody dictionarySelf (Thunk.mk fun _ => dictionaryParent.get.lookup key) =
      functionBody functionSelf (Thunk.mk fun _ => functionParent.get.observe key)) :
    (slotGen key dictionaryBody dictionarySelf dictionaryParent).Related
      (FunctionRecord.slotGen key functionBody functionSelf functionParent) := by
  intro query
  rw [slotGen_observe order lt laws _ _ _ _ _ valid, FunctionRecord.slotGen_observe, bodies, parents]

/-- A slot specification can observe final self and lazily demand super. -/
abbrev SlotBody (Key Value : Type) :=
  (Key → Except String (Option Value)) → Thunk (Except String (Option Value)) → Except String Value

def DictionaryRecord.semanticSlot (key : Key) (body : SlotBody Key Value) :
    DelayedProto (DictionaryRecord Key Value) (DictionaryRecord Key Value) (DictionaryRecord Key Value) :=
  slotGen key (fun self old => body self.get.lookup old)

def FunctionRecord.semanticSlot (key : Key) (body : SlotBody Key Value) :
    DelayedProto (FunctionRecord Key Value) (FunctionRecord Key Value) (FunctionRecord Key Value) :=
  slotGen key (fun self old => body self.get.observe old)

def LayersRelated (order : OrderOps Key) (lt : Key → Key → Prop)
    (dictionary : DelayedProto (DictionaryRecord Key Value) (DictionaryRecord Key Value) (DictionaryRecord Key Value))
    (function : DelayedProto (FunctionRecord Key Value) (FunctionRecord Key Value) (FunctionRecord Key Value)) : Prop :=
  ∀ ds fs dp fp, ds.get.Related fs.get → dp.get.Related fp.get → dp.get.Valid order lt →
    (dictionary ds dp).Valid order lt ∧ (dictionary ds dp).Related (function fs fp)

theorem semanticSlot_related (order : OrderOps Key) (lt : Key → Key → Prop)
    (laws : order.Laws lt) (key : Key) (body : SlotBody Key Value) :
    LayersRelated order lt (DictionaryRecord.semanticSlot key body) (FunctionRecord.semanticSlot key body) := by
  intro ds fs dp fp selves parents valid
  refine ⟨DictionaryRecord.slotGen_valid order lt laws ds dp key _ valid, ?_⟩
  apply DictionaryRecord.slotGen_related order lt laws ds dp fs fp key _ _ valid parents
  have sameSelf : ds.get.lookup = fs.get.observe := funext selves
  have sameParent : dp.get.lookup key = fp.get.observe key := parents key
  simp only [sameSelf, sameParent]

theorem LayersRelated.compose (order : OrderOps Key) (lt : Key → Key → Prop)
    (dc dp fc fp) (child : LayersRelated (Value := Value) order lt dc fc)
    (parent : LayersRelated order lt dp fp) :
    LayersRelated order lt (DelayedProto.compose dc dp) (DelayedProto.compose fc fp) := by
  intro ds fs db fb selves bases valid
  obtain ⟨parentValid, parentRelated⟩ := parent ds fs db fb selves bases valid
  exact child ds fs (Thunk.mk fun _ => dp ds db) (Thunk.mk fun _ => fp fs fb)
    selves parentRelated parentValid

namespace KeyedPrototype

theorem expose_values (keys : List Key) (self parent : Thunk (Rec Values)) (key : Key) :
    (expose keys self parent).lookup (.inl key) = parent.get.lookup (.inl key) := by
  simp [expose, Object.recordSlotGen]

theorem expose_keys (keys : List Key) (self parent : Thunk (Rec Values)) :
    (expose keys self parent).lookup (.inr ()) = some keys := by
  simp [expose, Object.recordSlotGen]

theorem compose_keys (child parent : Definition Key Values) :
    (compose child parent).keys = child.keys ++ parent.keys := rfl

theorem compose_layer (child parent : Definition Key Values)
    (self inherited : Thunk (Rec Values)) :
    (compose child parent).layer self inherited =
      child.layer self (Thunk.mk fun _ => parent.layer self inherited) := rfl

theorem Definition.withKeys_values (definition : Definition Key Values)
    (self parent : Thunk (Rec Values)) (key : Key) :
    (definition.withKeys false self parent).lookup (.inl key) =
      (definition.layer self parent).lookup (.inl key) := by
  simp [withKeys, DelayedProto.compose, expose, Object.recordSlotGen, Thunk.get]

theorem Definition.withKeys_keys (definition : Definition Key Values)
    (self parent : Thunk (Rec Values)) :
    (definition.withKeys false self parent).lookup (.inr ()) = some definition.keys := by
  simp [withKeys, DelayedProto.compose, expose, Object.recordSlotGen]

theorem Definition.withKeys_override (definition : Definition Key Values)
    (self parent : Thunk (Rec Values)) :
    definition.withKeys true self parent =
      definition.layer self (Thunk.mk fun _ => expose definition.keys self parent) := rfl

def valueView (record : Rec Values) : Record Key Values :=
   { lookup := fun key => record.lookup (.inl key) }

/-- Projection of an arbitrary delayed slot body into the ordinary function
record; both final self and lazy super retain their projected meanings. -/
theorem recordSlotGen_values (key query : Key)
    (compute : Thunk (Record Key Values) → Thunk (Option (Values key)) → Option (Values key))
    (self parent : Thunk (Rec Values)) :
    (Object.recordSlotGen (Key := Slot Key) (Value := KeyedPrototype.Value Values) (.inl key) (fun final old =>
      compute (Thunk.mk fun _ => valueView final.get) old) self parent).lookup (.inl query) =
    (Object.recordSlotGen key compute (Thunk.mk fun _ => valueView self.get)
      (Thunk.mk fun _ => valueView parent.get)).lookup query := by
  by_cases same : query = key
  · subst query
    simp only [Object.recordSlotGen, dite_true]
    rfl
  · simp [Object.recordSlotGen, same, valueView]; rfl

theorem slot_values (key query : Key) (value : Values key)
    (self parent : Thunk (Rec Values)) :
    ((slot key value).layer self parent).lookup (.inl query) =
      (Object.recordSlotGen key (fun _ _ => some value)
        (Thunk.mk fun _ => valueView self.get) (Thunk.mk fun _ => valueView parent.get)).lookup query := by
  by_cases same : query = key
  · subst query; simp [slot, Object.recordSlotGen]
  · simp [slot, Object.recordSlotGen, valueView, same]; rfl

end KeyedPrototype
end LeanPoo.Prototype
