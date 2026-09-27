import LeanPoo.Object.Generic

/-!
The paper factors static and dynamic class-method calls through the same
dictionary invocation. Lean's dependent function type is the dictionary:
each method key fixes its argument and result types. The only difference is
whether the dictionary comes from the runtime object or from the caller's
declared context. C4 may produce either dictionary through `Memoized.read`.
-/

namespace LeanPoo.Object

/-- The method key determines the complete method signature. -/
abbrev DictionaryMethod (Key Receiver : Type)
    (Args Result : Key → Type) (key : Key) :=
  Receiver → Args key → Result key

abbrev MethodDictionary (Key Receiver : Type)
    (Args Result : Key → Type) :=
  (key : Key) → Option (DictionaryMethod Key Receiver Args Result key)

namespace MethodDictionary

/-- Both dispatch strategies use this one invocation rule. -/
def call (dictionary : MethodDictionary Key Receiver Args Result)
    (key : Key) (receiver : Receiver) (args : Args key)
    (onMissing : Receiver → Args key → Result key) : Result key :=
  match dictionary key with
  | some method => method receiver args
  | none => onMissing receiver args

/-- Select one method at the caller's chosen stage. The returned Lean function
no longer consults a dictionary when it is invoked. -/
def select (dictionary : MethodDictionary Key Receiver Args Result)
    (key : Key) (onMissing : Receiver → Args key → Result key) :
    DictionaryMethod Key Receiver Args Result key :=
  (dictionary key).getD onMissing

theorem select_call (dictionary : MethodDictionary Key Receiver Args Result)
    (key : Key) (receiver : Receiver) (args : Args key)
    (onMissing : Receiver → Args key → Result key) :
    (dictionary.select key onMissing) receiver args =
      dictionary.call key receiver args onMissing := by
  cases h : dictionary key with
  | none => simp [MethodDictionary.select, MethodDictionary.call, h]
  | some method => simp [MethodDictionary.select, MethodDictionary.call, h]

/-- A C4 object's resolved method slots form a first-class dictionary.
The existing lazy evaluator remains the authority for inherited methods. -/
def fromMemoized [BEq Key] [LawfulBEq Key] [Hashable Key]
    (object : Memoized Key (DictionaryMethod Key Receiver Args Result)) :
    MethodDictionary Key Receiver Args Result :=
  object.read

theorem fromMemoized_select [BEq Key] [LawfulBEq Key] [Hashable Key]
    (object : Memoized Key (DictionaryMethod Key Receiver Args Result))
    (key : Key) :
    fromMemoized object key = object.read key := rfl

end MethodDictionary

/-- The runtime object carries its own method dictionary as a first-class
value. Methods operate on the typed receiver payload. -/
structure DictionaryObject (Key Receiver : Type)
    (Args Result : Key → Type) where
  receiver : Receiver
  methods : MethodDictionary Key Receiver Args Result

namespace DictionaryObject

/-- Dynamic dispatch selects the dictionary attached to this object. -/
def callDynamic (object : DictionaryObject Key Receiver Args Result)
    (key : Key) (args : Args key)
    (onMissing : Receiver → Args key → Result key) : Result key :=
  MethodDictionary.call object.methods key object.receiver args onMissing

/-- Static dispatch selects a dictionary from the caller's declared context.
The runtime object still supplies the receiver and arguments. -/
def callStatic (object : DictionaryObject Key Receiver Args Result)
    (declared : MethodDictionary Key Receiver Args Result)
    (key : Key) (args : Args key)
    (onMissing : Receiver → Args key → Result key) : Result key :=
  MethodDictionary.call declared key object.receiver args onMissing

/-- Invoke a previously selected static method without looking up the
dictionary again. The caller owns the stage at which selection happened. -/
def callSelected (object : DictionaryObject Key Receiver Args Result)
    (selected : DictionaryMethod Key Receiver Args Result key)
    (args : Args key) : Result key :=
  selected object.receiver args

theorem callSelected_eq_static
    (object : DictionaryObject Key Receiver Args Result)
    (declared : MethodDictionary Key Receiver Args Result)
    (key : Key) (args : Args key)
    (onMissing : Receiver → Args key → Result key) :
    object.callSelected (declared.select key onMissing) args =
      object.callStatic declared key args onMissing :=
  declared.select_call key object.receiver args onMissing

/-- A new runtime dictionary is a new first-class object. The old value and
any previously selected static dictionary retain their own behavior. -/
def withMethods (object : DictionaryObject Key Receiver Args Result)
    (methods : MethodDictionary Key Receiver Args Result) :
    DictionaryObject Key Receiver Args Result :=
  { object with methods }

theorem callStatic_own (object : DictionaryObject Key Receiver Args Result)
    (key : Key) (args : Args key)
    (onMissing : Receiver → Args key → Result key) :
    object.callStatic object.methods key args onMissing =
      object.callDynamic key args onMissing := rfl

theorem withMethods_dynamic (object : DictionaryObject Key Receiver Args Result)
    (methods : MethodDictionary Key Receiver Args Result)
    (key : Key) (args : Args key)
    (onMissing : Receiver → Args key → Result key) :
    (object.withMethods methods).callDynamic key args onMissing =
      object.callStatic methods key args onMissing := rfl

end DictionaryObject

/-- Reuse the existing `Generic` invoker when a receiver provides a runtime
dictionary. A constant provider expresses a statically selected dictionary. -/
def Generic.fromDictionary (key : Key)
    (dictionaryOf : Receiver → MethodDictionary Key Receiver Args Result)
    (fallback : Receiver → Args key → Result key) :
    Generic Receiver (DictionaryMethod Key Receiver Args Result key)
      (Args key) (Result key) :=
  { select := fun receiver => dictionaryOf receiver key
    invoke := fun method receiver args => method receiver args
    fallback }

theorem Generic.fromDictionary_call (key : Key)
    (dictionaryOf : Receiver → MethodDictionary Key Receiver Args Result)
    (fallback : Receiver → Args key → Result key)
    (receiver : Receiver) (args : Args key) :
    (Generic.fromDictionary key dictionaryOf fallback).call receiver args =
      MethodDictionary.call (dictionaryOf receiver) key receiver args fallback := by
  cases h : dictionaryOf receiver key with
  | none => simp [Generic.fromDictionary, Generic.call, MethodDictionary.call, h]
  | some method => simp [Generic.fromDictionary, Generic.call, MethodDictionary.call, h]

end LeanPoo.Object
