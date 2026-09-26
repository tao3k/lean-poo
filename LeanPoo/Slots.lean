import Std
import LeanPoo.Compose
import LeanPoo.Object.Instance

namespace LeanPoo

universe u v

/-- Does any declaration in the C4 precedence provide this key? -/
def hasSlot (plan : Object.Plan Key Value) (key : Key) : Bool :=
  plan.precedence.any (fun name =>
    match plan.schema.declaration name with
    | none => false
    | some declaration =>
      (declaration.slot key).isSome || (declaration.default key).isSome)

/-- Check an ordered collection of required slots against one compiled object. -/
def hasSlots (plan : Object.Plan Key Value) (keys : List Key) : Bool :=
  keys.all (hasSlot plan)

/-- Enumerate declared keys in Gerbil object.ss order: least-specific C4
declaration first, direct slots before defaults, skipping repetitions. -/
def allSlots [BEq Key] [LawfulBEq Key] [Hashable Key]
    (plan : Object.Plan Key Value) : List Key :=
  let (_, reversed) := plan.precedence.reverse.foldl
    (fun (seen, reversed) name =>
      let keys := match plan.schema.declaration name with
        | none => []
        | some declaration => declaration.directKeys
      keys.foldl (fun (seen, reversed) key =>
        if seen.contains key then (seen, reversed)
        else (seen.insert key, key :: reversed)) (seen, reversed))
    (({} : Std.HashSet Key), [])
  reversed.reverse

/-- Sort the finite declared key set without imposing a global order on Key. -/
def allSlotsSorted [BEq Key] [LawfulBEq Key] [Hashable Key]
    (plan : Object.Plan Key Value) (lessEq : Key → Key → Bool) : List Key :=
  (allSlots plan).mergeSort lessEq

/-- Assemble all slots from the declaration-owned order. -/
def prepareDeclared [BEq Key] [LawfulBEq Key] [Hashable Key]
    (plan : Object.Plan Key Value) :
    Object.Prepared Key Value :=
  plan.prepare (allSlots plan)

/-- A fixed-point instance can prepare its complete declaration-owned order. -/
def Object.Instance.prepareDeclared [BEq Key] [LawfulBEq Key] [Hashable Key]
    {plan : Object.Plan Key Value}
    (instanceValue : Object.Instance Key Value plan) :
    Object.Prepared Key Value :=
  instanceValue.prepare (allSlots plan)

/-- Create a cache for every declared slot of one fixed-point instance. -/
def Object.Instance.cacheDeclared [BEq Key] [LawfulBEq Key] [Hashable Key]
    {plan : Object.Plan Key Value}
    (instanceValue : Object.Instance Key Value plan) :
    Object.Cache instanceValue.prepareDeclared instanceValue.state :=
  instanceValue.cache (allSlots plan)

/-- Eagerly fill an explicit cache in declaration order. -/
def Object.Cache.forceDeclared [BEq Key] [LawfulBEq Key] [Hashable Key]
    {prepared : Object.Prepared Key Value} {self : Object.Self Key Value}
    (cache : Object.Cache prepared self) : Object.Cache prepared self :=
  cache.force (allSlots prepared.plan)

/-- Collect a caller's ordered keys while preserving each key's value type. -/
def collectValues {Key : Type u} {Value : Key → Type v}
    (keys : List Key)
    (lookup : (key : Key) → Except (Object.LookupError Key) (Value key)) :
    Except (Object.LookupError Key) (List (Sigma Value)) :=
  keys.mapM (fun key =>
    match lookup key with
    | .ok value => .ok ⟨key, value⟩
    | .error error => .error error)

/-- Read selected typed slots from a validated fixed-point instance. -/
def Object.Instance.select {Key : Type u} {Value : Key → Type v}
    {plan : Object.Plan Key Value}
    (instanceValue : Object.Instance Key Value plan)
    (keys : List Key) :
    Except (Object.LookupError Key) (List (Sigma Value)) :=
  collectValues keys instanceValue.ref

/-- Materialize the typed equivalent of object.ss .alist from a validated
fixed-point instance. -/
def Object.Instance.values [BEq Key] [LawfulBEq Key] [Hashable Key]
    {plan : Object.Plan Key Value}
    (instanceValue : Object.Instance Key Value plan) :
    Except (Object.LookupError Key) (List (Sigma Value)) :=
  instanceValue.select (allSlots plan)

end LeanPoo
