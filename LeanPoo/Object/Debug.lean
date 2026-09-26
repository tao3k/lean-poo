import LeanPoo.Object.Resolve
import LeanPoo.Proof.Invalidation

/-!
Debugging support for agent-authored objects. `Debug.Program` gives all slot
reads in one run a shared step budget and reports the key path on cycles.
Arbitrary Lean code inside a slot body is outside that budget.
-/

namespace LeanPoo.Object.Debug

universe u v

/-- Explain the C4 order and the declarations that contribute one slot. -/
structure Resolution (Key : Type u) where
  key : Key
  precedence : List String
  declaringNodes : List String

def Plan.explain (plan : Object.Plan Key Value) (key : Key) : Resolution Key where
  key := key
  precedence := plan.precedence
  declaringNodes := plan.precedence.filter (fun name =>
    match plan.schema.declaration name with
    | none => false
    | some declaration =>
        (declaration.slot key).isSome || (declaration.default key).isSome)

inductive Error (Key : Type u) where
  | cycle (path : List Key)
  | fuelExhausted (path : List Key)
  deriving Repr, DecidableEq

inductive Event (Key : Type u) where
  | enter (key : Key)
  | resolved (key : Key)
  | missing (key : Key)
  | rejectedCycle (path : List Key)
  | exhausted (path : List Key)
  deriving Repr, DecidableEq

private structure TraceState (Key : Type u) where
  remaining : Nat
  eventsRev : List (Event Key) := []

abbrev TraceM (Key : Type u) :=
  ExceptT (Error Key) (StateM (TraceState Key))

abbrev Read (Key : Type u) (Value : Key → Type u) :=
  (key : Key) → TraceM Key (Option (Value key))

abbrev Method (Key : Type u) (Value : Key → Type u) (key : Key) :=
  Read Key Value → TraceM Key (Option (Value key))

structure Report (Key : Type u) (α : Type u) where
  result : Except (Error Key) α
  events : List (Event Key)
  stepsUsed : Nat

structure Program (Key : Type u) (Value : Key → Type u) where
  slots : List (Object.Entry Key (Method Key Value)) := []

def Program.empty : Program Key Value := ⟨[]⟩

def Program.withSlot [DecidableEq Key] (program : Program Key Value)
    (key : Key) (method : Method Key Value key) : Program Key Value :=
  ⟨Object.Entry.replace program.slots key method⟩

/-- Every read spends shared fuel; events survive even a failed run. -/
def Program.runTrace [DecidableEq Key] (program : Program Key Value)
    (fuel : Nat) (key : Key) : Report Key (Option (Value key)) :=
  let (result, state) := (go fuel [] key).run { remaining := fuel }
  ⟨result, state.eventsRev.reverse, fuel - state.remaining⟩
where
  emit (event : Event Key) : TraceM Key Unit :=
    modify fun state => { state with eventsRev := event :: state.eventsRev }
  go : Nat → List Key → (key : Key) →
      TraceM Key (Option (Value key))
    | 0, stack, key => do
        let path := stack.reverse ++ [key]
        emit (.exhausted path)
        throw (.fuelExhausted path)
    | depth + 1, stack, key => do
        let state ← get
        if state.remaining == 0 then
          let path := stack.reverse ++ [key]
          emit (.exhausted path)
          throw (.fuelExhausted path)
        modify fun state => { state with remaining := state.remaining - 1 }
        if key ∈ stack then
          let path := stack.reverse ++ [key]
          emit (.rejectedCycle path)
          throw (.cycle path)
        else
          emit (.enter key)
          match Object.Entry.lookup program.slots key with
          | none =>
              emit (.missing key)
              pure none
          | some method =>
              let value ← method (go depth (key :: stack))
              emit (.resolved key)
              pure value

def Program.run [DecidableEq Key] (program : Program Key Value)
    (fuel : Nat) (key : Key) : Except (Error Key) (Option (Value key)) :=
  (program.runTrace fuel key).result

end LeanPoo.Object.Debug

namespace LeanPoo.Proof.Debug

universe u v

/-- Why one existing obligation will or will not be reused. -/
structure Impact (Key : Type u) where
  dependencies : List Key
  changed : List Key
  needsRepair : Bool
  deriving Repr, DecidableEq

def explainPatch {Key : Type u} {Value : Key → Type v}
    [DecidableEq Key] (object : ProofObject Key Value)
    (patch : Patch Key Value) : List (Impact Key) :=
  object.obligations.map fun obligation =>
    let changed := changedDependencies obligation patch
    { dependencies := obligation.dependencies
      changed
      needsRepair := !changed.isEmpty }

end LeanPoo.Proof.Debug
