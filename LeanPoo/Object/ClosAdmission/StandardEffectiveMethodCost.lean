-- SPDX-License-Identifier: Apache-2.0 AND LGPL-2.1-or-later
import Std

/-!
Cost at the standard effective-method selection boundary, after the four
qualifier reads and before execution. The staged and direct-field traces
correspond to the b487978 and a3add7b arms, respectively. A transfer is a
named Scheme/Gambit handoff here, not a native instruction or a time estimate.
-/
namespace LeanPoo.Object.ClosAdmission.StandardEffectiveMethodCost

inductive HookResult where
  | throws | invalidFields | invalidOwner | accepted

/-- The direct outcome is the result of the live, checked attempt. -/
inductive Route where
  | noRoots (sameOwner : Bool)
  | directMiss (sameOwner : Bool)
  | directHit
  | hook (result : HookResult)

inductive Effect where
  | qualifierReads | readProtocol | readHook | checkProtocolOwner
  | tryDirect | construct | openHook | callHook | checkReturnedFields
  | checkReturnedOwner | reject
  deriving DecidableEq

inductive Transfer where
  | prepareDefault | enterStandardSelector | invokeDeferredDefault
  deriving DecidableEq

private abbrev Step := Sum Effect Transfer

private def protocolReads : List Step :=
  [.inl .readProtocol, .inl .readHook, .inl .checkProtocolOwner]

private def defaultResult (sameOwner : Bool) : List Step :=
  [.inl .construct, .inl .checkReturnedOwner] ++
    (if sameOwner then [] else [.inl .reject])

private def hookResult : HookResult → List Step
  | .throws => []
  | .invalidFields => [.inl .checkReturnedFields, .inl .reject]
  | .invalidOwner => [.inl .checkReturnedFields, .inl .checkReturnedOwner, .inl .reject]
  | .accepted => [.inl .checkReturnedFields, .inl .checkReturnedOwner]

private def returned (defer : List Step) : Route → List Step
  | .noRoots ok => defer ++ defaultResult ok
  | .directMiss ok => [.inl .tryDirect] ++ defer ++ defaultResult ok
  | .directHit => [.inl .tryDirect]
  | .hook result =>
    [.inl .openHook] ++ defer ++ [.inl .construct, .inl .callHook] ++ hookResult result

private def staged (route : Route) : List Step :=
  [.inl .qualifierReads, .inr .prepareDefault] ++ protocolReads ++
    returned [.inr .invokeDeferredDefault] route

private def directFields (route : Route) : List Step :=
  [.inl .qualifierReads, .inr .enterStandardSelector] ++ protocolReads ++ returned [] route

private def effects (steps : List Step) : List Effect :=
  steps.filterMap fun
    | .inl effect => some effect
    | .inr _ => none

private def transferCost (weight : Transfer → Nat) (steps : List Step) : Nat :=
  (steps.map fun
    | .inl _ => 0
    | .inr transfer => weight transfer).sum

private def transfers : List Step → Nat := transferCost (fun _ => 1)

theorem preserves_ordered_effects (route : Route) :
    effects (staged route) = effects (directFields route) := by
  cases route with
  | noRoots ok => cases ok <;> rfl
  | directMiss ok => cases ok <;> rfl
  | directHit => rfl
  | hook result => cases result <;> rfl

/-- Expand each common operation with its own ordered observations. For
callback-sensitive reads, the expansion is indexed by the position of the
effect in the ordered trace and can use the state at that point. -/
theorem preserves_observations {Obs : Type}
    (interpret : List Effect → List Obs) (route : Route) :
    interpret (effects (staged route)) = interpret (effects (directFields route)) :=
  congrArg interpret (preserves_ordered_effects route)

/-- These counts cover the changed handoffs. The checked constructor,
direct attempt and hook calls are separately present in the effect trace. -/
theorem transfer_counts (route : Route) :
    (transfers (staged route), transfers (directFields route)) =
      match route with
      | .directHit => (1, 1)
      | _ => (2, 1) := by
  cases route with
  | noRoots ok => cases ok <;> rfl
  | directMiss ok => cases ok <;> rfl
  | directHit => rfl
  | hook result => cases result <;> rfl

/-- Transfer costs may differ across the old thunk path and the new
selector. Even with the same effect costs, this inequality must still hold
for a reduction in local execution cost. -/
theorem transfer_cost_condition (weight : Transfer → Nat) (route : Route) :
    transferCost weight (directFields route) ≤ transferCost weight (staged route) ↔
      weight .enterStandardSelector ≤ weight .prepareDefault +
        (match route with
         | .directHit => 0
         | _ => weight .invokeDeferredDefault) := by
  cases route with
  | noRoots ok => cases ok <;> simp [transferCost, staged, directFields, protocolReads,
      returned, defaultResult, Nat.add_comm]
  | directMiss ok => cases ok <;> simp [transferCost, staged, directFields, protocolReads,
      returned, defaultResult, Nat.add_comm]
  | directHit => simp [transferCost, staged, directFields, protocolReads, returned]
  | hook result => cases result <;> simp [transferCost, staged, directFields, protocolReads,
      returned, hookResult, Nat.add_comm]

theorem hook_result_checks_follow_callback :
    (returned [] (.hook .accepted)) =
      [.inl .openHook, .inl .construct, .inl .callHook,
       .inl .checkReturnedFields, .inl .checkReturnedOwner] := rfl

theorem rejected_hook_fields_precede_owner_check :
    (returned [] (.hook .invalidFields)) =
      [.inl .openHook, .inl .construct, .inl .callHook,
       .inl .checkReturnedFields, .inl .reject] := rfl

/-- Guards visible in the a3add7b GVM excerpt between the protocol owner
check and entry to the selected route. When roots are absent the excerpt
sets the result register to false and then tests that same constant. -/
inductive Guard where
  | hasHook | hasRoots | directResult | constantFalse
  deriving DecidableEq

def guards : Route → List Guard
  | .noRoots _ => [.hasHook, .hasRoots, .constantFalse]
  | .directMiss _ | .directHit => [.hasHook, .hasRoots, .directResult]
  | .hook _ => [.hasHook]

theorem no_roots_has_redundant_gvm_guard (sameOwner : Bool) :
    (guards (.noRoots sameOwner)).length =
      ((guards (.noRoots sameOwner)).filter (· != .constantFalse)).length + 1 := rfl

end LeanPoo.Object.ClosAdmission.StandardEffectiveMethodCost
