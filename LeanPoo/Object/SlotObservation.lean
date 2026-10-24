import LeanPoo.Prototype.DictionaryBridge

/-! Canonical packing of the existing slot-observation scope. The host supplies
lexical parameterization and faithful frame/callback identities. No VM timing,
thread scheduler, collector or arbitrary continuation semantics are inferred. -/
namespace LeanPoo.Object
universe u v w

/-- The three existing dynamic values, including opaque frame and callback data. -/
structure ReadScope (Frame : Type u) (Observer : Type v) (Check : Type w) where
  frame : Option Frame
  observers : List Observer
  prechecks : List Check

variable {Frame : Type u} {Observer : Type v} {Check : Type w}

/-- Disabled observation clears every channel together. -/
def emptyReadScope : ReadScope Frame Observer Check := ⟨none, [], []⟩

/-- The ordinary disabled path uses no allocated context; active scopes retain
all original payloads. No comparison between callbacks is required. -/
def packReadScope : ReadScope Frame Observer Check → Option (Sum Frame (ReadScope Frame Observer Check))
  | ⟨none, [], []⟩ => none
  | ⟨some frame, [], []⟩ => some (.inl frame)
  | scope => some (.inr scope)

/-- Interpret the optional context using the original three-channel interface. -/
def unpackReadScope : Option (Sum Frame (ReadScope Frame Observer Check)) → ReadScope Frame Observer Check
  | none => emptyReadScope
  | some (.inl frame) => ⟨some frame, [], []⟩
  | some (.inr scope) => scope

/-- Packing preserves every callback, order, precheck and exact frame payload. -/
theorem unpackReadScope_pack (scope : ReadScope Frame Observer Check) :
    unpackReadScope (packReadScope scope) = scope := by
  cases scope with
  | mk frame observers prechecks =>
    cases frame <;> cases observers <;> cases prechecks <;> rfl

/-- Reuse the existing representation bridge over canonical optional contexts.
An allocated but completely empty context is not a second representation. -/
def readScopeBridge : Prototype.DictionaryBridge (ReadScope Frame Observer Check)
    {packed : Option (Sum Frame (ReadScope Frame Observer Check)) //
      packReadScope (unpackReadScope packed) = packed} where
  toFields scope := ⟨packReadScope scope, congrArg packReadScope (unpackReadScope_pack scope)⟩
  fromFields packed := unpackReadScope packed.val
  from_to := unpackReadScope_pack
  to_from packed := Subtype.ext packed.property

/-- Installing an observer shares the caller's capture frame and prepends its
optional precheck, keeping inner-before-outer callback order. -/
def observeReadScope (scope : ReadScope Frame Observer Check) (observer : Observer)
    (before : Option Check) : ReadScope Frame Observer Check :=
  { scope with observers := observer :: scope.observers
               prechecks := match before with | none => scope.prechecks | some check => check :: scope.prechecks }

/-- Recording replaces only the capture frame; observer and precheck payloads
remain the same original values rather than reconstructed approvals. -/
def captureReadScope (scope : ReadScope Frame Observer Check) (frame : Frame) : ReadScope Frame Observer Check :=
  { scope with frame := some frame }

/-- Both entry operations create an active optional context, including an empty
observer list when an actual capture frame is installed. -/
theorem observeReadScope_active (scope : ReadScope Frame Observer Check)
    (observer : Observer) (before : Option Check) :
    packReadScope (observeReadScope scope observer before) = some (.inr (observeReadScope scope observer before)) := by
  cases scope with
  | mk frame observers prechecks => cases frame <;> rfl

theorem captureReadScope_active (scope : ReadScope Frame Observer Check) (frame : Frame) :
    (packReadScope (captureReadScope scope frame)).isSome = true := by
  cases scope with
  | mk old observers prechecks => cases observers <;> cases prechecks <;> rfl

/-- Capture without observers reuses the original frame rather than allocating
an additional context record. Its frame/collection allocation is still charged. -/
theorem captureReadScope_frameOnly (frame : Frame) :
    packReadScope (captureReadScope (emptyReadScope : ReadScope Frame Observer Check) frame) =
      some (.inl frame) := rfl

/-- Any interpreted consumer keeps its entire result, including an Except cause
or an explicit ordered event trace. The caller's lexical scope is unchanged. -/
theorem readScope_consumer (caller scope : ReadScope Frame Observer Check)
    (consume : ReadScope Frame Observer Check → Result) :
    (consume (unpackReadScope (packReadScope scope)), caller) = (consume scope, caller) := by
  rw [unpackReadScope_pack]

/-- Already disabled consumers run directly at precisely the original empty
scope, preserving multiple returned values and errors in their interpretation. -/
theorem emptyReadScope_consumer (consume : ReadScope Frame Observer Check → Result) :
    consume (unpackReadScope none) = consume emptyReadScope := rfl

/-- Source-primitive accounting for disabled calls, read delivery and capture
entry. Frame allocation and callback/storage work are shared and excluded here.
One capture under existing observers can add lookup/tag/field/allocation work;
its complete premium remains on the bound, even when hot paths become cheaper.
The hypotheses price concrete primitives, not entire desired workflow totals. -/
theorem readScope_cost_bound (disabled deliveries captures lookup binding tag field allocation : Nat)
    (lookup_price : lookup ≤ 3 * binding) (delivery_price : tag + 2 * field ≤ lookup) :
    disabled * lookup + deliveries * (lookup + tag + 2 * field) +
        captures * (lookup + tag + 2 * field + allocation) ≤
      3 * (disabled * binding) + 2 * (deliveries * lookup) +
        captures * (lookup + tag + 2 * field + allocation) := by
  have disabled_bound : disabled * lookup ≤ 3 * (disabled * binding) := by
    simpa only [Nat.mul_left_comm] using Nat.mul_le_mul_left disabled lookup_price
  have delivery_bound : deliveries * (lookup + tag + 2 * field) ≤
      2 * (deliveries * lookup) := by
    simpa only [Nat.mul_add, Nat.two_mul, Nat.add_assoc] using
      Nat.mul_le_mul_left deliveries (Nat.add_le_add_left delivery_price lookup)
  exact Nat.add_le_add_right (Nat.add_le_add disabled_bound delivery_bound) _

end LeanPoo.Object
