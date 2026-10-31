import LeanPoo.Prototype.DescriptorReflection

/-! Public declaration reflection reuses the existing descriptor and validator.
This models the checked API; trusted raw slot access is not a security boundary. -/
namespace LeanPoo.Prototype.DescriptorReflection
/-- One effective slot's metadata, after most-specific declaration selection. -/
structure SlotDeclaration (α : Type) where
  descriptor : Descriptor α
  hidden : Bool := false
/-- Metadata inspection neither reads nor validates an instance's slot value. -/
def publicSlots (entries : List (String × SlotDeclaration α)) : List (String × SlotDeclaration α) :=
  entries.filter (fun entry => !entry.2.hidden)
/-- Every entry exposed by ordinary public reflection has visible metadata. -/
theorem publicSlots_visible (entries : List (String × SlotDeclaration α)) (entry)
    (present : entry ∈ publicSlots entries) : entry.2.hidden = false := by
  simpa [publicSlots] using (List.mem_filter.mp present).2
/-- Resolve visibility before selecting a supplied value computation. -/
def readSlot (slot : SlotDeclaration α) (read : Unit → Except String α) : Except String α :=
  if slot.hidden then .error "slot is hidden or undeclared" else do
    let value ← read ()
    slot.descriptor.validate value
/-- Hidden-slot rejection cannot select a user computation. -/
theorem readSlot_hidden (slot : SlotDeclaration α) (read : Unit → Except String α)
    (hidden : slot.hidden = true) : readSlot slot read = .error "slot is hidden or undeclared" := by
  simp [readSlot, hidden]
/-- Cached raw values and hook-produced values must meet CURRENT metadata.
A previous successful read does not establish current descriptor admission. -/
theorem readSlot_valid (slot : SlotDeclaration α) (read : Unit → Except String α) (value : α)
    (accepted : readSlot slot read = .ok value) : slot.descriptor.accepts value = true := by
  cases hidden : slot.hidden with
  | true => simp [readSlot, hidden] at accepted
  | false =>
    cases computed : read () with
    | error message => simp [readSlot, hidden, computed, bind, Except.bind] at accepted
    | ok raw =>
      cases valid : slot.descriptor.accepts raw <;>
        simp [readSlot, hidden, computed, Descriptor.validate, valid, bind, Except.bind] at accepted
      subst value
      exact valid
/-- Validate a proposed value before selecting the native specification write.
This is a single sequential edit; callback effects and concurrency are not modeled. -/
def writeSlot (slot : SlotDeclaration α) (value : α)
    (write : α → Except String State) : Except String State := do
  if slot.hidden then throw "slot is hidden or undeclared"
  let accepted ← slot.descriptor.validate value
  write accepted
/-- Invalid values do not invoke a mutation or invalidate a cache. -/
theorem writeSlot_rejected (slot : SlotDeclaration α) (value : α)
    (write : α → Except String State) (visible : slot.hidden = false)
    (invalid : slot.descriptor.accepts value = false) :
    writeSlot slot value write = .error s!"value rejected by {slot.descriptor.name}" := by
  simp [writeSlot, visible, Descriptor.validate, invalid, bind, Except.bind, throw, throwThe]
/-- Successful checked writes use precisely the admitted proposed value. -/
theorem writeSlot_admitted (slot : SlotDeclaration α) (value : α)
    (write : α → Except String State) (visible : slot.hidden = false)
    (valid : slot.descriptor.accepts value = true) : writeSlot slot value write = write value := by
  simp [writeSlot, visible, Descriptor.validate, valid, bind, Except.bind]
end LeanPoo.Prototype.DescriptorReflection
