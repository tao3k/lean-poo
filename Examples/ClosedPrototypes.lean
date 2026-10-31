import LeanPoo.Prototype.FocusedClosure
import LeanPoo.Object.MethodCombination

/-! Controlled non-record closure and universal custom product-lens laws. Native
vectors implement the same immutable layout; finite runtime checks remain separate. -/
namespace LeanPoo.Examples.ClosedPrototypes
open Prototype Prototype.Generalized Object.MethodCombination
/-- Only comparable scalar data lives in raw state; audit is independent. -/
abbrev Raw := (Nat × Nat × Nat) × String
/-- Existing standard methods consume the current units/rate/fee/reserve row. -/
abbrev Row := Nat × Nat × Nat × Nat
/-- Cooking can allocate a callable interface without comparing closures as raw data. -/
structure View where
  rate : Nat
  fee : Nat
  reserve : Nat
  charge : Nat → Except String Nat
/-- Immutable method policy is shared outside raw construction, as in Gerbil. -/
def methods : Methods Row (Except String) Nat :=
  {primary := [fun _ row => .ok (row.1 * row.2.1 + row.2.2.1 + row.2.2.2)],
   around := [fun next _ => do return 2 * (← next ())]}
/-- Same standard method interpreter, with one current argument row per invocation. -/
def cook (raw : Raw) : View :=
  ⟨raw.1.1,raw.1.2.1,raw.1.2.2,fun units =>
    effective methods (fun _ => .error "no primary method") (units,raw.1.1,raw.1.2.1,raw.1.2.2)⟩
/-- A reusable custom product getter, paired with a persistent setter. -/
def firstGet (source : A × B) : A := source.1
/-- Replacement preserves the complete second component. -/
def firstPut (value : A) (source : A × B) : A × B := (value,source.2)
/-- All three laws hold for every product value and every focus replacement. -/
theorem firstLaws : LensLaws (firstGet : A × B → A) firstPut := by
  constructor
  · intro source; cases source; rfl
  · intro source value; rfl
  · intro source first second; rfl
/-- A nested rate getter corresponds to native composed vector lenses. -/
def rateGet (raw : Raw) := raw.1.1
/-- Persistent update retains the two other scalars and outer audit. -/
def ratePut (value : Nat) (raw : Raw) : Raw := ((value,raw.1.2),raw.2)
/-- The composition theorem discharges a real nested custom lens. -/
theorem rateLaws : LensLaws rateGet ratePut := LensLaws.compose firstLaws firstLaws
/-- The second scalar is another custom focus on the same non-record carrier. -/
def feeGet (raw : Raw) := raw.1.2.1
/-- The fee setter preserves rate, reserve and audit. -/
def feePut (value : Nat) (raw : Raw) : Raw := ((raw.1.1,value,raw.1.2.2),raw.2)
/-- Concrete laws quantify universally, unlike finite native sample controls. -/
theorem feeLaws : LensLaws feeGet feePut := by
  constructor
  · intro source; rcases source with ⟨⟨rate,fee,reserve⟩,audit⟩; rfl
  · intro source value; rfl
  · intro source first second; rfl
/-- The final focus carries reserve, derived from the preceding self fee. -/
def reserveGet (raw : Raw) := raw.1.2.2
/-- Raw persistence permits structural adjacent-state equality checking. -/
def reservePut (value : Nat) (raw : Raw) : Raw := ((raw.1.1,raw.1.2.1,value),raw.2)
/-- All three replacement laws also hold for the deepest component. -/
theorem reserveLaws : LensLaws reserveGet reservePut := by
  constructor
  · intro source; rcases source with ⟨⟨rate,fee,reserve⟩,audit⟩; rfl
  · intro source value; rfl
  · intro source first second; rfl
/-- Three explicit dependencies reuse the already-proved generalized lens compiler. -/
def partsAt (rate : Nat) : List (Generalized.Fragment Raw View) :=
  [⟨Nat,Nat,MonoLens.ofGetSet rateGet ratePut,fun value _ _ => value,rate⟩,
   ⟨Nat,Nat,MonoLens.ofGetSet feeGet feePut,fun value self _ => value + self.get.rate,3⟩,
   ⟨Nat,Nat,MonoLens.ofGetSet reserveGet reservePut,fun value self _ => value + self.get.fee,2⟩]
/-- The original local service retains its ten-unit rate policy. -/
def parts := partsAt 10
/-- Raw base has no methods or synthesized function identities. -/
def base : Raw := ((0,0,0),"audit")
/-- Three advances settle the chain from ANY seed; audit comes from the base. -/
example (seed : Raw) : (fragmentProtocol cook).approximate parts base seed 3 = ((10,13,15),"audit") := rfl
/-- Four raw evaluations include the final adjacent equality verification. -/
example : (closeWithin (fragmentProtocol cook) parts base base 4).map
    (fun result => (result.steps,result.closed.raw)) = .ok (4,((10,13,15),"audit")) := rfl
/-- A successful closed raw state cooks to the expected actual method result. -/
example : ((closeWithin (fragmentProtocol cook) parts base base 4).map
    (fun result => result.closed.interface.charge 2)) = .ok (.ok 96) := rfl
/-- Budget exhaustion is a refusal, even for a workflow that would settle later. -/
example : (closeWithin (fragmentProtocol cook) parts base base 3).map (fun _ => ()) =
    .error "closure budget exhausted" := rfl
/-- Replacing a value with its own view preserves the independent audit universally. -/
example (raw : Raw) : ratePut (rateGet raw) raw = raw := rateLaws.get_put raw
/-- An absolute-value setter is not a lawful Int focus, even if positive samples pass. -/
example : ¬ LensLaws (fun source : Int × String => source.1)
    (fun value source => ((value.natAbs : Int),source.2)) := by
  intro laws
  have impossible := laws.put_get (0,"audit") (-1)
  contradiction
/-- Two non-record service carriers share an independent outer tenant/audit frame. -/
abbrev Family := Raw × Raw × String
/-- Focus the left recursively closed service. -/
def leftGet (whole : Family) : Raw := whole.1
/-- Persistent left replacement preserves the sibling and shared frame. -/
def leftPut (value : Raw) (whole : Family) : Family := (value,whole.2)
/-- Focus the second service through the other product branch. -/
def rightGet (whole : Family) : Raw := whole.2.1
/-- Persistent right replacement preserves the first service and shared frame. -/
def rightPut (value : Raw) (whole : Family) : Family := (whole.1,value,whole.2.2)
/-- The left custom lens is universally lawful. -/
theorem leftLaws : LensLaws leftGet leftPut := firstLaws
/-- The right custom lens is universally lawful. -/
theorem rightLaws : LensLaws rightGet rightPut := by
  constructor
  · intro source; rcases source with ⟨left,right,audit⟩; rfl
  · intro source value; rfl
  · intro source first second; rfl
/-- Independence needs an explicit proof, beyond the separate lens laws. -/
theorem servicesIndependent : LensIndependent leftGet leftPut rightGet rightPut :=
  ⟨fun _ _ => rfl,fun _ _ => rfl,fun _ _ _ => rfl⟩
/-- A combined view/replacement for both services also obeys all three laws. -/
example : LensLaws (fun whole => (leftGet whole,rightGet whole))
    (fun pair whole => rightPut pair.2 (leftPut pair.1 whole)) :=
  leftLaws.pair rightLaws servicesIndependent
/-- Name the settled raw carrier so nested workflows do not repeatedly unfold
proof-carrying closure searches during kernel conversion. -/
def settled (rate : Nat) : Raw := ((rate,3+rate,2+(3+rate)),"audit")
/-- Each local certificate retains the same actual fixed equation and four steps. -/
def certificate (rate : Nat) : BoundedClosed (fragmentProtocol cook) (partsAt rate) base :=
  ⟨⟨settled rate,by rfl⟩,4⟩
/-- Check the shared left search once; later family proofs reuse an opaque theorem. -/
theorem close10 : closeWithin (fragmentProtocol cook) parts base base 4 = .ok (certificate 10) := rfl
/-- Sequential local closures are revalidated against ONE final wider raw carrier. -/
def closeFamily (seed : Family) (rightBudget : Nat := 4) : Except String Family := do
  let left ← closeFocused (fragmentProtocol cook) parts leftGet leftPut base seed 4
  let whole ← closeFocused (fragmentProtocol cook) (partsAt 20) rightGet rightPut base left rightBudget
  validateFocused (fragmentProtocol cook) parts leftGet base whole
  validateFocused (fragmentProtocol cook) (partsAt 20) rightGet base whole
  return whole
/-- Cooking retains both actual standard effective methods and a shared audit. -/
def reportFamily (whole : Family) (units : Nat) : Except String (Nat × Nat × Nat × String) := do
  let left ← (cook whole.1).charge units
  let right ← (cook whole.2.1).charge units
  return (left,right,left+right,whole.2.2)
/-- Compose the checked local searches before checking the two final equations.
This prevents a nested rfl from expanding both proof-carrying searches repeatedly. -/
theorem familyResult : closeFamily (base,base,"tenant audit") =
    .ok (settled 10,settled 20,"tenant audit") := by
  simp only [closeFamily,closeFocused,leftGet,rightGet,leftPut,rightPut,close10,Except.map]
  rfl
/-- A budget refusal remains a refusal after the successful first local closure. -/
theorem familyRefused : closeFamily (base,base,"tenant audit") 0 =
    .error "closure budget exhausted" := by
  simp only [closeFamily,closeFocused,leftGet,rightGet,leftPut,rightPut,close10,Except.map]
  rfl
/-- The complex family closes and cooks the same outputs as the native vectors. -/
example : ((closeFamily (base,base,"tenant audit")).bind (fun whole => reportFamily whole 2)) =
    .ok (96,176,272,"tenant audit") := by rw [familyResult]; rfl
/-- The second refusal cannot publish the already-completed first component. -/
example (old : Family) : publishClosed old (closeFamily (base,base,"tenant audit") 0) = old := by rw [familyRefused]; rfl
/-- ANY accepted left closure preserves both sibling and shared frame. -/
example (seed result : Family) (accepted : closeFocused (fragmentProtocol cook) parts
    leftGet leftPut base seed 4 = .ok result) : result.2 = seed.2 :=
  closeFocused_frame (fragmentProtocol cook) parts leftGet leftPut Prod.snd
    (fun _ _ => rfl) base seed result 4 accepted
/-- Later right replacement preserves a proved left equation for EVERY value. -/
example (whole : Family) (value : Raw)
    (fixed : (fragmentProtocol cook).step parts (leftGet whole) base = leftGet whole) :
    (fragmentProtocol cook).step parts (leftGet (rightPut value whole)) base = leftGet (rightPut value whole) :=
  fixed_preserved _ _ _ _ servicesIndependent.left_view _ _ _ fixed
/-- Two individually lawful identity lenses overlap and are NOT independent. -/
example : ¬ LensIndependent (id : Nat → Nat) (fun value _ => value)
    id (fun value _ => value) := by
  intro h
  have impossible := h.left_view 0 1
  contradiction
/-- A later conflicting closure through the SAME lawful lens fails final admission. -/
example : (do
    let first ← closeFocused (fragmentProtocol cook) parts leftGet leftPut base (base,base,"audit") 4
    let second ← closeFocused (fragmentProtocol cook) (partsAt 20) leftGet leftPut base first 4
    validateFocused (fragmentProtocol cook) parts leftGet base second) =
    .error "later focused update invalidated an earlier raw closure" := by
  simp only [closeFocused,leftGet,leftPut,close10,Except.map]
  rfl
/-- A scalar prototype uses the SAME generalized protocol alongside a vector-like service. -/
def scalarProtocol : Protocol Nat Nat Nat := ⟨id,fun value _ _ => value⟩
/-- Distinct raw/focus types need no shared representation tag or erased interpreter. -/
example : (do
    let first ← closeFocused (fragmentProtocol cook) parts (fun raw : Raw × Nat × String => raw.1)
      (fun value raw => (value,raw.2)) base (base,0,"audit") 4
    let whole ← closeFocused scalarProtocol [7] (fun raw : Raw × Nat × String => raw.2.1)
      (fun value raw => (raw.1,value,raw.2.2)) 0 first 2
    validateFocused (fragmentProtocol cook) parts Prod.fst base whole
    validateFocused scalarProtocol [7] (fun raw : Raw × Nat × String => raw.2.1) 0 whole
    return whole) = .ok (((10,13,15),"audit"),7,"audit") := by
  simp only [closeFocused,Except.map]
  rfl
#print axioms LensLaws.compose
#print axioms rateLaws
#print axioms feeLaws
#print axioms reserveLaws
#print axioms closeWithin_fixed
#print axioms closeWithin_bound
#print axioms closeWithin_reached
#print axioms closeWithin_forever
#print axioms BoundedClosed.stable
#print axioms LensLaws.pair
#print axioms servicesIndependent
#print axioms closeFocused_fixed
#print axioms closeFocused_reached
#print axioms closeFocused_frame
#print axioms validateFocused_sound
#print axioms fixed_preserved
end LeanPoo.Examples.ClosedPrototypes
