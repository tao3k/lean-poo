import LeanPoo.Prototype.GeneralizedClosure
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
def parts : List (Generalized.Fragment Raw View) :=
  [⟨Nat,Nat,MonoLens.ofGetSet rateGet ratePut,fun value _ _ => value,10⟩,
   ⟨Nat,Nat,MonoLens.ofGetSet feeGet feePut,fun value self _ => value + self.get.rate,3⟩,
   ⟨Nat,Nat,MonoLens.ofGetSet reserveGet reservePut,fun value self _ => value + self.get.fee,2⟩]
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
#print axioms LensLaws.compose
#print axioms rateLaws
#print axioms feeLaws
#print axioms reserveLaws
#print axioms closeWithin_fixed
#print axioms closeWithin_bound
#print axioms closeWithin_reached
#print axioms closeWithin_forever
#print axioms BoundedClosed.stable
end LeanPoo.Examples.ClosedPrototypes
