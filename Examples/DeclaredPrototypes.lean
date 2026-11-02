import LeanPoo.Prototype.GeneralizedDeclaration
import LeanPoo.Object.MethodCombination

/-! Nested product tuples model the native nested-vector carrier. Heterogeneous
scalar/method fragments share one macro/protocol; a second carrier is a function. -/
namespace LeanPoo.Examples.DeclaredPrototypes
open Prototype Prototype.Generalized Object.MethodCombination
/-- The third local component is a method group, unlike the first two scalars. -/
abbrev Groups := Methods Nat (Except String) Nat
/-- Outer audit data is independent of the nested heterogeneous computation. -/
abbrev Raw := (Nat × Nat × Groups) × String
/-- The consumed interface is callable and keeps scalar fields available to self. -/
structure View where
  rate : Nat
  fee : Nat
  charge : Nat → Except String Nat
/-- Cooking reuses standard method combination; no new method evaluator is needed. -/
def cook (raw : Raw) : View :=
  ⟨raw.1.1,raw.1.2.1,effective raw.1.2.2 (fun _ => .error "no declared primary")⟩
/-- Functional nested lenses preserve all components outside their own focus. -/
def rateFocus : MonoLens Raw Nat := MonoLens.ofGetSet (·.1.1)
  (fun value raw => ((value,raw.1.2),raw.2))
/-- The dependent fee updates only the second nested scalar. -/
def feeFocus : MonoLens Raw Nat := MonoLens.ofGetSet (·.1.2.1)
  (fun value raw => ((raw.1.1,value,raw.1.2.2),raw.2))
/-- Method storage is selected with the same lens protocol. -/
def methodsFocus : MonoLens Raw Groups := MonoLens.ofGetSet (·.1.2.2)
  (fun value raw => ((raw.1.1,raw.1.2.1,value),raw.2))
/-- Each descriptor existentially packages its own method/focus type. -/
def rate : Generalized.Fragment Raw View := ⟨Nat,Nat,rateFocus,fun amount _ _ => amount,10⟩
/-- The wrapper reads only prior-stage cooked self, not a recursive native knot. -/
def fee : Generalized.Fragment Raw View :=
  ⟨Nat,Nat,feeFocus,fun amount self _ => amount + self.get.rate,3⟩
/-- Lift one typed qualified method producer into raw grouped storage. -/
def method (producer : Thunk View → Contribution Nat (Except String) Nat) : Generalized.Fragment Raw View :=
  ⟨Groups,Thunk View → Contribution Nat (Except String) Nat,methodsFocus,
    fun source self inherited => inherited.get.prepend (source self),producer⟩
/-- The same source stream contains scalars, an around wrapper and a primary. -/
def entries : List (FragmentEntry Raw View) :=
  [("rate",rate),("fee",fee),
   ("around",method (fun _ => .around (fun next _ => do return 2 * (← next ())))),
   ("primary",method (fun self => .primary (fun _ units => .ok (units * self.get.rate + self.get.fee))))]
/-- The concrete source has distinct reflection labels; targets can still overlap. -/
def declaration : FragmentDeclaration Raw View := ⟨entries,by decide⟩
/-- Empty raw method storage is not an invented callable primary. -/
def base : Raw := ((0,0,{}),"audit")
/-- Current-context finalization precedes raw construction and cooked observation. -/
def candidate (approved : Bool) := elaborateFragments [fun (_ : Bool) => .ok entries] approved
  (fun current parts => if current then .ok parts else .error "generalized declaration refused")
/-- Only the complete approved source can provide declaration labels. -/
example : (candidate true).map (fun value => value.entries.map Prod.fst) =
    .ok ["rate","fee","around","primary"] := rfl
/-- Refusal returns no partially admitted fragment declaration. -/
example : (candidate false).map (fun _ => ()) = .error "generalized declaration refused" := rfl
/-- The example's triangular dependency yields 46 after two finite stages. -/
example : (declaration.observe cook base base 2).charge 2 = .ok 46 := rfl
/-- Three stages remove seed dependence for every invocation argument, even if
the seed's method storage differs. This is an observation law, not raw closure. -/
example (seed : Raw) (units : Nat) : (declaration.observe cook base seed 3).charge units =
    .ok (2 * (units * 10 + 13)) := rfl
/-- The three actual lenses preserve the independent audit frame universally. -/
example (raw : Raw) (value : Nat) : (rateFocus.modify (fun _ => value) raw).2 = raw.2 := rfl
/-- A non-record callable can itself be the raw AND cooked representation. -/
def callableFocus : MonoLens (Nat → Nat) (Nat → Nat) := MonoLens.ofGetSet id (fun value _ => value)
/-- The wrapper constructs a function without executing its inherited function. -/
def callable (factor : Nat) : Generalized.Fragment (Nat → Nat) (Nat → Nat) :=
  ⟨Nat → Nat,Nat,callableFocus,fun amount _ inherited input => amount * input + inherited.get input,factor⟩
/-- The identical generic protocol compiles a function carrier without record slots. -/
example : (fragmentProtocol id).observe [callable 2,callable 3] (fun _ => 7) (fun _ => 7) 1 4 = 27 := rfl
#print axioms Fragment.compile_eq
#print axioms Fragment.compile_frame
#print axioms fragments_frame
#print axioms elaborateFragments_source
end LeanPoo.Examples.DeclaredPrototypes
