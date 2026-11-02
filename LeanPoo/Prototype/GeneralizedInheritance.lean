import LeanPoo.Prototype.GeneralizedPrototype
import LeanPoo.Object.C3
import LeanPoo.Object.MethodCombination

/-! Certified C3 preparation and standard method fragments for the generalized
protocol. This is future-work development, not a new source-closure claim. -/
namespace LeanPoo.Prototype.Generalized
universe u v w

/-- Standard contributions read the cooked final self when they are installed.
Execution remains owned by the existing method-combination interpreter. -/
def standardCompiler {Raw Cooked Receiver Result : Type} {M : Type → Type}
    (focus : MonoLens Raw (Object.MethodCombination.Methods Receiver M Result)) :
    Compiler Raw Cooked (Thunk Cooked → Object.MethodCombination.Contribution Receiver M Result) :=
  lensCompiler focus (fun contribution self inherited => inherited.get.prepend (contribution self))

theorem standardCompiler_frame {Raw Cooked Receiver Result Frame : Type} {M : Type → Type}
    (focus : MonoLens Raw (Object.MethodCombination.Methods Receiver M Result))
    (frame : Raw → Frame) (preserved : ∀ value raw, frame (focus.modify (fun _ => value) raw) = frame raw)
    (fragment : Thunk Cooked → Object.MethodCombination.Contribution Receiver M Result)
    (self : Thunk Cooked) (parent : Thunk Raw) :
    frame (standardCompiler focus fragment self parent) = frame parent.get :=
  lensCompiler_frame focus _ frame preserved fragment self parent

/-- Alternative policies share the same focus protocol; policy interpretation
is supplied by cooking and remains the existing simpleEffective operation. -/
def simpleCompiler {Raw Cooked Receiver Item Result : Type} {M : Type → Type}
    (focus : MonoLens Raw (Object.MethodCombination.SimpleMethods Receiver M Item Result)) :
    Compiler Raw Cooked (Thunk Cooked → Object.MethodCombination.SimpleContribution Receiver M Item Result) :=
  lensCompiler focus (fun contribution self inherited => inherited.get.prepend (contribution self))

/-- The graph receipt fixes source order before fragment elaboration. -/
structure Plan (protocol : Protocol Raw Cooked Fragment) (graph : C3.Graph)
    (declarations : String → List Fragment) (root : String) where
  precedence : List String
  valid : C3.linearize graph root = .ok precedence

def Protocol.prepare (protocol : Protocol Raw Cooked Fragment) (graph : C3.Graph)
    (declarations : String → List Fragment) (root : String) :
    Except LeanPoo.C4.Error (Plan protocol graph declarations root) :=
  match valid : C3.linearize graph root with
  | .error error => .error error
  | .ok order => .ok ⟨order,valid⟩

variable {protocol : Protocol Raw Cooked Fragment} {graph : C3.Graph}
variable {declarations : String → List Fragment} {root : String}

def Plan.fragments (plan : Plan protocol graph declarations root) : List Fragment :=
  plan.precedence.flatMap declarations

def Plan.program (plan : Plan protocol graph declarations root) : DelayedProto Cooked Raw Raw :=
  protocol.assemble plan.fragments

def Plan.observe (plan : Plan protocol graph declarations root) (base seed : Raw) (depth : Nat) : Cooked :=
  protocol.observe plan.fragments base seed depth

theorem Plan.derivation (plan : Plan protocol graph declarations root) :
    C3.GraphDerivation graph root plan.precedence := C3.linearize_derivation _ _ _ plan.valid

theorem Plan.fragments_reference (plan : Plan protocol graph declarations root)
    (order : List String) (derived : C3.GraphDerivation graph root order) :
    plan.fragments = order.flatMap declarations := by
  rw [← plan.derivation.unique derived]
  rfl

theorem Protocol.prepare_error (protocol : Protocol Raw Cooked Fragment) (graph : C3.Graph)
    (declarations : String → List Fragment) (root : String) (error : LeanPoo.C4.Error)
    (refused : C3.linearize graph root = .error error) :
    protocol.prepare graph declarations root = .error error := by
  unfold Protocol.prepare
  split <;> simp_all

def Plan.transport (plan : Plan protocol graph declarations root)
    (raw : DictionaryBridge Raw NewRaw) (interface : DictionaryBridge Cooked NewCooked) :
    Plan (protocol.transport raw interface) graph declarations root := ⟨plan.precedence,plan.valid⟩

theorem Plan.transport_program (plan : Plan protocol graph declarations root)
    (raw : DictionaryBridge Raw NewRaw) (interface : DictionaryBridge Cooked NewCooked) :
    (plan.transport raw interface).program =
      DictionaryBridge.toDelayedPrototype interface raw raw plan.program :=
  protocol.assemble_transport raw interface plan.fragments

theorem Plan.transport_observe (plan : Plan protocol graph declarations root)
    (raw : DictionaryBridge Raw NewRaw) (interface : DictionaryBridge Cooked NewCooked)
    (base seed : Raw) (depth : Nat) :
    (plan.transport raw interface).observe (raw.toFields base) (raw.toFields seed) depth =
      interface.toFields (plan.observe base seed depth) :=
  protocol.observe_transport raw interface plan.fragments base seed depth

end LeanPoo.Prototype.Generalized
