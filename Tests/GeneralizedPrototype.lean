import LeanPoo.Prototype.GeneralizedInheritance
import LeanPoo.Deriving.DictionaryCompiler
import LeanPoo.Object.MethodCombinationSemantics

/-! Research example: one protocol owns raw assembly and cooked final self.
C3, nested lenses, standard method execution and exact dictionary bridges remain
existing mechanisms. Finite depth is explicit and is not a termination claim. -/
namespace LeanPoo.Tests.GeneralizedPrototype
open Prototype Prototype.Generalized Object.MethodCombination
abbrev Action := EStateM String (List String)
abbrev Methods := Object.MethodCombination.Methods Int Action Int
structure Billing where
  rate : Int
  methods : Methods := {}
structure Storage where
  billing : Billing
  identity : String
structure Interface where
  rate : Int
  quote : Int → Action Int

derive_dictionary Storage
derive_dictionary Interface

def billingFocus : MonoLens Storage Billing := MonoLens.ofGetSet (·.billing) (fun value raw => {raw with billing := value})
def rateFocus : MonoLens Billing Int := MonoLens.ofGetSet (·.rate) (fun value raw => {raw with rate := value})
def methodsFocus : MonoLens Billing Methods := MonoLens.ofGetSet (·.methods) (fun value raw => {raw with methods := value})
abbrev MethodFragment := Thunk Int → Contribution Int Action Int
abbrev Fragment := Sum Int MethodFragment

def fragmentsProtocol : Protocol Storage Int Fragment where
  cook := fun raw => raw.billing.rate
  compile := sumCompiler
    (lensCompiler (billingFocus.compose rateFocus) (fun value _ _ => value))
    (standardCompiler (billingFocus.compose methodsFocus))

def protocol : Protocol Storage Interface Fragment := fragmentsProtocol.reindexSelf (·.rate)
  (fun raw => ⟨raw.billing.rate, effective raw.billing.methods (fun _ => throw "missing")⟩)

def graph : Prototype.C3.Graph :=
  [("Service",["Audit","Discount"]),("Audit",["Base"]),("Discount",["Base"]),("Base",[])]
def mark (event : String) : Action Unit := modify (· ++ [event])
def method (body : MethodFragment) : Fragment := .inr body
def declarations (rate fee discount limit : Int) (name : String) : List Fragment :=
  if name == "Service" then [
    .inl rate,
    method (fun _ => .around (fun next units => do
      mark "guard"
      if units < 0 || units > limit then throw "units" else next ())),
    method (fun _ => .primary (fun next _ => do mark "fee"; return (← next ()) + fee))]
  else if name == "Audit" then [
    method (fun _ => .around (fun next _ => do mark "enter"; let result ← next (); mark "exit"; return result)),
    method (fun _ => .before (fun _ => mark "audit.before")),
    method (fun _ => .after (fun _ => mark "audit.after"))]
  else if name == "Discount" then [
    method (fun _ => .primary (fun next _ => do mark "discount"; return (← next ()) - discount))]
  else if name == "Base" then [
    .inl 1,
    method (fun self => .primary (fun _ units => do mark "base"; return units * self.get)),
    method (fun _ => .before (fun _ => mark "base.before")),
    method (fun _ => .after (fun _ => mark "base.after"))]
  else []

def base : Storage := ⟨⟨1,{}⟩,"tenant-A"⟩
def summary : EStateM.Result String (List String) Int → Option Int × Option String × List String
  | .ok value ledger => (some value,none,ledger)
  | .error error ledger => (none,some error,ledger)

theorem identity_frame (fragment : Fragment) (self : Thunk Interface) (parent : Thunk Storage) :
    (protocol.compile fragment self parent).identity = parent.get.identity := by
  cases fragment <;> rfl

theorem assembly_identity (fragments : List Fragment) (seed : Storage) (depth : Nat) :
    (protocol.approximate fragments base seed (depth+1)).identity = base.identity :=
  protocol.approximate_frame fragments (·.identity) identity_frame base seed depth

def control (rate fee discount limit units : Int) (depth : Nat) : Option Int × Option String × List String :=
  if depth == 0 then (none,some "missing",["prefix"])
  else if units < 0 || units > limit then (none,some "units",["prefix","guard"])
  else (some (units * (if depth == 1 then 1 else rate) + fee - discount),none,
    ["prefix","guard","enter","audit.before","base.before","fee","discount","base","base.after","audit.after","exit"])

def ordered (rate fee discount limit : Int) : List Fragment :=
  ["Service","Audit","Discount","Base"].flatMap (declarations rate fee discount limit)

theorem protocol_step (fragments : List Fragment) :
    protocol.step fragments = fragmentsProtocol.step fragments :=
  fragmentsProtocol.step_reindexSelf (fun self : Interface => self.rate)
    (fun raw => ⟨raw.billing.rate, effective raw.billing.methods (fun _ => throw "missing")⟩) (fun _ => rfl) fragments

theorem service_stable (rate fee discount limit : Int) :
    protocol.approximate (ordered rate fee discount limit) base base 3 =
      protocol.approximate (ordered rate fee discount limit) base base 2 := by
  simp only [Protocol.approximate, protocol_step]
  exact fragmentsProtocol.stable_two _ base base rate (fun _ => rfl)

theorem service_derivation : Prototype.C3.GraphDerivation graph "Service" ["Service","Audit","Discount","Base"] := by
  have leaf : LeanPoo.C4.Precedence.Trace [[]] [] := .done rfl
  have baseDerived : Prototype.C3.GraphDerivation graph "Base" ["Base"] :=
    .node (entry := ("Base",[])) (by decide) .nil (.ofCertified leaf) leaf
  have parentTrace : LeanPoo.C4.Precedence.Trace [["Base"],["Base"]] ["Base"] :=
    .step (by decide) (.done (by decide))
  have audit : Prototype.C3.GraphDerivation graph "Audit" ["Audit","Base"] :=
    .node (entry := ("Audit",["Base"])) (by decide) (.cons baseDerived .nil) (.ofCertified parentTrace) parentTrace
  have discount : Prototype.C3.GraphDerivation graph "Discount" ["Discount","Base"] :=
    .node (entry := ("Discount",["Base"])) (by decide) (.cons baseDerived .nil) (.ofCertified parentTrace) parentTrace
  have merged : LeanPoo.C4.Precedence.Trace
      [["Audit","Base"],["Discount","Base"],["Audit","Discount"]] ["Audit","Discount","Base"] :=
    .step (by decide) (.step (by decide) (.step (by decide) (.done (by decide))))
  exact .node (entry := ("Service",["Audit","Discount"])) (by decide)
    (.cons audit (.cons discount .nil)) (.ofCertified merged) merged

theorem plan_stable (rate fee discount limit : Int)
    (plan : Plan protocol graph (declarations rate fee discount limit) "Service") :
    protocol.approximate plan.fragments base base 3 = protocol.approximate plan.fragments base base 2 := by
  rw [plan.fragments_reference _ service_derivation]
  exact service_stable rate fee discount limit

theorem quote_all_depth (rate fee discount limit : Int)
    (plan : Plan protocol graph (declarations rate fee discount limit) "Service")
    (units : Int) (ledger : List String) (extra : Nat) :
    (((plan.observe base base (2 + extra)).quote units).run ledger) =
      (((protocol.closeAt plan.fragments base base 2 (plan_stable rate fee discount limit plan)).interface.quote units).run ledger) := by
  have stable := protocol.stable plan.fragments base base 2 (plan_stable rate fee discount limit plan).symm extra
  unfold Plan.observe Protocol.observe
  rw [stable]
  rfl

def run : IO Unit := do
  let mut count := 0
  for rate in [2,5] do
    for fee in [0,2] do
      for discount in [0,1] do
        for limit in [0,3,10] do
          let plan ← IO.ofExcept ((protocol.prepare graph (declarations rate fee discount limit) "Service").mapError reprStr)
          let rawPlan := plan.transport Storage.dictionaryBridge (DictionaryBridge.identity Interface)
          let bothPlan := plan.transport Storage.dictionaryBridge Interface.dictionaryBridge
          for units in [-1,0,2,4,7] do
            for depth in [0,1,2] do
              let expected := control rate fee discount limit units depth
              let original := plan.observe base base depth
              let rawOnly := rawPlan.observe (Storage.toFields base) (Storage.toFields base) depth
              let both := Interface.fromFields (bothPlan.observe (Storage.toFields base) (Storage.toFields base) depth)
              for service in [original,rawOnly,both] do
                let actual := summary ((service.quote units).run ["prefix"])
                unless actual == expected do
                  throw (IO.userError s!"generalized control {rate}/{fee}/{discount}/{limit}/{units}/{depth}: {repr actual} != {repr expected}")
              let assembled := protocol.approximate plan.fragments base base depth
              unless assembled.identity == "tenant-A" && assembled.billing.rate == (if depth == 0 then 1 else rate) do
                throw (IO.userError "raw metadata/frame control")
              count := count + 1
  unless count == 360 do throw (IO.userError "inventory")
  -- Forward the existing C3 error exactly, including cycles and inconsistent orders.
  for (candidate,root) in [
      ([("Loop",["Loop"])],"Loop"),
      ([("X",["A","B"]),("Y",["B","A"]),("Z",["X","Y"]),("A",[]),("B",[])],"Z"),
      (graph,"Missing")] do
    let source := Prototype.C3.linearize candidate root
    let prepared := (protocol.prepare candidate (declarations 2 0 0 3) root).map (·.precedence)
    unless reprStr prepared == reprStr source && source.toOption.isNone do throw (IO.userError "C3 refusal forwarding")
  IO.println s!"GENERALIZED-PROTOTYPE-OK cases={count} executions={count*3} independent-results/errors/complete-traces raw/cooked-bridges C3-refusals"
#eval run

-- A checked closure example is separate from any chosen unfolding budget.
def scalar : Protocol Nat Nat Nat := ⟨id, fun value => DelayedProto.constant value⟩
def scalarClosed (value : Nat) : Closed scalar [value] 0 :=
  scalar.closeAt [value] 0 0 1 (by rfl)
example (value : Nat) : (scalarClosed value).interface = value := rfl
example (value : Nat) : scalar.observe [value] 0 0 10 = value := rfl

-- Terminal method bodies need not call a failing inherited method body.
def functionFocus : MonoLens ((Nat → Nat) × String) (Nat → Nat) :=
  MonoLens.ofGetSet Prod.fst (fun value raw => (value,raw.2))
def terminal := lensCompiler functionFocus (Cooked := Unit) (fun (value : Nat) _ _ => fun _ => value)
#guard (terminal 9 (Thunk.mk fun _ => ()) (Thunk.mk fun _ => ((fun _ => panic! "inherited called"),"keep"))).1 0 == 9
#print axioms quote_all_depth
#print axioms plan_stable
#print axioms Protocol.stable_two
#print axioms Protocol.stable
#print axioms Closed.assembly
#print axioms Closed.transport_interface
#print axioms Plan.fragments_reference
#print axioms Protocol.prepare_error
#print axioms Protocol.approximate_transport
#print axioms Protocol.observe_transport
#print axioms Protocol.assemble_frame
end LeanPoo.Tests.GeneralizedPrototype
