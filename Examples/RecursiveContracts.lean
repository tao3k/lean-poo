import LeanPoo.Functional.RecursiveValidation
import LeanPoo.Functional.FunctionValidation

/-! Two actual cyclic object references (interpreted by owner-scoped identities),
productive computed handlers, a positive Boolean cycle, safe recursive memo,
whole-graph refinement and exact publication. Host pointer/receiver correspondence,
revision guards, local callback termination and external effects are not proved. -/
namespace LeanPoo.Examples.RecursiveContracts
open Functional Functional.ObjectContract Functional.DeclarativeMetadata
open Prototype.Recursive

/-- Both indices belong to the finite declared catalog; missing names are a host
preflight error, not an axiom permitting an unregistered recursive target. -/
abbrev Node := Fin 2

/-- Opposite object references make a genuine two-node cycle. -/
def peer (node : Node) : Node := if node = 0 then 1 else 0

/-- Decreasing requests terminate even though the component references form a cycle. -/
def program : Generator (Node × Nat) Int := fun (node,count) =>
  if count = 0 then .value 0
  else (Interaction.call (peer node,count-1) .value).map (fun value => value + if node = 0 then 2 else 3)

abbrev Memo := Cached.Cache program

/-- Function argument rows retain dynamic Boolean/Integer distinctions. -/
inductive Scalar where
  | integer : Int → Scalar
  | flag : Bool → Scalar

abbrev Handler := Memo × Scalar → Except String (Int × Memo)

/-- Explicit source evaluation preserves diagnostic/source distinctions. No cache
is returned on an incomplete run, so it cannot become an admitted result. -/
def call (node : Node) (memo : Memo) (count : Int) : Except String (Int × Memo) := do
  if count < 0 || count > 32 then throw "argument"
  let (receipt,next) ← (Cached.runCertified program (node,count.toNat) 256 memo).mapError
    (fun diagnostic => match diagnostic.diagnostic with | .cycle _ => "cycle" | .budgetExhausted => "budget")
  match receipt.result with
  | .error cause => throw cause
  | .value value => pure (value,next)

/-- Existing Function validation supplies the callable boundary; the recursive
machine owns request closure and the caller explicitly threads its source memo. -/
def handler (node : Node) : Handler :=
  FunctionValidation.wrap
    (fun (memo,value) => match value with
      | .integer count => .ok (memo,count) | .flag _ => .error "integer argument")
    Except.ok (fun (memo,count) => call node memo count)

/-- Genuine positive computed equations: left = true OR right, right = left. -/
def equations : PositiveEquations.Equations 2 := fun index =>
  if index = 0 then .either (.literal true) (.read 1) else .read 0

/-- The existing least-closure solver supplies values, never a chosen warm seed. -/
def active (node : Node) : Bool := (PositiveEquations.close equations).value node

/-- Payload fields correspond to delayed handler and computed peer-handler.
All function values are typed closures; no equality over arbitrary functions is used. -/
structure Payload where
  handler : Handler
  peerHandler : Handler
  active : Bool

abbrev Graph := RecursiveValidation.Graph 2 Nat Payload

/-- Owner-scoped canonical identities model distinct graph versions. Their
correspondence to actual host pointer identity is an explicit adapter premise. -/
def canonical (owner : Nat) (node : Node) : Nat := owner*100+10+node.val

/-- Install reference backedges through the complete canonical receiver map. -/
def edges (node : Node) : List Node := [peer node]

/-- Actual node payloads use checked wrappers and the same safe final program. -/
def normalize (node : Node) : Except String Payload := .ok ⟨handler node,handler (peer node),active node⟩

/-- Final node obligations inspect the whole assembled graph, including canonical
links and positive computed flags. No active node is accepted as a substitute. -/
def admit (graph : Graph) (node : Node) : Except String Unit :=
  if (graph.payload node).active && graph.links node == [graph.canonical (peer node)] then .ok ()
  else .error "graph obligation"

/-- A finite graph factory closes all nodes before exposing any canonical root. -/
def close (owner : Nat) := RecursiveValidation.close (canonical owner) edges (fun _ => .ok ()) normalize admit

/-- This concrete two-hop object cycle preserves the final root's identity. -/
theorem peer_peer (node : Node) : peer (peer node) = node := by
  have all : ∀ index : Fin 2, peer (peer index) = index := by decide
  exact all node

/-- Root refinement composes canonical cycles with already admitted node payloads. -/
def schema : ObjectContract.Contract Graph String Unit String :=
  refine
    {view := ⟨fun _ => true,fun _ => true,fun _ => [],fun _ _ => none⟩
     fields := [], strict := true, constraints := [], validInventory := Or.inl rfl
     obligations := fun _ _ => []}
    (fun graph path => if graph.links 0 == [graph.canonical 1] && graph.links 1 == [graph.canonical 0]
      then [] else [.rejected path "backedge"])

/-- Application evidence names the actual root owner and current context. -/
structure Result where
  subject : Nat
  descriptor : Nat
  context : Nat
  total : Int
  deriving Repr, DecidableEq

/-- Projection binds all associations, without authenticating producer identity. -/
def view (value : Result) : Nat × Nat × Nat := (value.subject,value.descriptor,value.context)

/-- Invocation policy remains active independently of the exact-reference rule. -/
def invocation : Contract Unit Nat Result where
  input := ⟨"root",fun _ => True,fun _ => isTrue True.intro⟩
  output := ⟨"result",fun _ => True,fun _ => isTrue True.intro⟩
  meaning := fun _ _ _ => True
  decide := fun _ _ _ => isTrue True.intro
  rule := .atom ()

/-- Execute the matching 10+8 service workflow, shared completed memo, guarded
arguments, incomplete/eager-cycle refusal, remote/shape refusal and bound retry. -/
def test : Except String Unit := do
  match RecursiveValidation.checkCatalog 8 ["left","right"] ["right","left"] with
  | .ok () => pure () | _ => throw "catalog refused"
  match RecursiveValidation.checkCatalog 8 ["left"] ["missing"] with
  | .error .missingReference => pure () | _ => throw "missing target admitted"
  let graph ← close 1
  unless (diagnose schema graph []).isEmpty do throw "root refinement"
  let root := graph.payload 0
  let (first,next) ← root.handler ({},.integer 4)
  let (second,reused) ← root.peerHandler (next,.integer 3)
  unless first == 10 && second == 8 && reused.statistics.hits > next.statistics.hits do throw "memo workflow"
  match root.handler ({},.flag false) with
  | .error "integer argument" => pure () | _ => throw "Function guard bypassed"
  match Cached.runCertified program (0,4) 0 {} with
  | .error .budgetExhausted => pure () | _ => throw "budget accepted"
  let loop : Generator Nat Int := fun input => .call input .value
  match Cached.runCertified loop 0 20 {} with
  | .error (.cycle _ _) => pure () | _ => throw "eager cycle accepted"
  match RecursiveValidation.close (canonical 1) edges (fun _ => .ok ()) normalize (fun _ node =>
      if node = 1 then .error "remote refusal" else .ok ()) with
  | .error "remote refusal" => pure () | _ => throw "remote node skipped"
  match RecursiveValidation.close (canonical 1) edges (fun node => if node = 1 then .error "shape" else .ok ()) normalize admit with
  | .error "shape" => pure () | _ => throw "shape skipped"
  let current ← close 2
  let reference := current.canonical 0
  let bound := invocation.bindEvidence reference 7 5 view
  let produce (subject context : Nat) (_ : Nat) : Except String (Result × Nat) := .ok (⟨subject,7,context,first+second⟩,6)
  match bound.publish 5 (produce (graph.canonical 0) 5) reference with
  | (.error .logic,5) => pure () | _ => throw "old graph evidence accepted"
  match bound.publish 5 (produce reference 4) reference with
  | (.error .logic,5) => pure () | _ => throw "stale context accepted"
  match bound.publish 5 (produce reference 5) reference with
  | (.ok result,6) => unless result.total == 18 do throw "pipeline total"
  | _ => throw "current retry refused"

#eval match test with
  | .ok () => IO.println "RECURSIVE-CONTRACTS-OK"
  | .error cause => throw (IO.userError cause)
#print axioms RecursiveValidation.catalog_success
#print axioms RecursiveValidation.collect_apply
#print axioms RecursiveValidation.collect_complete
#print axioms RecursiveValidation.shape_error
#print axioms RecursiveValidation.normalization_error
#print axioms RecursiveValidation.admission_error
#print axioms RecursiveValidation.requirements
#print axioms RecursiveValidation.edge_preserved
#print axioms RecursiveValidation.shared_target
#print axioms RecursiveValidation.distinct_targets
#print axioms RecursiveValidation.bound_root
#print axioms peer_peer
#print axioms PositiveEquations.least
#print axioms Cached.runCertified_diagnostic
#print axioms ValidationRebinding.memo_agrees
#print axioms validateObject_refine
end LeanPoo.Examples.RecursiveContracts
