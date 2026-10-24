import LeanPoo.Functional.RecursiveRevision
import LeanPoo.Functional.FunctionValidation

/-! Shared provider, two mutually recursive services, a computed report and an
independent cached node. The fixture exercises two different invalidation cones,
actual checked Function calls, current refinement/evidence and old-reference
refusal. Complete dependency declarations and host identity/stamp lowering are
premises, not inferred from arbitrary Scheme closures. -/
namespace LeanPoo.Examples.RecursiveRevisions
open Functional Functional.RecursiveValidation Functional.RecursiveRevision

abbrev Node := Fin 5

/-- Consumer-to-dependency edges include the report's computed reads. -/
def edges (node : Node) : List Node :=
  if node = 1 then [2,0] else if node = 2 then [1,0]
  else if node = 3 then [1,2,0] else []

/-- The same finite read graph is supplied to existing reachability certification. -/
def edge (reader target : Node) : Bool := decide (target ∈ edges reader)

/-- Concrete exact relation: the two services form one SCC above shared provider 0. -/
def relation (reader target : Node) : Bool :=
  if reader = 3 then decide (target.val < 4)
  else if reader = 1 ∨ reader = 2 then decide (target.val < 3)
  else decide (reader = target)

/-- A checked relation uses existing path soundness. No assumed graph axiom is added. -/
def graph : StrongComponents.Checked edge where
  rel := relation
  laws := by unfold StrongComponents.Laws; decide
  sound := by
    intro reader target found
    apply StrongComponents.reachable_sound edge 5 reader target
    have all : ∀ reader target : Node, relation reader target = true →
        StrongComponents.reachable edge 5 reader target = true := by decide
    exact all reader target found

/-- Dynamic argument classes remain distinct at checked Function boundaries. -/
inductive Scalar where
  | integer : Int → Scalar
  | flag : Bool → Scalar

abbrev Handler := Scalar → Except String Int

/-- Actual handlers use the existing callable input/result normalization chain. -/
def handler (offset : Int) : Handler := FunctionValidation.wrap
  (fun value => match value with | .integer n => .ok n | .flag _ => .error "integer argument")
  Except.ok (fun n => .ok (n+offset))

/-- Cached payloads contain a callable and a computed report value. -/
structure Payload where
  call : Handler
  computed : Int

/-- Service results share the same provider delta; report combines both branches. -/
def payload (delta leftWeight : Int) (node : Node) : Payload :=
  let offset := if node = 1 then delta+leftWeight else if node = 2 then delta+3 else delta
  ⟨handler offset, if node = 3 then 2*(1+delta)+leftWeight+3 else if node = 4 then 99 else offset⟩

/-- Current final admission checks the computed report and every canonical edge. -/
def admit (expected : Int) (candidate : Graph 5 (Node × Nat) Payload) (node : Node) : Except String Unit :=
  if (candidate.payload 3).computed = expected ∧
      candidate.links node = (edges node).map candidate.canonical then .ok () else .error "refinement"

/-- A source edit at the shared provider invalidates both services and the report. -/
def sharedDirty : Node → Bool := graph.dirty (fun node => decide (node = 0))

/-- Replacing one service invalidates its SCC and report, preserving provider/idle. -/
def peerDirty : Node → Bool := graph.dirty (fun node => decide (node = 1))

/-- The clean branch of the normalization callback deliberately fails: successful
closure therefore checks that it really skipped this construction path. -/
def rebuild (dirty : Node → Bool) (delta weight : Int) (node : Node) : Except String Payload :=
  if dirty node then .ok (payload delta weight node) else .error "clean callback ran"

/-- First revised graph retains idle while recooking both branches from delta 8. -/
def first := reclose sharedDirty (fun _ => 0) (payload 3 2) edges
  (fun _ => .ok ()) (rebuild sharedDirty 8 2) (admit 23)

/-- Subsequent revision keeps provider/idle and changes the complete service SCC. -/
def second := first.bind fun current => reclose peerDirty (advance sharedDirty (fun _ => 0))
  current.payload edges (fun _ => .ok ()) (rebuild peerDirty 8 9) (admit 30)

example : (List.finRange 5).filter sharedDirty = [0,1,2,3] := by decide
example : (List.finRange 5).filter peerDirty = [1,2,3] := by decide
example : first.map (fun current => (current.payload 3).computed) = .ok 23 := by rfl
example : second.map (fun current => (current.payload 3).computed) = .ok 30 := by rfl
example : (second.bind fun current => (current.payload 1).call (.integer 1)) = .ok 18 := by rfl
example : (second.bind fun current => (current.payload 1).call (.flag false)) = .error "integer argument" := by rfl
example : recognizes (advance peerDirty (advance sharedDirty (fun _ => 0))) 0 (0,1) = true := by decide
example : recognizes (advance peerDirty (advance sharedDirty (fun _ => 0))) 1 (1,1) = false := by decide
example : recognizes (advance peerDirty (advance sharedDirty (fun _ => 0))) 4 (4,0) = true := by decide

/-- A new final obligation can refuse even when every recipe and cache is clean. -/
def denied := reclose (fun _ : Node => false) (fun _ => 0) (payload 3 2) edges
  (fun _ => .error "shape must be skipped") (fun _ => .error "normalize must be skipped")
  (fun _ node => if node = 3 then .error "joint refusal" else .ok ())

example : denied.map (fun _ => ()) = .error "joint refusal" := by rfl

/-- Current whole-value refinement composes computed consistency and backedges. -/
def schema (expected : Int) : ObjectContract.Contract (Graph 5 (Node × Nat) Payload) String Unit String :=
  ObjectContract.refine
    {view := ⟨fun _ => true,fun _ => true,fun _ => [],fun _ _ => none⟩
     fields := [], strict := true, constraints := [], validInventory := Or.inl rfl
     obligations := fun _ _ => []}
    (fun current path => if (current.payload 3).computed == expected &&
      current.links 1 == [current.canonical 2,current.canonical 0] &&
      current.links 2 == [current.canonical 1,current.canonical 0] then []
      else [.rejected path "current computed refinement"])

/-- Application policy remains independently checked by bind-evidence. -/
def Call : DeclarativeMetadata.Contract Unit (Node × Nat) ((Node × Nat) × Nat × Nat) where
  input := ⟨"reference",fun _ => True,fun _ => isTrue True.intro⟩
  output := ⟨"evidence",fun _ => True,fun _ => isTrue True.intro⟩
  meaning := fun _ _ _ => True
  decide := fun _ _ _ => isTrue True.intro
  rule := .atom ()

/-- Two rounds, current refinement, stale subject/context refusal and current retry. -/
def test : Except String Unit := do
  let current ← second
  unless (ObjectContract.diagnose (schema 30) current []).isEmpty do throw "refine refused"
  let root := current.canonical 3
  let bound := Call.bindEvidence root 7 2 (fun value => value)
  let produce (reference : Node × Nat) (context : Nat) (_ : Node × Nat) :
      Except String (((Node × Nat) × Nat × Nat) × Nat) := .ok ((reference,7,context),3)
  match bound.publish 2 (produce (3,1) 2) root with
  | (.error .logic,2) => pure () | _ => throw "old subject accepted"
  match bound.publish 2 (produce root 1) root with
  | (.error .logic,2) => pure () | _ => throw "old context accepted"
  match bound.publish 2 (produce root 2) root with
  | (.ok _,3) => pure () | _ => throw "current retry refused"

#check RecursiveRevision.bound_root
#print axioms clean_dependency
#print axioms shared_dirty
#print axioms clean_select
#print axioms old_reference_refused
#print axioms older_reference_refused
#print axioms RecursiveRevision.requirements
#print axioms failed_commit
#print axioms RecursiveRevision.bound_root
#eval first.map (fun current => (current.payload 3).computed)
#eval second.map (fun current => (current.payload 3).computed)
#eval match test with
  | .ok () => IO.println "RECURSIVE-REVISIONS-OK"
  | .error cause => throw (IO.userError cause)
end LeanPoo.Examples.RecursiveRevisions
