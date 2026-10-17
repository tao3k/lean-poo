import LeanPoo.Functional.ComponentRevision
import LeanPoo.Functional.ComponentExecution
import LeanPoo.Functional.ComponentPublication

/-! Repeated merge/split, component replacement and shared-input migration. This
finite generalized-protocol future work certifies actual resolver equations. -/
namespace LeanPoo.Examples.ComponentRounds
open Functional.GeneralizedGraph Functional.StrongComponents
/-- Same twelve lens positions as the native multi-round services. -/
abbrev Key := Fin 12
/-- Numeric endpoints reuse the existing dependent graph representation. -/
abbrev Values := fun _ : Key => Nat
/-- Active component lifecycle phases describe topology, not revision identities. -/
inductive Phase where | merge | replace | restore
/-- Copy real outcomes, including component errors. -/
def copied (dep : Key) : Code Key Values dep := .need dep fun _ value => value
/-- Existing applicative computations gather complete declared outcomes. -/
def collect : List Key → Functional.Computation Unit Key (fun _ dep => Outcome Key Values dep)
    (fun _ => Except (Functional.ComputationError Key) (List Nat))
  | [] => .pure (fun _ => .ok [])
  | key :: rest => .both (copied key) (collect rest) fun _ head tail => do return (← head) :: (← tail)
/-- One first-order recipe reuses the native read-list and higher-order combination. -/
def recipe (deps : List Key) (combine : List Nat → Nat) (key : Key) : Code Key Values key :=
  .map (collect deps) fun _ values => values.map combine
/-- Capped growth combines one shared input and a feedback predecessor. -/
def advance (values : List Nat) : Nat := min values[0]! (1 + values[1]!)
/-- Same stable three phase recipes as native, including merged bridge equations. -/
def program (phase : Phase) (key : Key) : Code Key Values key :=
  match phase,key.val with
  | .merge,2 => recipe [1,4] advance key
  | .merge,4 => recipe [3,8] (fun vs => min vs[0]! vs[1]!) key
  | .merge,5 => recipe [2,6,7] (fun vs => min vs[0]! (1 + max vs[1]! vs[2]!)) key
  | .merge,7 => recipe [2,5,8] (fun vs => min vs[0]! (1 + max vs[1]! vs[2]!)) key
  | .merge,8 => copied 7
  | .replace,2 => recipe [1,7] advance key
  | .replace,3 => recipe [2,7] advance key
  | .replace,5 => recipe [2,8] advance key
  | .replace,7 => copied 3
  | .replace,8 => copied 5
  | .restore,2 => recipe [0,4] advance key
  | _,3 => recipe [2,4] advance key
  | _,4 => copied 3
  | _,5 => recipe [0,6] advance key
  | _,6 => copied 5
  | _,9 => copied 2
  | .merge,10 => recipe [3,4,5,6,7,8] List.sum key
  | .replace,10 => recipe [3,5,7,8] List.sum key
  | .restore,10 => recipe [3,4,5,6] List.sum key
  | _,11 => recipe [11] (fun vs => min 2 (1 + vs[0]!)) key
  | _,_ => .pure (fun _ => .ok 0)
/-- Initial supported components match the native compact declaration. -/
def source : Declaration Key Values :=
  ⟨[0,1,2,3,4,5,6,9,10,11],fun key => if key.val < 2 then none else some (program .restore key),
    fun key => if key.val = 0 then some (.ok 3) else if key.val = 1 then some (.ok 4) else none⟩
/-- Ordered recipe edits preserve the actual dependent payload at each key. -/
def codes (phase : Phase) (keys : List Key) : List ((key : Key) × Option (Code Key Values key)) :=
  keys.map fun key => ⟨key,some (program phase key)⟩
/-- Stage complete multi-service changes; phase transitions themselves are checked
against current support. Restoring deleted B/D supplies their definitions anew. -/
def contributions (phase : Phase) (inputs : List ((key : Key) × Option (Outcome Key Values key)) := []) :
    List (RevisionFragment Key Values) :=
  (match phase with
  | .merge => [⟨[7,8],[],codes phase [2,4,5,7,8,10],[]⟩]
  | .replace => [⟨[],[4],codes phase [2,3],[]⟩,⟨[],[],codes phase [7],[]⟩,
      ⟨[],[6],codes phase [5,8],[]⟩,⟨[],[],codes phase [10],[]⟩]
  | .restore => [⟨[4,6],[7,8],codes phase [2,3,4,5,6,10],[]⟩]) ++ [⟨[],[],[],inputs⟩]
/-- Joint policy checks current endpoints and both service decisions on each round. -/
def approved (spec : Declaration Key Values) (left right : Bool) (limit : Nat) (raw : Vector Nat 12) : Bool :=
  let endpoints := spec.keys.filter fun key => decide (key.val ∈ [3,4,5,6,7,8])
  left && right && (9 :: endpoints).all (fun key => decide (raw.get key = raw.get 2)) &&
    decide (raw.get 10 = endpoints.length * raw.get 2 ∧ raw.get 10 ≤ limit)
/-- Check a successful source, discovered exact groups and typed final equations.
The shared reference runner retains residual proofs, not just sampled numbers. -/
def execute (spec : Declaration Key Values) : Except String (Vector Nat 12) := do
  let some graph := discoverSupported spec.keys (fun key dep => decide (dep ∈ spec.reads key)) |
    throw "round SCC discovery refused"
  let closed ← Functional.ComponentExecution.build spec graph (Vector.replicate 12 0) 32
  unless approved spec true true 30 closed.raw && !approved spec true false 30 closed.raw do
    throw "current cross-service policy mismatch"
  return closed.raw
/-- Runtime check of accepted/refused dependent edits, with no serialized identity. -/
def refused {α : Type u} : Except String α → Bool
  | .error _ => true
  | .ok _ => false
end LeanPoo.Examples.ComponentRounds
