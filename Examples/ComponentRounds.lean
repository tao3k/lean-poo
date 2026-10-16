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
/-- Six actual rounds exercise shared migration, repeated endpoint recreation,
interleaved SCC merge/split, erased providers and stale snapshot rejection. -/
def check : Except String Unit := do
  let .ok r1 := SupportRevision.joinAt (0 : Nat) 0 source (contributions .merge) | throw "merge refused"
  let .ok r2 := SupportRevision.joinAt (1 : Nat) 1 r1.apply (contributions .replace) | throw "split refused"
  let .ok r3 := SupportRevision.joinAt (2 : Nat) 2 r2.apply (contributions .restore) | throw "restore refused"
  let some g1 := discoverSupported r1.keys (fun key dep => decide (dep ∈ r1.apply.reads key)) | throw "merged graph refused"
  let some g2 := discoverSupported r2.keys (fun key dep => decide (dep ∈ r2.apply.reads key)) | throw "replaced graph refused"
  let some g3 := discoverSupported r3.keys (fun key dep => decide (dep ∈ r3.apply.reads key)) | throw "restored graph refused"
  unless (g1.members 2).length == 7 && (g2.members 2).map Fin.val == [2,3,7] &&
      (g2.members 5).map Fin.val == [5,8] && (g3.members 2).map Fin.val == [2,3,4] &&
      (g3.members 5).map Fin.val == [5,6] do throw "interleaved groups mismatch"
  unless (List.finRange 12).map (g2.dirty (supportRevisionSeed g1 g2 (fun _ => false))) ==
      [false,false,true,true,false,true,false,true,true,true,true,false] do throw "split invalidation mismatch"
  unless (List.finRange 12).map (g3.dirty (supportRevisionSeed g2 g3 (fun _ => false))) ==
      [false,false,true,true,true,true,true,false,false,true,true,false] do throw "restore invalidation mismatch"
  let old ← execute source
  let merged ← execute r1.apply
  let replaced ← execute r2.apply
  let restored ← execute r3.apply
  unless old.get 10 == 12 && merged.get 10 == 24 && replaced.get 10 == 16 && restored == old do
    throw "actual round closure mismatch"
  unless refused (SupportRevision.joinAt (0 : Nat) 3 r3.apply (contributions .merge)) do
    throw "old staged request accepted after support/value round trip"
  let .ok r4 := SupportRevision.joinAt (3 : Nat) 3 r3.apply
    (contributions .merge [⟨1,some (.ok 5)⟩]) | throw "second merge refused"
  let .ok r5 := SupportRevision.joinAt (4 : Nat) 4 r4.apply (contributions .replace) | throw "second split refused"
  let .ok r6 := SupportRevision.joinAt (5 : Nat) 5 r5.apply
    (contributions .restore [⟨0,some (.ok 2)⟩]) | throw "second restore refused"
  let next ← execute r4.apply
  let split ← execute r5.apply
  let final ← execute r6.apply
  unless next.get 10 == 30 && split.get 10 == 20 && final.get 10 == 8 && final.get 2 == 2 do
    throw "repeated migration closure mismatch"
  unless (r6.apply.code 7).isNone && (r6.apply.base 7).isNone &&
      (r6.apply.code 8).isNone && (r6.apply.base 8).isNone do throw "removed providers reappeared"
/-- Competing staged requests reuse actual component sources/closure while the
serialized publication rule selects which fully approved candidate may install.
Snapshot labels are local fixtures; runtime freshness is a separate premise. -/
def requestsCheck : Except String Unit := do
  let .ok first := SupportRevision.joinAt (0 : Nat) 0 source (contributions .merge) |
    throw "first staged request refused"
  let .ok second := SupportRevision.joinAt (0 : Nat) 0 source
    (contributions .merge [⟨1,some (.ok 5)⟩]) | throw "second staged request refused"
  let firstRaw ← execute first.apply
  let secondRaw ← execute second.apply
  unless firstRaw.get 10 == 24 && secondRaw.get 10 == 30 do throw "candidate construction mismatch"
  let winner := Functional.ComponentPublication.install (0 : Nat) 0 2 (approved second.apply true true 30 secondRaw)
  let late := Functional.ComponentPublication.install (0 : Nat) winner.head 1
    (approved first.apply true true 30 firstRaw)
  unless winner.accepted && winner.head == 2 && !late.accepted && late.head == winner.head do
    throw "late candidate overwrote accepted rival"
  let denied := Functional.ComponentPublication.install (0 : Nat) 0 1
    (approved first.apply true false 30 firstRaw)
  unless !denied.accepted && denied.head == 0 do throw "joint refusal advanced publication"
  let retry := Functional.ComponentPublication.install (0 : Nat) denied.head 1
    (approved first.apply true true 30 firstRaw)
  unless retry.accepted && retry.head == 1 do throw "fresh current-policy retry failed"
  unless refused (SupportRevision.joinAt (0 : Nat) winner.head second.apply (contributions .merge)) do
    throw "stale staging accepted after rival"
  let .ok split := SupportRevision.joinAt (2 : Nat) winner.head second.apply (contributions .replace) |
    throw "retry on current topology refused"
  let splitRaw ← execute split.apply
  unless splitRaw.get 10 == 20 do throw "current topology retry closure mismatch"
  let installed := Functional.ComponentPublication.install (2 : Nat) winner.head 3
    (approved split.apply true true 30 splitRaw)
  unless installed.accepted && installed.head == 3 do throw "current topology retry not installed"
#eval match requestsCheck with
  | .ok () => IO.println "COMPONENT-REQUESTS-OK"
  | .error message => throw (IO.userError message)
#print axioms Functional.ComponentPublication.stale
#print axioms Functional.ComponentPublication.refused
#print axioms Functional.ComponentPublication.accepted
#print axioms Functional.ComponentPublication.competing
#print axioms Functional.ComponentPublication.retry
#eval match check with
  | .ok () => IO.println "COMPONENT-ROUNDS-OK"
  | .error message => throw (IO.userError message)
#print axioms SupportRevision.joinAt_stale
#print axioms SupportRevision.joinAt_accepted
#print axioms SupportRevision.join_erased
#print axioms Functional.ComponentExecution.resolved_correct
#print axioms Functional.ComponentExecution.focus_laws
end LeanPoo.Examples.ComponentRounds
