import LeanPoo.Functional.ComponentRevision
import LeanPoo.Functional.SupportedComponents
import LeanPoo.Functional.ComponentExecution

/-! Joint replacement of two services and their shared dependency. Future-work
closure uses actual dependent source resolvers, not a separately supplied equation. -/
namespace LeanPoo.Examples.ComponentMigration
open Functional.GeneralizedGraph Functional.StrongComponents Prototype Prototype.Generalized
/-- The native declared lens universe is unchanged by active component replacement. -/
abbrev Key := Fin 12
/-- Raw positions remain separate from active component support. -/
abbrev Raw := Vector Nat 12
/-- This scenario uses numeric endpoints with the existing dependent source API. -/
abbrev Values := fun _ : Key => Nat
/-- Copy an actual outcome, preserving failure rather than defaulting at the recipe. -/
def copied (dep : Key) : Code Key Values dep := .need dep fun _ value => value
/-- Existing typed applicative combination implements capped feedback advancement. -/
def advanced (cap dep : Key) : Code Key Values dep :=
  .both (copied cap) (copied dep) fun _ capValue depValue => do
    return min (← capValue) (1 + (← depValue))
/-- Settlement gathers actual outcomes using the same finite applicative chain. -/
def collect : List Key → Functional.Computation Unit Key (fun _ dep => Outcome Key Values dep)
    (fun _ => Except (Functional.ComputationError Key) (List Nat))
  | [] => .pure (fun _ => .ok [])
  | key :: rest => .both (copied key) (collect rest) fun _ head tail => do
      return (← head) :: (← tail)
/-- Same initial and replacement recipes as native, including unchanged monitor. -/
def program (migrated : Bool) (key : Key) : Code Key Values key :=
  match key.val with
  | 2 => if migrated then advanced 1 7 else advanced 0 4
  | 3 => if migrated then advanced 2 7 else advanced 2 4
  | 4 => copied 3
  | 5 => if migrated then advanced 2 8 else advanced 0 6
  | 6 => copied 5
  | 7 => copied 3
  | 8 => copied 5
  | 9 => copied 2
  | 10 => .map (collect (if migrated then [3,5,7,8] else [3,4,5,6])) fun _ result => result.map List.sum
  | 11 => .map (copied 11) fun _ result => result.map (fun n => min 2 (1+n))
  | _ => .pure (fun _ => .ok 0)
/-- Fresh E/F have no active support despite potential latent code in this source. -/
def source (quota spare : Nat) : Declaration Key Values :=
  ⟨[0,1,2,3,4,5,6,9,10,11],fun key => if key.val < 2 then none else some (program false key),
    fun key => if key.val = 0 then some (.ok quota) else if key.val = 1 then some (.ok spare) else none⟩
/-- Four service fragments include forward references to not-yet-contributed E/F. -/
def contributions : List (RevisionFragment Key Values) :=
  [⟨[],[4],[⟨2,some (program true 2)⟩,⟨3,some (program true 3)⟩],[]⟩,
   ⟨[7],[],[⟨7,some (program true 7)⟩],[]⟩,
   ⟨[8],[6],[⟨5,some (program true 5)⟩,⟨8,some (program true 8)⟩],[]⟩,
   ⟨[],[],[⟨10,some (program true 10)⟩],[]⟩]
/-- Graph discovery reads footprints from the actual submitted typed source. -/
def edge (spec : Declaration Key Values) (key dep : Key) : Bool := decide (dep ∈ spec.reads key)
/-- Reuse the shared source-driven reference runner, including final real residuals. -/
def build (spec : Declaration Key Values) (graph : Supported (edge spec)) : Except String Raw :=
  (Functional.ComponentExecution.build spec graph (Vector.replicate 12 0) 32).map (·.raw)
/-- Joint policy requires every replacement endpoint and the unchanged monitor. -/
def approved (allowed : Bool) (limit : Nat) (raw : Raw) : Bool :=
  allowed && ([3,5,7,8,9] : List Key).all (fun key => decide (raw.get key = raw.get 2)) &&
    decide (raw.get 10 = 4 * raw.get 2 ∧ raw.get 10 ≤ limit)
/-- Inspect refusal without projecting success across dependent payload universes. -/
def refused {α : Type u} : Except String α → Bool
  | .error _ => true
  | .ok _ => false
/-- Execute typed fragment validation, accepted SCC discovery, real source closure,
shared invalidation, conflict refusal and current approval together. -/
def check : Except String Unit := do
  let original := source 3 4
  let .ok revision := SupportRevision.join original contributions | throw "joint revision refused"
  let next := revision.apply
  let some oldGraph := discoverSupported original.keys (edge original) | throw "old discovery refused"
  let some nextGraph := discoverSupported next.keys (edge next) | throw "joint discovery refused"
  unless next.keys.map Fin.val == [0,1,2,3,5,9,10,11,7,8] &&
      (oldGraph.members 2).map Fin.val == [2,3,4] && (oldGraph.members 5).map Fin.val == [5,6] &&
      (nextGraph.members 2).map Fin.val == [2,3,7] && (nextGraph.members 5).map Fin.val == [5,8] do
    throw "joint membership mismatch"
  unless (List.finRange 12).map (nextGraph.dirty (supportRevisionSeed oldGraph nextGraph (fun _ => false))) ==
      [false,false,true,true,false,true,false,true,true,true,true,false] do throw "replacement invalidation mismatch"
  unless (List.finRange 12).map (nextGraph.dirty (fun key => decide (key.val = 0))) ==
      [true,false,false,false,false,false,false,false,false,false,false,false] &&
      (List.finRange 12).map (nextGraph.dirty (fun key => decide (key.val = 1))) ==
      [false,true,true,true,false,true,false,true,true,true,true,false] do throw "shared migration mismatch"
  let initial ← build original oldGraph
  let migrated ← build next nextGraph
  unless initial.toList == [3,4,3,3,3,3,3,0,0,3,12,2] &&
      migrated.toList == [3,4,4,4,0,4,0,4,4,4,16,2] do throw "actual source closure mismatch"
  unless approved true 20 migrated && !approved true 12 migrated && !approved false 20 migrated do
    throw "current joint policy mismatch"
  let .ok joint := SupportRevision.join original (contributions ++
      [⟨[],[],[],[⟨0,some (.ok 9)⟩]⟩,⟨[],[],[],[⟨1,some (.ok 5)⟩]⟩]) | throw "mixed joint revision refused"
  let some jointGraph := discoverSupported joint.apply.keys (edge joint.apply) | throw "joint input graph refused"
  let jointRaw ← build joint.apply jointGraph
  unless jointRaw.toList == [9,5,5,5,0,5,0,5,5,5,20,2] do throw "mixed joint closure mismatch"
  unless (refused (SupportRevision.join next contributions)) do throw "stale membership replay accepted"
  let .ok updated := SupportRevision.join next [⟨[],[],[],[⟨1,some (.ok 5)⟩]⟩] | throw "input revision refused"
  let some updatedGraph := discoverSupported updated.apply.keys (edge updated.apply) | throw "updated discovery refused"
  let raised ← build updated.apply updatedGraph
  unless raised.toList == [3,5,5,5,0,5,0,5,5,5,20,2] do throw "joint input closure mismatch"
  unless (refused (SupportRevision.join original [contributions[0]'(by decide),contributions[0]'(by decide)])) &&
      (refused (SupportRevision.join original [contributions[1]'(by decide),contributions[1]'(by decide)])) &&
      (refused (SupportRevision.join original [⟨[4],[4],[],[]⟩])) &&
      (refused (SupportRevision.join original [⟨[],[],[⟨3,some (program true 3)⟩],[]⟩,
        ⟨[],[],[⟨3,some (program true 3)⟩],[]⟩])) &&
      (refused (SupportRevision.join original [⟨[],[],[],[⟨1,some (.ok 4)⟩]⟩,⟨[],[],[],[⟨1,some (.ok 4)⟩]⟩])) do
    throw "joint conflict accepted"
  let .ok incomplete := SupportRevision.join original [contributions[0]'(by decide)] | throw "partial source preparation refused"
  unless (discoverSupported incomplete.apply.keys (edge incomplete.apply)).isNone do throw "dangling contribution accepted"
#eval match check with
  | .ok () => IO.println "COMPONENT-MIGRATION-OK"
  | .error message => throw (IO.userError message)
#print axioms SupportRevision.join_valid
#print axioms SupportRevision.join_fields
#print axioms SupportRevision.join_members
#print axioms SupportRevision.join_unique
#print axioms SupportRevision.join_fresh
#print axioms SupportRevision.join_erased
#print axioms Functional.ComponentExecution.resolved_correct
#print axioms Functional.ComponentExecution.focus_laws
#print axioms componentGroup_equation
end LeanPoo.Examples.ComponentMigration
