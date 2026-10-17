import LeanPoo.Functional.RecursiveMigration
import LeanPoo.Functional.FunctionValidation

/-! Matching six-round Gerbil workflow: provider addition/migration/removal,
same-key recipe return, failed final admission/retry, computed-reader replacement,
checked Functions and refined evidence. Fin positions change; names own identity.
Host callback/read completeness and source/identity correspondence remain premises. -/
namespace LeanPoo.Examples.RecursiveMigrations
open Functional

/-- Stable names outlive removal; neither a row number nor its reuse owns identity. -/
inductive Name where
  | a | b | left | right | summary | report | idle | meter
  deriving Repr, BEq, DecidableEq
open Name

/-- Original directory, before the second provider or downstream observer exists. -/
def c0 : RecursiveMigration.Catalog Name := ⟨[a,left,right,summary,report,idle],by decide,by decide⟩
/-- New provider is appended, preserving submitted directory order. -/
def c1 : RecursiveMigration.Catalog Name := ⟨[a,left,right,summary,report,idle,b],by decide,by decide⟩
/-- Remove unread a, shifting report from row 4 to row 3, and append meter. -/
def c2 : RecursiveMigration.Catalog Name := ⟨[left,right,summary,report,idle,b,meter],by decide,by decide⟩
/-- Remove b and re-add the original a name after the gap. -/
def c3 : RecursiveMigration.Catalog Name := ⟨[left,right,summary,report,idle,meter,a],by decide,by decide⟩

/-- Explicit recipe parameters carry the actual shared and computed footprints. -/
structure Source where
  catalog : RecursiveMigration.Catalog Name
  provider : Name
  reader : Name
  leftWeight : Int := 2
  refuse : Bool := false

/-- Declared edges include peer cycles, computed captures and downstream reporting. -/
def dependencies (source : Source) : Name → List Name
  | .left => [right,source.provider]
  | .right => [left,source.provider]
  | .summary => [source.reader]
  | .report => [left,right,summary]
  | .meter => [report]
  | _ => []

/-- Dynamic Boolean arguments cannot silently pass an Integer Function contract. -/
inductive Scalar where
  | integer : Int → Scalar
  | flag : Bool → Scalar

/-- Existing Function validation supplies input/result normalization. -/
def handler (offset : Int) : Scalar → Except String Int := FunctionValidation.wrap
  (fun value => match value with | .integer n => .ok n | .flag _ => .error "integer argument")
  Except.ok (fun n => .ok (n+offset))

/-- Actual cached closures and computed totals are retained as values, not hashes. -/
structure Payload where
  call : Scalar → Except String Int
  total : Int

/-- Each provider has a stable definition; service recipes choose which one they read. -/
def delta (provider : Name) : Int := if provider = b then 8 else 3

/-- Concrete source results agree with the corresponding Gerbil checked handlers. -/
def service (source : Source) (name : Name) : Int :=
  1 + delta source.provider + if name = left then source.leftWeight else 3

/-- Computed-only reader changes affect summary/report/meter, without touching peers. -/
def total (source : Source) : Name → Int
  | .a => 3 | .b => 8 | .idle => 99
  | .left => service source left | .right => service source right
  | .summary => service source source.reader
  | .report | .meter => service source left + service source right + service source source.reader

/-- Build actual checked Functions and computed payloads for dirty/new components. -/
def payload (source : Source) (name : Name) : Payload :=
  ⟨handler (if name = a then 3 else if name = b then 8
            else delta source.provider + if name = left then source.leftWeight else 3),total source name⟩

/-- A published snapshot has the graph's actual current support/index carrier. -/
structure Snapshot where
  source : Source
  generations : Name → Nat
  graph : RecursiveValidation.Graph source.catalog.names.length (Name × Nat) Payload
  evaluated : List Name

/-- A total cache adapter has an arbitrary outside-support fallback. New names
must normalize, so that fallback is never permission to resurrect a latent node. -/
def cache (snapshot : Snapshot) (name : Name) : Payload :=
  match snapshot.source.catalog.index name with
  | none => ⟨handler 0,0⟩
  | some index => snapshot.graph.payload index

/-- Read only supported canonical identities from the actual closed graph. -/
def reference (snapshot : Snapshot) (name : Name) : Option (Name × Nat) :=
  (snapshot.source.catalog.index name).map snapshot.graph.canonical

/-- All current node obligations run, including fully retained nodes. -/
def admit (source : Source)
    (edges : Fin source.catalog.names.length → List (Fin source.catalog.names.length))
    (candidate : RecursiveValidation.Graph source.catalog.names.length (Name × Nat) Payload)
    (index : Fin source.catalog.names.length) : Except String Unit :=
  if source.refuse && source.catalog.name index == summary then .error "joint refusal"
  else if (candidate.payload index).total = total source (source.catalog.name index) ∧
      candidate.links index = (edges index).map candidate.canonical then .ok () else .error "current obligation"

/-- Lower actual named edges, compute least invalidation from new support/body/
footprint seeds, then reuse the existing all-or-error reclosure. Clean shape and
normalization callbacks deliberately error if invoked, making accidental replay visible. -/
def build (oldNames : List Name) (oldDependencies : Name → List Name) (previous : Name → Payload)
    (generation : Name → Nat) (next : Source) (changed : List Name) : Except String Snapshot := do
  let edges ← (RecursiveMigration.lower next.catalog (dependencies next)).mapError (fun _ => "dangling target")
  let seed := RecursiveMigration.seeds oldNames oldDependencies (dependencies next) (fun key => changed.contains key)
  let dirty := RecursiveMigration.dirtyNames next.catalog edges seed
  let candidate ← (RecursiveMigration.reclose oldNames next.catalog dirty generation previous (dependencies next)
    (fun key => if RecursiveMigration.needsBuild oldNames dirty key then .ok () else .error "clean shape replayed")
    (fun key => if RecursiveMigration.needsBuild oldNames dirty key then .ok (payload next key) else .error "clean normalization replayed")
    (admit next edges)).mapError (fun cause => match cause with | .inl _ => "lowering" | .inr message => message)
  return ⟨next,RecursiveMigration.advanceKey oldNames next.catalog.names dirty generation,candidate,
    next.catalog.names.filter (RecursiveMigration.needsBuild oldNames dirty)⟩

/-- One admitted round consumes exactly the prior named graph and its epoch ledger. -/
def step (previous : Snapshot) (next : Source) (changed : List Name) : Except String Snapshot :=
  build previous.source.catalog.names (dependencies previous.source) (cache previous) previous.generations next changed

/-- Existing whole-value refinement verifies current report/summary correspondence. -/
def schema (expected : Int) : ObjectContract.Contract Snapshot String Unit String :=
  ObjectContract.refine
    {view := ⟨fun _ => true,fun _ => true,fun _ => [],fun _ _ => none⟩
     fields := [],strict := true,constraints := [],validInventory := Or.inl rfl,obligations := fun _ _ => []}
    (fun value path => if (cache value report).total == expected &&
      (cache value meter).total == expected then [] else [.rejected path "computed migration"])

/-- Exact subject/descriptor/context evidence remains independent of application policy. -/
def Call : DeclarativeMetadata.Contract Unit (Name × Nat) ((Name × Nat) × Nat × Nat) where
  input := ⟨"reference",fun _ => True,fun _ => isTrue True.intro⟩
  output := ⟨"evidence",fun _ => True,fun _ => isTrue True.intro⟩
  meaning := fun _ _ _ => True
  decide := fun _ _ _ => isTrue True.intro
  rule := .atom ()

/-- The original report row really moves when unused provider a is removed. -/
example : (c0.index report).map Fin.val = some 4 ∧ (c2.index report).map Fin.val = some 3 := by decide
/-- Ordered shared aliases survive lowering, rather than being deduplicated. -/
example : (RecursiveMigration.lowerLinks c0 [left,left,a]).map (List.map c0.name) = .ok [left,left,a] := by rfl

/-- Execute six matching rounds, abort late approval, retry, check old references
and bind current refined evidence. No failed candidate replaces the previous state. -/
def test : Except String Unit := do
  let initial : Source := ⟨c0,a,left,2,false⟩
  let s0 ← build [] (fun _ => []) (fun _ => ⟨handler 0,0⟩) (fun _ => 0) initial []
  unless (cache s0 report).total == 19 do throw "initial total"
  let s1 ← step s0 ⟨c1,b,right,2,false⟩ [left,right,summary,b]
  unless (cache s1 report).total == 35 && s1.evaluated == [left,right,summary,report,b] do throw "shared migration"
  let s2 ← step s1 ⟨c2,b,right,2,false⟩ [meter]
  unless s2.evaluated == [meter] && reference s1 report == reference s2 report do throw "reindex lost clean identity"
  unless reference s2 a == none do throw "removed latent reference"
  let s3 ← step s2 ⟨c3,a,left,2,false⟩ [left,right,summary,a]
  unless (cache s3 report).total == 19 && reference s0 a != reference s3 a do throw "ABA revived"
  unless !(RecursiveMigration.recognizes c3.names s3.generations a (a,s0.generations a)) do throw "old a accepted"
  match step s3 ⟨c3,a,right,9,true⟩ [left,summary] with
  | .error "joint refusal" => pure () | _ => throw "late refusal bypassed"
  let s4 ← step s3 ⟨c3,a,right,9,false⟩ [left,summary]
  unless s4.evaluated == [left,right,summary,report,meter] && (cache s4 report).total == 27 do throw "retry failed"
  let s5 ← step s4 ⟨c3,a,left,9,false⟩ [summary]
  unless s5.evaluated == [summary,report,meter] && (cache s5 meter).total == 33 do throw "computed footprint"
  unless reference s4 left == reference s5 left && reference s0 idle == reference s5 idle do throw "over-invalidation"
  match (cache s5 left).call (.flag false) with
  | .error "integer argument" => pure () | _ => throw "Function guard"
  unless (ObjectContract.diagnose (schema 33) s5 []).isEmpty do throw "refine"
  let root := (report,s5.generations report)
  let bound := Call.bindEvidence root 7 7 (fun value => value)
  let produce (subject : Name × Nat) (context : Nat) (_ : Name × Nat) :
      Except String (((Name × Nat) × Nat × Nat) × Nat) := .ok ((subject,7,context),8)
  match bound.publish 7 (produce (report,s4.generations report) 7) root with
  | (.error .logic,7) => pure () | _ => throw "old report evidence"
  match bound.publish 7 (produce root 6) root with
  | (.error .logic,7) => pure () | _ => throw "stale context evidence"
  match bound.publish 7 (produce root 7) root with
  | (.ok _,8) => pure () | _ => throw "current evidence retry"

#print axioms RecursiveMigration.Catalog.name_injective
#print axioms RecursiveMigration.Catalog.index_name
#print axioms RecursiveMigration.Catalog.index_self
#print axioms RecursiveMigration.lower_names
#print axioms RecursiveMigration.reindex_retained
#print axioms RecursiveMigration.removed_advance
#print axioms RecursiveMigration.gap_refused
#print axioms RecursiveMigration.dirty_old_refused
#print axioms RecursiveMigration.fresh_build
#print axioms RecursiveMigration.footprint_seed
#print axioms RecursiveMigration.invalidate_equation
#print axioms RecursiveMigration.invalidate_least
#print axioms RecursiveMigration.invalidate_bound
#print axioms RecursiveMigration.reader_dirty
#print axioms RecursiveMigration.clean_dependency
#print axioms RecursiveMigration.admitted
#print axioms RecursiveMigration.bound_root
#print axioms RecursiveRevision.failed_commit
#eval match test with
  | .ok () => IO.println "RECURSIVE-MIGRATIONS-OK"
  | .error cause => throw (IO.userError cause)
end LeanPoo.Examples.RecursiveMigrations
