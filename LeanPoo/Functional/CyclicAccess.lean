import LeanPoo.Functional.CyclicPublication
import LeanPoo.Functional.DeclarativeMetadata
import LeanPoo.Prototype.RecursiveCacheSemantics

/-! Safe recursive attestation seeds mutually dependent group/review/release
capabilities. Least cyclic closure, lossy public cooking and two typed generics
are admitted and published together. Generalized-MOP future work. -/
namespace LeanPoo.Functional.CyclicAccess
open PositiveEquations Prototype.Recursive

/-- A safe recursive attestation chain with shared subrequests. Source failure,
recursive divergence and a completed false answer remain distinct outcomes. -/
def attestation : Generator (Nat × String) Bool := fun request =>
  if request.2 == "cycle" then .call request .value
  else if request.2 == "failed" then .error "attestation-source"
  else if request.1 = 0 then .value (request.2 == "active")
  else .call (request.1-1,request.2) (fun first =>
    .call (request.1-1,request.2) (fun second => .value (first && second)))

theorem attestation_active (depth : Nat) :
    Evaluates attestation (attestation (depth,"active")) (.value true) := by
  induction depth with
  | zero => exact .value
  | succ depth ih => exact .callValue ih (.callValue ih .value)

structure Config where
  trust : Bool := true
  training : Bool := true
  team : Bool := true
  compliance : Bool := true
  deriving Repr

/-- Two cycles, a shared membership dependency and a final branch join.
No negative dependency occurs inside the fixed-point equations. -/
def equations (config : Config) (attested : Bool) : Equations 10 := fun index => match index.val with
  | 0 => .literal attested
  | 1 => .either (.read 0) (.read 2)
  | 2 => .both (.read 1) (.literal config.trust)
  | 3 => .literal config.training
  | 4 => .both (.read 2) (Expr.twoOfThree (.read 3) (.literal config.team) (.literal config.compliance))
  | 5 => .either (.read 4) (.read 6)
  | 6 => .both (.read 5) (.literal config.team)
  | 7 => .both (.read 6) (.read 8)
  | 8 => .both (.read 2) (.literal config.compliance)
  | _ => .either (.read 7) (.read 5)

/-- All literal configurations of this workflow share the exact read topology. -/
theorem equation_dependencies (left right : Config) (first second : Bool) (index : Fin 10) :
    IncrementalClosure.dependencies (equations left first index) =
      IncrementalClosure.dependencies (equations right second index) := by
  unfold equations
  split <;> rfl

/-- An unseeded positive cycle cannot manufacture release authority, even though
nonleast fixed points may contain it. This holds for every configuration. -/
theorem unseeded_release (config : Config) : (close (equations config false)).value 7 = false := by
  let lower : Bits 10 := fun index => if index.val = 3 then config.training else false
  have fixed : step (equations config false) lower = lower := by
    rcases config with ⟨trust,training,team,compliance⟩
    cases trust <;> cases training <;> cases team <;> cases compliance <;> decide
  have below := least (equations config false) lower fixed 7
  cases found : (close (equations config false)).value 7 with
  | false => rfl
  | true =>
    have impossible := below found
    have denied : lower 7 = false := rfl
    rw [denied] at impossible
    contradiction

structure View where
  member : Bool
  approved : Bool
  release : Bool
  active : List Nat
  deriving Repr, BEq

inductive Service where
  | grant | explain
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable
abbrev Args : Service → Type
  | .grant => String × Bool
  | .explain => Unit
abbrev Result : Service → Type
  | .grant => Except String String
  | .explain => List Nat
abbrev Method (key : Service) := Args key → Result key

structure Policy where
  requireRelease : Bool := false
  forbidden : Bool := false
  broken : Bool := false
  corrupt : Bool := false

def bit (raw : GeneralizedGraph.State (Fin 10) (fun _ => Bool)) (index : Fin 10) : Bool :=
  ((raw index).bind Except.toOption).getD false

def cook (raw : GeneralizedGraph.State (Fin 10) (fun _ => Bool)) : View :=
  ⟨bit raw 2,bit raw 5,bit raw 7,((List.ofFn id : List (Fin 10)).filter (bit raw)).map Fin.val⟩

def seed : (key : Service) → Policy → View → Object.Multimethod (Args key) (Method key) (Result key)
  | .grant, policy, _ => {
    arity := if policy.broken then 2 else 1
    precedence := fun args => [if args.1 == "forbidden" then ["Forbidden"] else ["Release"]]
    combine := fun methods args => match methods[0]? with | none => .error "missing" | some method => method args }
  | .explain, _, _ => {
    arity := 1
    precedence := fun _ => [["Explain"]]
    combine := fun methods args => match methods[0]? with | none => [] | some method => method args }

def declarations : (key : Service) → Policy → View → List (DeclarativeMetadata.Declaration (Args key) (Method key))
  | .grant, policy, view => [.replace "grant.release" [.prototype "Release"] (fun args =>
      if policy.corrupt then .ok "unproved"
      else if !args.2 then .error "consent"
      else if view.release then .ok ("release:" ++ args.1) else .error "not-authorized")] ++
      if policy.forbidden then [.replace "grant.forbidden" [.prototype "Forbidden"] (fun _ => .ok "forbidden")] else []
  | .explain, _, view => [.replace "explain.active" [.prototype "Explain"] (fun _ => view.active)]

def model : StagedPublication.Model (Fin 10) (fun _ => Bool) Service Policy View Args Method Result where
  cook := fun _ => cook
  generics := {
    keys := [.grant,.explain]
    seed
    seedEmpty := by intro key policy view; cases key <;> rfl
    methods := fun key policy view => (declarations key policy view).map DeclarativeMetadata.Declaration.compile
    watches := fun key => match key with | .grant => [.call ("forbidden",true)] | .explain => [.shape [["Forbidden"]]] }

abbrev Request := GeneralizedMOP.Request (Fin 10) (fun _ => Bool) Policy
abbrev Candidate (current : Request) := StagedPublication.Candidate model current

def probes {current : Request} (candidate : Candidate current) : Option (Option String) × Option (List Nat) :=
  ((candidate.family.table.call .grant ("customer",true)).toOption.map (fun pair => pair.1.toOption),
    (candidate.family.table.call .explain ()).toOption.map Prod.fst)

structure Approval (current : Request) (candidate : Candidate current) : Type where
  required : current.policy.requireRelease = true → candidate.interface.release = true
  coherent : probes candidate =
    (some (if candidate.interface.release then some "release:customer" else none),some candidate.interface.active)

def admit (current : Request) (candidate : Candidate current) : Except String (Approval current candidate) :=
  if required : current.policy.requireRelease = true → candidate.interface.release = true then
    if coherent : probes candidate =
        (some (if candidate.interface.release then some "release:customer" else none),some candidate.interface.active) then
      .ok ⟨required,coherent⟩
    else .error "coherence"
  else .error "release-required"

/-- The safe recursive program is a supplied existing generator. Its exact
program/request evaluation receipt seeds the Boolean equation declaration. -/
structure Version (program : Generator Input Bool) where
  input : Input
  enabled : Bool
  receipt : Cached.Receipt program (program input)
  observed : receipt.result = .value enabled
  memo : Cached.Cache program
  config : Config
  closure : CyclicPublication.Version (Approved := Approval) model
  source : closure.equations = equations config enabled

inductive Failure (program : Generator Input Bool) where
  | recursive (input : Input) (error : Cached.Failure program input)
  | source (message : String)
  | publication (error : StagedPublication.Failure (BuildError := Unit) (AdmissionError := String) model)

variable {Input : Type} [DecidableEq Input] (program : Generator Input Bool)

def prepare (memo : Cached.Cache program) (input : Input) (budget : Nat) (config : Config) (policy : Policy)
    (prior : Option (Version program) := none) :
    Except (Failure program) (Version program) :=
  match Cached.runCertified program input budget memo with
  | .error error => .error (.recursive input error)
  | .ok (receipt,next) => match observed : receipt.result with
    | .error message => .error (.source message)
    | .value enabled =>
      let chosen : {plan : IncrementalClosure.Plan 10 // plan.source = equations config enabled} := match prior with
        | none => ⟨IncrementalClosure.compile _,IncrementalClosure.compile_source _⟩
        | some old => ⟨IncrementalClosure.reconfigure old.closure.plan (equations config enabled) (by
            intro index
            rw [old.closure.planSource,old.source]
            exact equation_dependencies _ _ _ _ _),IncrementalClosure.reconfigure_source _ _ _⟩
      match prepared : CyclicPublication.prepareWithPlan model (equations config enabled) policy chosen.val chosen.property admit with
      | .error error => .error (.publication error)
      | .ok closure => .ok ⟨input,enabled,receipt,observed,next,config,closure,
          CyclicPublication.prepareWithPlan_equations model _ policy _ _ admit closure prepared⟩

def start (input : Input) (budget : Nat) (config : Config) (policy : Policy) := prepare program {} input budget config policy

def revise (old : Version program) (input : Input) (budget : Nat) (config : Config) (policy : Policy) :=
  CarrierMigration.publish old (fun version => prepare program version.memo input budget config policy (some version))

def invoke (old : Version program) (key : Service) (args : Args key) :
    Except (Sum (Object.DispatchTableError Service) String) (Result key × Version program) :=
  match called : old.closure.invoke model key args admit with
  | .error error => .error error
  | .ok (result,next) =>
    .ok (result,{old with
      closure := next
      source := (CyclicPublication.Version.invoke_equations model old.closure key args admit result next called).trans old.source})

omit [DecidableEq Input] in
/-- Equation input is bound to an actual safe-recursion evaluation, independently
of the fixed-point theorem and generic admission. -/
theorem observed_source (version : Version program) :
    ∃ depth, solve program depth version.input = .value version.enabled := by
  obtain ⟨depth,observed⟩ := version.receipt.observed
  exact ⟨depth,by simpa [version.observed,Cached.Completed.observation] using observed⟩

omit [DecidableEq Input] in
/-- Revoked external attestation removes release at the actual materialized
public interface, rather than retaining a larger, self-supporting fixed point. -/
theorem revoked (version : Version program) (disabled : version.enabled = false) :
    version.closure.snapshot.candidate.interface.release = false := by
  change bit version.closure.snapshot.candidate.cache.closed.raw 7 = false
  rw [version.closure.canonical,version.source,disabled]
  simp [bit,raw,Except.toOption,unseeded_release]

end LeanPoo.Functional.CyclicAccess
