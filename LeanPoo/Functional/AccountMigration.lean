import LeanPoo.Functional.ServiceMetadata
import LeanPoo.Functional.ProjectedSelf
import LeanPoo.Functional.CarrierMigration

/-! A settlement service migrates into a differently typed prepaid account.
The public API discards audit/private storage while preserving construction's
observations. Target construction and two generics publish atomically. Future work. -/
namespace LeanPoo.Functional.AccountMigration
open GeneralizedGraph ProjectedSelf

inductive Key where
  | balance | rate | charge | label | audit | privateNote
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable

structure Money where
  cents : Nat
  deriving Repr, DecidableEq, BEq

abbrev Value : Key → Type
  | .balance | .rate => Nat
  | .charge => Money
  | .label | .audit | .privateNote => String
abbrev Raw := State Key Value
abbrev Cell (key : Key) := Option (Outcome Key Value key)

structure PublicView where
  balance : Cell .balance
  rate : Cell .rate
  charge : Cell .charge
  label : Cell .label

structure Api where
  wallet : Cell .balance × Cell .rate
  invoice : Cell .charge × Cell .label

/-- Exact representation conversion of an already lossy public view. -/
def bridge : Prototype.DictionaryBridge PublicView Api :=
  ⟨fun value => ⟨(value.balance,value.rate),(value.charge,value.label)⟩,
   fun value => ⟨value.wallet.1,value.wallet.2,value.invoice.1,value.invoice.2⟩,
   fun value => by cases value; rfl,fun value => by cases value with | mk wallet invoice => cases wallet; cases invoice; rfl⟩

def projection : Projection Key Value PublicView where
  visible := [.balance,.rate,.charge,.label]
  cook raw := ⟨raw .balance,raw .rate,raw .charge,raw .label⟩
  view value key := match key with
    | .balance => value.balance | .rate => value.rate
    | .charge => value.charge | .label => value.label
    | .audit | .privateNote => none
  preserves := by intro raw key member; cases key <;> simp_all

def apiProjection := projection.represent bridge

def need (key : Key) (f : Value key → Value result) : Code Key Value result :=
  .need key (fun _ outcome => outcome.map f)

def code : (key : Key) → Option (Code Key Value key)
  | .charge => some (.both (need .balance id) (need .rate id) (fun _ left right => do
      let balance ← left
      let rate ← right
      return ⟨balance*rate⟩))
  | .audit => some (.both (need .charge id) (need .label id) (fun _ left right => do
      let charge ← left
      let label ← right
      return label ++ ":" ++ toString charge.cents))
  | _ => none

def graph (rate : Nat) (note : String) : Declaration Key Value where
  keys := [.balance,.rate,.charge,.label,.audit,.privateNote]
  code
  base key := match key with
    | .balance => none
    | .rate => some (.ok rate)
    | .label => some (.ok "anonymous")
    | .privateNote => some (.ok note)
    | .charge | .audit => none

/-- A hidden raw note changes without any change to actual public cooking. -/
theorem cook_hidden (raw : Raw) (note : String) :
    apiProjection.cook (setSlot raw .privateNote (some (.ok note))) = apiProjection.cook raw := rfl

theorem lossy : ¬ Function.Injective apiProjection.cook := by
  intro injective
  let empty : Raw := fun _ => none
  have same := injective ((cook_hidden empty "first").trans (cook_hidden empty "second").symm)
  have note := congrFun same Key.privateNote
  simp [setSlot] at note

inductive Service where
  | spend | receipt
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable
abbrev Args : Service → Type
  | .spend => Nat
  | .receipt => String
abbrev Result : Service → Type
  | .spend => Except String Nat
  | .receipt => Except String String
abbrev Method (key : Service) := Args key → Result key

structure Policy where
  fee : Nat := 0
  forbidden : Bool := false
  broken : Bool := false

def seed : (key : Service) → Policy → Api → Object.Multimethod (Args key) (Method key) (Result key)
  | .spend, policy, _ => {
    arity := if policy.broken then 2 else 1
    precedence := fun _ => [["Account"]]
    combine := fun methods args => match methods[0]? with
      | none => .error "missing:spend" | some method => method args }
  | .receipt, _, _ => {
    arity := 1
    precedence := fun args => [if args == "forbidden" then ["Forbidden"] else ["Account"]]
    combine := fun methods args => match methods[0]? with
      | none => .error "missing:receipt" | some method => method args }

def selected (cell : Cell key) : Except String (Value key) := match cell with
  | none => .error "missing"
  | some (.error _) => .error "source"
  | some (.ok value) => .ok value

def declarations : (key : Service) → Policy → Api → List (DeclarativeMetadata.Declaration (Args key) (Method key))
  | .spend, policy, cooked => [.replace "spend.balance" [.prototype "Account"] (fun units => do
      let balance ← selected cooked.wallet.1
      if units+policy.fee ≤ balance then return balance-(units+policy.fee) else .error "funds")]
  | .receipt, policy, cooked => [.replace "receipt.charge" [.prototype "Account"] (fun customer => do
      let charge ← selected cooked.invoice.1
      let label ← selected cooked.invoice.2
      return customer ++ "/" ++ label ++ "/" ++ toString charge.cents)] ++
      if policy.forbidden then [.replace "receipt.forbidden" [.prototype "Forbidden"] (fun _ => .ok "forbidden")] else []

def model : StagedPublication.Model Key Value Service Policy Api Args Method Result where
  cook := fun _ => apiProjection.cook
  generics := {
    keys := [.spend,.receipt]
    seed
    seedEmpty := by intro key policy cooked; cases key <;> rfl
    methods := fun key policy cooked => (declarations key policy cooked).map DeclarativeMetadata.Declaration.compile
    watches := fun key => match key with | .spend => [.shape [["Forbidden"]]] | .receipt => [.call "forbidden"] }

abbrev Request := GeneralizedMOP.Request Key Value Policy
abbrev Candidate (current : Request) := StagedPublication.Candidate model current

def probes {current : Request} (candidate : Candidate current) : Option Nat × Option String :=
  ((candidate.family.table.call .spend 2).toOption.bind (fun pair => pair.1.toOption),
   (candidate.family.table.call .receipt "customer").toOption.bind (fun pair => pair.1.toOption))

structure Approval (current : Request) (candidate : Candidate current) where
  coverage : Checked apiProjection current.graph
  known : ∀ key, (current.graph.footprint key).unknown = false
  balance : Nat
  rate : Nat
  label : String
  data : (candidate.interface.wallet.1,candidate.interface.wallet.2,candidate.interface.invoice.2) =
    (some (.ok balance),some (.ok rate),some (.ok label))
  charge : candidate.interface.invoice.1 = some (.ok ⟨balance*rate⟩)
  audit : candidate.cache.closed.raw .audit = some (.ok (label ++ ":" ++ toString (balance*rate)))
  bounded : balance*rate ≤ 10000
  coherent : probes candidate = (some (balance-(2+current.policy.fee)),some ("customer/" ++ label ++ "/" ++ toString (balance*rate)))

/-- Compare with a successful payload without imposing equality on arbitrary
error carriers. Failure and absence cannot be admitted as a successful value. -/
def valueDecision (cell : Cell key) (value : Value key) [DecidableEq (Value key)] :
    Decidable (cell = some (.ok value)) := by
  cases cell with
  | none => exact isFalse (by intro same; cases same)
  | some outcome => cases outcome with
    | error error => exact isFalse (by intro same; cases same)
    | ok actual => exact decidable_of_iff (actual = value) (by simp)

def admit (current : Request) (candidate : Candidate current) : Except String (Approval current candidate) :=
  match ProjectedSelf.check apiProjection current.graph with
  | .error _ => .error "projection-coverage"
  | .ok coverage => match current.graph.schedule with
    | .error _ => .error "schedule"
    | .ok scheduled =>
      match data : (candidate.interface.wallet.1,candidate.interface.wallet.2,candidate.interface.invoice.2) with
      | (some (.ok balance),some (.ok rate),some (.ok label)) =>
        letI := valueDecision candidate.interface.invoice.1 ⟨balance*rate⟩
        letI := valueDecision (candidate.cache.closed.raw .audit) (label ++ ":" ++ toString (balance*rate))
        if charge : candidate.interface.invoice.1 = some (.ok ⟨balance*rate⟩) then
          if audit : candidate.cache.closed.raw .audit = some (.ok (label ++ ":" ++ toString (balance*rate))) then
            if bounded : balance*rate ≤ 10000 then
              if coherent : probes candidate = (some (balance-(2+current.policy.fee)),some ("customer/" ++ label ++ "/" ++ toString (balance*rate))) then
                .ok ⟨coverage,scheduled.known,balance,rate,label,data,charge,audit,bounded,coherent⟩
              else .error "family-coherence"
            else .error "charge-limit"
          else .error "audit"
        else .error "charge"
      | _ => .error "data"

abbrev Version := StagedPublication.Snapshot model Approval

/-- This is closure of the actual lossy cooked-self lens protocol, stronger than
raw closure alone. It reuses the already materialized raw fixed point. -/
def closed (version : Version) :=
  ProjectedSelf.close apiProjection version.request.graph version.approval.coverage version.approval.known version.candidate.cache

/-- Source Int becomes target Nat; keys and the public/API/generic carriers also
change. Missing input may use the target label default; missing balance refuses. -/
abbrev Transfer := CarrierMigration.Transfer (SourceKey := String) (SourceValue := ConstructionWorkflow.Values) (TargetValue := Value)

def balanceTransfer (maxBalance : Nat) : Transfer :=
  {source := "total",target := .balance,convert := fun amount =>
    if 0 ≤ amount && amount ≤ (maxBalance : Int) then .ok amount.toNat else .error "balance-range"}

def labelTransfer : Transfer :=
  {source := "input",target := .label,convert := fun input => .ok ("legacy-" ++ toString input),missing := .useTargetDefault}

def transfers (maxBalance : Nat) : List Transfer := [balanceTransfer maxBalance,labelTransfer]

def migrate (old : ServiceMetadata.Version ceiling) (rate : Nat) (policy : Policy) (maxBalance : Nat)
    (allow : Key → Bool) :=
  CarrierMigration.publish old (fun version => CarrierMigration.rebuild model version.candidate.cache.closed.raw
    (graph rate "target-private") policy (transfers maxBalance)
    (fun spec => ConstructionCache.Builder.guarded spec allow) admit)

def revise (old : Version) (edits : List (GeneralizedMOP.Redefinition Key Value Policy)) (allow : Key → Bool) :=
  StagedPublication.publish model old edits
    (ConstructionCache.Builder.guarded (GeneralizedMOP.redefine old.request edits).graph allow) admit

/-- An accepted carrier migration used the actual old raw snapshot, checked the
explicit typed transfers, and constructed exactly that prepared target graph. -/
theorem migration_origin (old : ServiceMetadata.Version ceiling) (rate : Nat) (policy : Policy) (maxBalance : Nat)
    (allow : Key → Bool) (next : Version)
    (accepted : (migrate old rate policy maxBalance allow).1 = .ok next) :
    ∃ actual, CarrierMigration.prepare old.candidate.cache.closed.raw (graph rate "target-private")
        (transfers maxBalance) = .ok actual ∧ next.request = ⟨actual,policy⟩ := by
  exact CarrierMigration.rebuild_origin model old.candidate.cache.closed.raw (graph rate "target-private") policy
    (transfers maxBalance) (fun spec => ConstructionCache.Builder.guarded spec allow) admit next accepted

/-- Checked numeric conversion, target base installation and target closure
agree on the actual migrated balance, for every old approved snapshot. -/
theorem migrated_balance (old : ServiceMetadata.Version ceiling) (rate : Nat) (policy : Policy) (maxBalance : Nat)
    (allow : Key → Bool) (next : Version)
    (within : old.approval.business.total ≤ (maxBalance : Int))
    (accepted : (migrate old rate policy maxBalance allow).1 = .ok next) :
    next.candidate.cache.closed.raw .balance = some (.ok old.approval.business.total.toNat) := by
  obtain ⟨actual,converted,current⟩ := migration_origin old rate policy maxBalance allow next accepted
  have origin := CarrierMigration.prepare_origin old.candidate.cache.closed.raw (graph rate "target-private")
    (transfers maxBalance) actual converted
  have readOk : CarrierMigration.read old.candidate.cache.closed.raw (balanceTransfer maxBalance) =
      .ok (some old.approval.business.total.toNat) := by
    simp [balanceTransfer, CarrierMigration.read, Object.FieldTransfer.evaluate,
      old.approval.business.totalReady, old.approval.business.nonnegative, within,
      Except.map, Except.mapError, Except.toOption]
  have written : actual.base .balance = some (.ok old.approval.business.total.toNat) := by
    apply CarrierMigration.apply_head old.candidate.cache.closed.raw (graph rate "target-private").base
      ((balanceTransfer maxBalance)) [labelTransfer] _ actual.base readOk
    · simp [labelTransfer, balanceTransfer]
    · exact origin.2.2
  have data : next.request.graph.code .balance = none := by
    rw [current,origin.2.1]
    rfl
  rw [CarrierMigration.data_value _ next.candidate.cache .balance data, current]
  exact written

@[simp] theorem closed_raw (version : Version) : (closed version).raw = version.candidate.cache.closed.raw := rfl

/-- Post-migration public invocation reuses existing full-family approval. -/
def invoke (version : Version) (key : Service) (args : Args key) := version.invoke model key args admit

end LeanPoo.Functional.AccountMigration
