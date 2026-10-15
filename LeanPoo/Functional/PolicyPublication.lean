import LeanPoo.Functional.SharedSettlement
import LeanPoo.Prototype.GeneralizedRevision

/-! Future-work client: upgrade actual method policies on an invoice/audit fork
and its release join while retaining an existing seven-component shared upstream. -/
namespace LeanPoo.Functional.PolicyPublication
open Prototype Prototype.Generalized
open TariffComponent (Account Local Fragment Action family narrow localCook closeLocal stageFragments summary)
namespace Base
export SharedSettlement (Publication Revision publish revise assemble checkout locals rates wholeProtocol fragments wholeBase)
end Base

structure Policy where
  invoiceFee : Int
  auditFee : Int
  releaseFee : Int
  deriving DecidableEq, BEq, Repr

/-- Policy affects successful public actions, not the metadata tariff projection. -/
def policyCook (fee : Int) (raw : Account) : Local :=
  ⟨raw.rate,fun units => EStateM.map (fun value => value+fee) ((localCook raw).price units)⟩
def configured (fee dependency : Int) := (narrow dependency).reindexSelf Local.rate (policyCook fee)
def policyFamily (key : Int × Int) := configured key.1 key.2

def closePolicy (fee dependency : Int) (fragments : List Fragment) (base : Account) :
    Except String (Closed (configured fee dependency) fragments base) := do
  let original ← closeLocal dependency fragments base
  let rawClosed : Closed (narrow dependency) fragments base := ⟨original.raw,by
    rw [← TariffComponent.family_step]
    exact original.fixed⟩
  return rawClosed.reindexSelf Local.rate (policyCook fee) (fun _ => rfl)

def invoice := stageFragments 2 "invoice" (some 3)
def audit := stageFragments 3 "audit"
def release := stageFragments 1 "release" (some 2)
def base : Account := ⟨1,{}⟩
abbrev Context := Policy × SharedSettlement.Service

def fork : DependencyFork Context policyFamily policyFamily :=
  ⟨(fun context => (context.1.invoiceFee,context.2.2.rate/10)),
    (fun context => (context.1.auditFee,context.2.1.1.1.1.rate/4)),invoice,audit,base,base⟩

def contextProtocol (policy : Policy) (key : Int) := (Base.wholeProtocol key).reindexSelf Prod.snd
  (fun raw => (policy,(Base.wholeProtocol key).cook raw))
def contextClosed (policy : Policy) {key : Int} (publication : Base.Publication key) :
    Closed (contextProtocol policy key) Base.fragments Base.wholeBase :=
  (Base.assemble publication).reindexSelf Prod.snd (fun raw => (policy,(Base.wholeProtocol key).cook raw)) (fun _ => rfl)

def build (name : String) (fragments : List Fragment) (refuse : Bool) (key : Int × Int) :
    Except String (Closed (policyFamily key) fragments base) :=
  if refuse then .error (name ++ ".construction") else closePolicy key.1 key.2 fragments base

abbrev ReleaseKey := Int × (Int × Int)
def releaseView (whole : Context × (Local × Local)) : ReleaseKey :=
  (whole.1.1.releaseFee,whole.2.1.rate/4,whole.2.2.rate/4)
def releaseFamily (key : ReleaseKey) := configured key.1 (10*key.2.1+key.2.2)
def releaseBuilder (refuse : Bool) (key : ReleaseKey) : Except String (Closed (releaseFamily key) release base) :=
  build "release" release refuse (key.1,10*key.2.1+key.2.2)

structure Publication (policy : Policy) (key : Int) where
  upstream : Base.Publication key
  branches : fork.Publication (policy,(Base.assemble upstream).interface)
  joined : Closed (releaseFamily (releaseView ((policy,(Base.assemble upstream).interface),branches.closed.interface))) release base

def publish (policy : Policy) (key : Int) : Except String (Publication policy key) := do
  let upstream ← Base.publish key
  let branches ← fork.publish (policy,(Base.assemble upstream).interface) (build "invoice" invoice false) (build "audit" audit false)
  let joined ← releaseBuilder false (releaseView ((policy,(Base.assemble upstream).interface),branches.closed.interface))
  return ⟨upstream,branches,joined⟩

structure Revision {oldPolicy : Policy} {old : Int} (original : Publication oldPolicy old) (policy : Policy) (key : Int) where
  upstream : SharedSettlement.Revision original.upstream key
  branches : fork.Refresh original.branches (policy,(Base.assemble upstream.publication).interface)
  joined : DependencyRefresh original.joined
    (releaseView ((policy,(Base.assemble upstream.publication).interface),branches.publication.closed.interface))

def Revision.publication {oldPolicy policy : Policy} {old key : Int} {original : Publication oldPolicy old}
    (revision : Revision original policy key) : Publication policy key :=
  ⟨revision.upstream.publication,revision.branches.publication,revision.joined.closed⟩
def Revision.flags {oldPolicy policy : Policy} {old key : Int} {original : Publication oldPolicy old}
    (revision : Revision original policy key) : List Bool :=
  revision.upstream.flags ++ [revision.branches.left.reused,revision.branches.right.reused,revision.joined.reused]

def revise {oldPolicy : Policy} {old : Int} (original : Publication oldPolicy old) (policy : Policy) (key : Int)
    (refuse : Nat → Bool) : Except String (Revision original policy key) := do
  let upstream ← Base.revise original.upstream key refuse
  let branches ← fork.refresh original.branches (policy,(Base.assemble upstream.publication).interface)
    (build "invoice" invoice (refuse 7)) (build "audit" audit (refuse 8))
  let joined ← branches.joinWith releaseView original.joined (releaseBuilder (refuse 9))
  return ⟨upstream,branches,joined⟩

def first (policy : Policy) (key : Int) := DependentComponents.pair (contextProtocol policy key) fork.family id
def wholeProtocol (policy : Policy) (key : Int) :=
  (DependentComponents.pair (first policy key).protocol releaseFamily releaseView).protocol
def pairFragments (left : List A) (right : List B) : List (Sum A B) := left.map Sum.inl ++ right.map Sum.inr
def fragments := pairFragments (pairFragments Base.fragments fork.fragments) release
def wholeBase := ((Base.wholeBase,fork.base),base)

def assemble {policy : Policy} {key : Int} (publication : Publication policy key) :
    Closed (wholeProtocol policy key) fragments wholeBase := by
  let front := DependentComponents.closePair id (contextClosed policy publication.upstream) publication.branches.closed
  let joined := publication.joined.reuseDependency (releaseView front.interface)
    (by rfl)
  exact DependentComponents.closePair releaseView front joined

abbrev Service := (Context × (Local × Local)) × Local

theorem assemble_interface {policy : Policy} {key : Int} (publication : Publication policy key) :
    (assemble publication).interface =
      (((policy,(Base.assemble publication.upstream).interface),
        (publication.branches.leftClosed.interface,publication.branches.rightClosed.interface)),publication.joined.interface) := by rfl

def checkout (service : Service) (units : Int) : Action Int := do
  let subtotal ← Base.checkout service.1.1.2 units
  let invoiceCost ← service.1.2.1.price units
  let auditCost ← service.1.2.2.price units
  let releaseCost ← service.2.price units
  return subtotal+invoiceCost+auditCost+releaseCost

def rates (service : Service) : List Int :=
  Base.rates service.1.1.2 ++ [service.1.2.1.rate,service.1.2.2.rate,service.2.rate]

theorem retained_audit {oldPolicy policy : Policy} {old key : Int} {original : Publication oldPolicy old}
    (revision : Revision original policy key) (reused : revision.branches.right.reused = true)
    (units : Int) (ledger : List String) :
    (((assemble revision.publication).interface.1.2.2.price units).run ledger) =
      (((assemble original).interface.1.2.2.price units).run ledger) := by
  rw [assemble_interface,assemble_interface]
  exact congrArg (fun viewed : Local => (viewed.price units).run ledger) (revision.branches.right.interface_same reused)

theorem retained_release {oldPolicy policy : Policy} {old key : Int} {original : Publication oldPolicy old}
    (revision : Revision original policy key) (reused : revision.joined.reused = true)
    (units : Int) (ledger : List String) :
    (((assemble revision.publication).interface.2.price units).run ledger) =
      (((assemble original).interface.2.price units).run ledger) := by
  rw [assemble_interface,assemble_interface]
  exact congrArg (fun viewed : Local => (viewed.price units).run ledger) (revision.joined.interface_same reused)

/-- Recooking preserves an existing successful action's full state. -/
theorem policyCook_ok (fee : Int) (raw : Account) (units value : Int) (ledger state : List String)
    (success : ((localCook raw).price units).run ledger = .ok value state) :
    ((policyCook fee raw).price units).run ledger = .ok (value+fee) state := by
  simp only [EStateM.run] at success
  simp only [policyCook,EStateM.run,EStateM.map,success]

/-- Policy adaptation retains the exact error and already executed ledger. -/
theorem policyCook_error (fee : Int) (raw : Account) (units : Int) (error : String) (ledger state : List String)
    (failed : ((localCook raw).price units).run ledger = .error error state) :
    ((policyCook fee raw).price units).run ledger = .error error state := by
  simp only [EStateM.run] at failed
  simp only [policyCook,EStateM.run,EStateM.map,failed]

/-- Equal tariff metadata is insufficient for retaining a successful policy action. -/
theorem changed_policy_observation (oldFee fee : Int) (raw : Account) (units value : Int)
    (ledger state : List String) (success : ((localCook raw).price units).run ledger = .ok value state)
    (changed : fee ≠ oldFee) :
    ((policyCook fee raw).price units).run ledger ≠ ((policyCook oldFee raw).price units).run ledger := by
  rw [policyCook_ok fee raw units value ledger state success,policyCook_ok oldFee raw units value ledger state success]
  intro same
  have amounts := EStateM.Result.ok.inj same
  omega

end LeanPoo.Functional.PolicyPublication
