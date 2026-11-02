import LeanPoo.Prototype.GeneralizedFork
import LeanPoo.Prototype.GeneralizedTariff

/-! Future-work client: one pricing object feeds independent shipping/insurance
branches, whose ordered selected views jointly configure settlement. -/
namespace LeanPoo.Examples.ForkedCheckout
open Prototype Prototype.Generalized
open TariffComponent (Account Local Fragment Action family closeLocal mark summary stageFragments)

def pricing := stageFragments 6 "pricing"
def shipping := stageFragments 2 "shipping" (some 8)
def insurance := stageFragments 3 "insurance"
def settlement := stageFragments 1 "settlement" (some 4)
def base : Account := ⟨1,{}⟩

def fork : DependencyFork Local family family where
  selectLeft := fun viewed => viewed.rate / 5
  selectRight := fun viewed => viewed.rate / 7
  leftFragments := shipping
  rightFragments := insurance
  leftBase := base
  rightBase := base

def joinView (branches : Local × Local) : Int × Int := (branches.1.rate / 3,branches.2.rate / 3)
def joinFamily (dependency : Int × Int) := family (10*dependency.1 + dependency.2)

def builder (name : String) (fragments : List Fragment) (refuse : Bool) (dependency : Int) :
    Except String (Closed (family dependency) fragments base) :=
  if refuse then .error (name ++ ".construction") else closeLocal dependency fragments base

def joinBuilder (refuse : Bool) (dependency : Int × Int) :
    Except String (Closed (joinFamily dependency) settlement base) :=
  builder "settlement" settlement refuse (10*dependency.1 + dependency.2)

structure Publication (dependency : Int) where
  root : Closed (family dependency) pricing base
  branches : fork.Publication root.interface
  joined : Closed (joinFamily (joinView branches.closed.interface)) settlement base

def publish (dependency : Int) : Except String (Publication dependency) := do
  let root ← closeLocal dependency pricing base
  let branches ← fork.publish root.interface (builder "shipping" shipping false) (builder "insurance" insurance false)
  let joined ← joinBuilder false (joinView branches.closed.interface)
  return ⟨root,branches,joined⟩

structure Revision {old : Int} (original : Publication old) (revised : Int) where
  root : DependencyRefresh original.root revised
  branches : fork.Refresh original.branches root.closed.interface
  joined : DependencyRefresh original.joined (joinView branches.publication.closed.interface)

def Revision.publication {old revised : Int} {original : Publication old}
    (revision : Revision original revised) : Publication revised :=
  ⟨revision.root.closed,revision.branches.publication,revision.joined.closed⟩

def Revision.flags {old revised : Int} {original : Publication old}
    (revision : Revision original revised) : List Bool :=
  [revision.root.reused,revision.branches.left.reused,revision.branches.right.reused,revision.joined.reused]

def revise {old : Int} (original : Publication old) (revised : Int) (refuse : Nat → Bool) :
    Except String (Revision original revised) := do
  let root ← original.root.refreshDependency revised (builder "pricing" pricing (refuse 0))
  let branches ← fork.refresh original.branches root.closed.interface
    (builder "shipping" shipping (refuse 1)) (builder "insurance" insurance (refuse 2))
  let joined ← branches.join joinView original.joined (joinBuilder (refuse 3))
  return ⟨root,branches,joined⟩

def first (dependency : Int) := DependentComponents.pair (family dependency) fork.family id
def second (dependency : Int) := DependentComponents.pair (first dependency).protocol joinFamily (fun viewed => joinView viewed.2)
def pairFragments (left : List A) (right : List B) : List (Sum A B) := left.map Sum.inl ++ right.map Sum.inr
def fragments := pairFragments (pairFragments pricing fork.fragments) settlement
def wholeBase := ((base,fork.base),base)

/-- The shared root occurs once in the raw whole; both branches reference its
same cooked final self, and settlement sees the resulting complete pair. -/
def assemble {dependency : Int} (publication : Publication dependency) :
    Closed (second dependency).protocol fragments wholeBase := by
  let front := DependentComponents.closePair id publication.root publication.branches.closed
  let joined := publication.joined.reuseDependency (joinView front.interface.2)
    (by rw [DependentComponents.closePair_interface])
  exact DependentComponents.closePair (fun viewed => joinView viewed.2) front joined

theorem assemble_interface {dependency : Int} (publication : Publication dependency) :
    (assemble publication).interface =
      ((publication.root.interface,(publication.branches.leftClosed.interface,publication.branches.rightClosed.interface)),
        publication.joined.interface) := by rfl

abbrev Service := (Local × (Local × Local)) × Local

def checkout (service : Service) (units : Int) : Action Int := do
  let subtotal ← service.1.1.price units
  let delivery ← service.1.2.1.price units
  let coverage ← service.1.2.2.price units
  let charge ← service.2.price units
  return subtotal + delivery + coverage + charge

def rates (service : Service) : List Int := [service.1.1.rate,service.1.2.1.rate,service.1.2.2.rate,service.2.rate]

theorem retained_shipping {old revised : Int} {original : Publication old}
    (revision : Revision original revised) (reused : revision.branches.left.reused = true)
    (units : Int) (ledger : List String) :
    (((assemble revision.publication).interface.1.2.1.price units).run ledger) =
      (((assemble original).interface.1.2.1.price units).run ledger) := by
  rw [assemble_interface,assemble_interface]
  exact congrArg (fun viewed : Local => (viewed.price units).run ledger) (revision.branches.left.interface_same reused)

/-- Join reuse preserves complete settlement outcomes independently of which
branches were rebuilt in this revision. -/
theorem retained_settlement {old revised : Int} {original : Publication old}
    (revision : Revision original revised) (reused : revision.joined.reused = true)
    (units : Int) (ledger : List String) :
    (((assemble revision.publication).interface.2.price units).run ledger) =
      (((assemble original).interface.2.price units).run ledger) := by
  rw [assemble_interface,assemble_interface]
  exact congrArg (fun viewed : Local => (viewed.price units).run ledger) (revision.joined.interface_same reused)

def run : IO Unit := do
  let original ← IO.ofExcept (publish 0)
  for (dependency,flags,values) in [
      (0,[true,true,true,true],[6,3,3,12]),
      (2,[false,true,false,true],[8,3,4,12]),
      (4,[false,false,false,true],[10,4,4,12]),
      (14,[false,false,false,false],[20,6,5,22])] do
    let revised ← IO.ofExcept (revise original dependency (fun _ => false))
    unless revised.flags == flags && rates (assemble revised.publication).interface == values do
      throw (IO.userError "diamond branch/join boundary")
  let previous ← IO.ofExcept (publish 2)
  let insuranceHeld ← IO.ofExcept (revise previous 4 (fun stage => stage ≥ 2))
  unless insuranceHeld.flags == [false,false,true,true] do
    throw (IO.userError "left-only revision rebuilt insurance or settlement")
  let stopped ← IO.ofExcept (revise original 4 (fun stage => stage == 3))
  unless stopped.joined.reused do throw (IO.userError "unchanged pair called refusing join builder")
  unless (revise original 14 (fun stage => stage ≥ 2)).toOption.isNone &&
      (summary ((checkout (assemble original).interface 2).run [])).1 == some 48 do
    throw (IO.userError "failed diamond damaged old publication")
  IO.println "FORKED-CHECKOUT-OK shared-root independent-branch-refresh exact-pair-join retained-join first-refusal whole-fixed-point"
#eval run
#print axioms assemble
#print axioms assemble_interface
#print axioms retained_shipping
#print axioms retained_settlement
#print axioms DependencyFork.Refresh.join_reuses
#print axioms DependencyFork.refresh_right_error
end LeanPoo.Examples.ForkedCheckout
