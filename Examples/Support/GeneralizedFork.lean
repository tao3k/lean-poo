import LeanPoo.Prototype.GeneralizedFork
import LeanPoo.Prototype.GeneralizedTariff

/-! Future-work client: one pricing object feeds independent shipping/insurance
branches, whose ordered selected views jointly configure settlement. -/
namespace LeanPoo.Tests.GeneralizedFork
open Prototype Prototype.Generalized
open TariffComponent (Account Local Fragment Action family closeLocal mark summary stageFragments)

/-- Ordered pricing fragments shared by both dependent branches. -/
def pricing := stageFragments 6 "pricing"
/-- Shipping fragments retain their eight-unit rejection boundary. -/
def shipping := stageFragments 2 "shipping" (some 8)
/-- Independent insurance fragments observe the same pricing root. -/
def insurance := stageFragments 3 "insurance"
/-- Settlement fragments retain their four-unit rejection boundary. -/
def settlement := stageFragments 1 "settlement" (some 4)
/-- Missing-method base used by every component closure. -/
def base : Account := ⟨1,{}⟩

/-- Select each sibling dependency from the shared cooked pricing object. -/
def fork : DependencyFork Local family family where
  selectLeft := fun viewed => viewed.rate / 5
  selectRight := fun viewed => viewed.rate / 7
  leftFragments := shipping
  rightFragments := insurance
  leftBase := base
  rightBase := base

/-- Preserve branch order when selecting settlement metadata. -/
def joinView (branches : Local × Local) : Int × Int := (branches.1.rate / 3,branches.2.rate / 3)
/-- Construct settlement from the ordered pair of branch views. -/
def joinFamily (dependency : Int × Int) := family (10*dependency.1 + dependency.2)

/-- Reject before closing a changed dependency when its stage refuses. -/
def builder (name : String) (fragments : List Fragment) (refuse : Bool) (dependency : Int) :
    Except String (Closed (family dependency) fragments base) :=
  if refuse then .error (name ++ ".construction") else closeLocal dependency fragments base

/-- Apply the same refusal discipline to the joined component. -/
def joinBuilder (refuse : Bool) (dependency : Int × Int) :
    Except String (Closed (joinFamily dependency) settlement base) :=
  builder "settlement" settlement refuse (10*dependency.1 + dependency.2)

structure Publication (dependency : Int) where
  root : Closed (family dependency) pricing base
  branches : fork.Publication root.interface
  joined : Closed (joinFamily (joinView branches.closed.interface)) settlement base

/-- Close pricing, both branches and settlement in dependency order. -/
def publish (dependency : Int) : Except String (Publication dependency) := do
  let root ← closeLocal dependency pricing base
  let branches ← fork.publish root.interface (builder "shipping" shipping false) (builder "insurance" insurance false)
  let joined ← joinBuilder false (joinView branches.closed.interface)
  return ⟨root,branches,joined⟩

structure Revision {old : Int} (original : Publication old) (revised : Int) where
  root : DependencyRefresh original.root revised
  branches : fork.Refresh original.branches root.closed.interface
  joined : DependencyRefresh original.joined (joinView branches.publication.closed.interface)

/-- Expose the completed revision only after all stages succeed. -/
def Revision.publication {old revised : Int} {original : Publication old}
    (revision : Revision original revised) : Publication revised :=
  ⟨revision.root.closed,revision.branches.publication,revision.joined.closed⟩

/-- Report exactly which dependency closures were reused. -/
def Revision.flags {old revised : Int} {original : Publication old}
    (revision : Revision original revised) : List Bool :=
  [revision.root.reused,revision.branches.left.reused,revision.branches.right.reused,revision.joined.reused]

/-- Refresh changed components in order and return the first construction error. -/
def revise {old : Int} (original : Publication old) (revised : Int) (refuse : Nat → Bool) :
    Except String (Revision original revised) := do
  let root ← original.root.refreshDependency revised (builder "pricing" pricing (refuse 0))
  let branches ← fork.refresh original.branches root.closed.interface
    (builder "shipping" shipping (refuse 1)) (builder "insurance" insurance (refuse 2))
  let joined ← branches.join joinView original.joined (joinBuilder (refuse 3))
  return ⟨root,branches,joined⟩

/-- Pair the root with its two dependent branches. -/
def first (dependency : Int) := DependentComponents.pair (family dependency) fork.family id
/-- Pair the front components with their ordered settlement dependency. -/
def second (dependency : Int) := DependentComponents.pair (first dependency).protocol joinFamily (fun viewed => joinView viewed.2)
/-- Tag component fragments while preserving their internal order. -/
def pairFragments (left : List A) (right : List B) : List (Sum A B) := left.map Sum.inl ++ right.map Sum.inr
/-- Complete root, sibling and settlement fragment sequence. -/
def fragments := pairFragments (pairFragments pricing fork.fragments) settlement
/-- Product base for the complete four-component construction. -/
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

/-- Use the shared ordered action fold rather than a private interpreted chain. -/
def checkout (service : Service) (units : Int) : Action Int :=
  TariffComponent.checkoutMany [service.1.1,service.1.2.1,service.1.2.2,service.2] units

/-- The shared combinator preserves complete successful/error states for all
four arbitrary prices and caller ledgers, not only the arithmetic fixtures. -/
theorem checkout_reference (service : Service) (units : Int) : checkout service units = (do
    let subtotal ← service.1.1.price units
    let delivery ← service.1.2.1.price units
    let coverage ← service.1.2.2.price units
    let charge ← service.2.price units
    return subtotal + delivery + coverage + charge) := by
  simp [checkout, TariffComponent.checkoutMany, List.foldlM, Int.zero_add]

/-- Observe all four cooked rates in component order. -/
def rates (service : Service) : List Int := [service.1.1.rate,service.1.2.1.rate,service.1.2.2.rate,service.2.rate]

theorem retained_shipping {old revised : Int} {original : Publication old}
    (revision : Revision original revised) (reused : revision.branches.left.reused = true)
    (units : Int) (ledger : List String) :
    (((assemble revision.publication).interface.1.2.1.price units).run ledger) =
      (((assemble original).interface.1.2.1.price units).run ledger) := by
  rw [assemble_interface,assemble_interface]
  exact congrArg (fun viewed : Local => (viewed.price units).run ledger) (revision.branches.left.interface_same reused)

/-- Transport product representations through an invertible dictionary bridge. -/
def reassociate (A : Type) : DictionaryBridge ((A × (A × A)) × A) (A × (A × (A × A))) :=
  ⟨(fun raw => (raw.1.1,raw.1.2.1,raw.1.2.2,raw.2)),
    (fun raw => ((raw.1,(raw.2.1,raw.2.2.1)),raw.2.2.2)),fun _ => rfl,fun _ => rfl⟩

-- A genuine interleaving of sibling fragments preserves each branch's order.
/-- Interleave sibling fragments without changing either sibling order. -/
def interleave : List A → List B → List (Sum A B)
  | [], right => right.map Sum.inr
  | left, [] => left.map Sum.inl
  | first::left, second::right => .inl first :: .inr second :: interleave left right

/-- Concrete sibling interleaving used by the complete workflow. -/
def mixed := interleave shipping insurance

/-- Reuse the existing interleaved-closure construction and its order witnesses. -/
def mixedClosed {dependency : Int} (publication : Publication dependency) :
    Closed (fork.family publication.root.interface) mixed fork.base :=
  publication.branches.closeInterleaved mixed (by rfl) (by rfl)

/-- Expose a numeric raw component through its own protocol. -/
def heterogeneousLeft : Bool → Protocol Nat Nat Unit := fun _ => ⟨id,fun _ _ parent => parent.get⟩
/-- Expose string length through a different raw-component protocol. -/
def heterogeneousRight : Int → Protocol String Nat Bool := fun _ => ⟨String.length,fun _ _ parent => parent.get⟩
/-- Exercise heterogeneous dependency keys and raw representations. -/
def heterogeneous : DependencyFork Nat heterogeneousLeft heterogeneousRight :=
  ⟨(fun value => decide (value > 5)),Int.ofNat,[],[],7,"approved"⟩

/-- Join reuse preserves complete settlement outcomes independently of which
branches were rebuilt in this revision. -/
theorem retained_settlement {old revised : Int} {original : Publication old}
    (revision : Revision original revised) (reused : revision.joined.reused = true)
    (units : Int) (ledger : List String) :
    (((assemble revision.publication).interface.2.price units).run ledger) =
      (((assemble original).interface.2.price units).run ledger) := by
  rw [assemble_interface,assemble_interface]
  exact congrArg (fun viewed : Local => (viewed.price units).run ledger) (revision.joined.interface_same reused)

end LeanPoo.Tests.GeneralizedFork
