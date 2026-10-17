import LeanPoo.Prototype.GeneralizedContext
import LeanPoo.Prototype.GeneralizedTariff

/-! Future-work client: pricing → shipping/insurance → reserve → tax/risk →
settlement. Later stages retain direct shared-pricing dependencies across joins. -/
namespace LeanPoo.Functional.SharedSettlement
open Prototype Prototype.Generalized
open TariffComponent (Account Local Fragment Action family closeLocal stageFragments summary)

def pricing := stageFragments 6 "pricing"
def shipping := stageFragments 2 "shipping" (some 8)
def insurance := stageFragments 3 "insurance"
def reserve := stageFragments 1 "reserve"
def tax := stageFragments 2 "tax" (some 6)
def risk := stageFragments 3 "risk"
def settlement := stageFragments 1 "settlement" (some 4)
def base : Account := ⟨1,{}⟩
def pairFragments (left : List A) (right : List B) : List (Sum A B) := left.map Sum.inl ++ right.map Sum.inr

def firstFork : DependencyFork Local family family :=
  ⟨(fun viewed => viewed.rate/5),(fun viewed => viewed.rate/7),shipping,insurance,base,base⟩
def reserveView (branches : Local × Local) : Int × Int := (branches.1.rate/3,branches.2.rate/3)
def reserveFamily (key : Int × Int) := family (10*key.1+key.2)
def taxFamily (key : Int × Int) := family (10*key.1+key.2)

def build (name : String) (fragments : List Fragment) (refuse : Bool) (key : Int) :
    Except String (Closed (family key) fragments base) :=
  if refuse then .error (name ++ ".construction") else closeLocal key fragments base

def reserveBuilder (refuse : Bool) (key : Int × Int) : Except String (Closed (reserveFamily key) reserve base) :=
  build "reserve" reserve refuse (10*key.1+key.2)
def taxBuilder (refuse : Bool) (key : Int × Int) : Except String (Closed (taxFamily key) tax base) :=
  build "tax" tax refuse (10*key.1+key.2)

structure Early (key : Int) where
  root : Closed (family key) pricing base
  branches : firstFork.Publication root.interface
  joined : Closed (reserveFamily (reserveView branches.closed.interface)) reserve base

def first (key : Int) := DependentComponents.pair (family key) firstFork.family id
def earlyProtocol (key : Int) :=
  (DependentComponents.pair (first key).protocol reserveFamily (fun viewed => reserveView viewed.2)).protocol
def earlyFragments := pairFragments (pairFragments pricing firstFork.fragments) reserve
def earlyBase := ((base,firstFork.base),base)
abbrev EarlyService := (Local × (Local × Local)) × Local

def Early.closed {key : Int} (early : Early key) : Closed (earlyProtocol key) earlyFragments earlyBase := by
  let front := DependentComponents.closePair id early.root early.branches.closed
  let joined := early.joined.reuseDependency (reserveView front.interface.2)
    (by rw [DependentComponents.closePair_interface])
  exact DependentComponents.closePair (fun viewed => reserveView viewed.2) front joined

def sharedView (early : EarlyService) : Local × Local := (early.1.1,early.2)

def laterSpec : DependencyFork (Local × Local) taxFamily family :=
  ⟨(fun viewed => (viewed.1.rate/4,viewed.2.rate/5)),
    (fun viewed => viewed.1.rate/6),tax,risk,base,base⟩
def laterFork := laterSpec.contramap sharedView

abbrev FinalKey := Int × (Int × (Int × Int))
def finalView (whole : EarlyService × (Local × Local)) : FinalKey :=
  (whole.1.1.1.rate/9,whole.1.2.rate/7,whole.2.1.rate/4,whole.2.2.rate/4)
def finalWeight (key : FinalKey) : Int := 1000*key.1 + 100*key.2.1 + 10*key.2.2.1 + key.2.2.2
def finalFamily (key : FinalKey) := family (finalWeight key)
def finalBuilder (refuse : Bool) (key : FinalKey) : Except String (Closed (finalFamily key) settlement base) :=
  build "settlement" settlement refuse (finalWeight key)

structure Publication (key : Int) where
  early : Early key
  later : laterFork.Publication early.closed.interface
  final : Closed (finalFamily (finalView (early.closed.interface,later.closed.interface))) settlement base

def publish (key : Int) : Except String (Publication key) := do
  let root ← closeLocal key pricing base
  let branches ← firstFork.publish root.interface (build "shipping" shipping false) (build "insurance" insurance false)
  let joined ← reserveBuilder false (reserveView branches.closed.interface)
  let early : Early key := ⟨root,branches,joined⟩
  let later ← laterFork.publish early.closed.interface (taxBuilder false) (build "risk" risk false)
  let final ← finalBuilder false (finalView (early.closed.interface,later.closed.interface))
  return ⟨early,later,final⟩

structure Revision {old : Int} (original : Publication old) (revised : Int) where
  root : DependencyRefresh original.early.root revised
  branches : firstFork.Refresh original.early.branches root.closed.interface
  joined : DependencyRefresh original.early.joined (reserveView branches.publication.closed.interface)
  later : laterFork.Refresh original.later (Early.closed (⟨root.closed,branches.publication,joined.closed⟩ : Early revised)).interface
  final : DependencyRefresh original.final
    (finalView ((Early.closed (⟨root.closed,branches.publication,joined.closed⟩ : Early revised)).interface,later.publication.closed.interface))

def Revision.publication {old revised : Int} {original : Publication old}
    (revision : Revision original revised) : Publication revised :=
  ⟨⟨revision.root.closed,revision.branches.publication,revision.joined.closed⟩,revision.later.publication,revision.final.closed⟩

def Revision.flags {old revised : Int} {original : Publication old} (revision : Revision original revised) : List Bool :=
  [revision.root.reused,revision.branches.left.reused,revision.branches.right.reused,revision.joined.reused,
    revision.later.left.reused,revision.later.right.reused,revision.final.reused]

def revise {old : Int} (original : Publication old) (revised : Int) (refuse : Nat → Bool) :
    Except String (Revision original revised) := do
  let root ← original.early.root.refreshDependency revised (build "pricing" pricing (refuse 0))
  let branches ← firstFork.refresh original.early.branches root.closed.interface
    (build "shipping" shipping (refuse 1)) (build "insurance" insurance (refuse 2))
  let joined ← branches.join reserveView original.early.joined (reserveBuilder (refuse 3))
  let early : Early revised := ⟨root.closed,branches.publication,joined.closed⟩
  let later ← laterFork.refresh original.later early.closed.interface (taxBuilder (refuse 4)) (build "risk" risk (refuse 5))
  let final ← later.joinWith finalView original.final (finalBuilder (refuse 6))
  return ⟨root,branches,joined,later,final⟩

def third (key : Int) := DependentComponents.pair (earlyProtocol key) laterFork.family id
def wholeProtocol (key : Int) := (DependentComponents.pair (third key).protocol finalFamily finalView).protocol
def fragments := pairFragments (pairFragments earlyFragments laterFork.fragments) settlement
def wholeBase := ((earlyBase,laterFork.base),base)

def assemble {key : Int} (publication : Publication key) : Closed (wholeProtocol key) fragments wholeBase := by
  let front := DependentComponents.closePair id publication.early.closed publication.later.closed
  let final := publication.final.reuseDependency (finalView front.interface)
    (by rw [DependentComponents.closePair_interface])
  exact DependentComponents.closePair finalView front final

abbrev Service := (EarlyService × (Local × Local)) × Local

theorem assemble_interface {key : Int} (publication : Publication key) :
    (assemble publication).interface =
      ((((publication.early.root.interface,(publication.early.branches.leftClosed.interface,publication.early.branches.rightClosed.interface)),
          publication.early.joined.interface),(publication.later.leftClosed.interface,publication.later.rightClosed.interface)),publication.final.interface) := by rfl

def locals (service : Service) : List Local :=
  [service.1.1.1.1,service.1.1.1.2.1,service.1.1.1.2.2,service.1.1.2,service.1.2.1,service.1.2.2,service.2]
def rates (service : Service) : List Int := (locals service).map Local.rate

def checkout (service : Service) (units : Int) : Action Int := do
  let mut total := 0
  for component in locals service do total := total + (← component.price units)
  return total

theorem retained_risk {old revised : Int} {original : Publication old}
    (revision : Revision original revised) (reused : revision.later.right.reused = true) (units : Int) (ledger : List String) :
    (((assemble revision.publication).interface.1.2.2.price units).run ledger) =
      (((assemble original).interface.1.2.2.price units).run ledger) := by
  rw [assemble_interface,assemble_interface]
  exact congrArg (fun viewed : Local => (viewed.price units).run ledger) (revision.later.right.interface_same reused)

theorem retained_final {old revised : Int} {original : Publication old}
    (revision : Revision original revised) (reused : revision.final.reused = true) (units : Int) (ledger : List String) :
    (((assemble revision.publication).interface.2.price units).run ledger) =
      (((assemble original).interface.2.price units).run ledger) := by
  rw [assemble_interface,assemble_interface]
  exact congrArg (fun viewed : Local => (viewed.price units).run ledger) (revision.final.interface_same reused)

end LeanPoo.Functional.SharedSettlement
