import LeanPoo.Prototype.GeneralizedFork
import LeanPoo.Prototype.GeneralizedTariff

/-! Future-work client: one pricing object feeds independent shipping/insurance
branches, whose ordered selected views jointly configure settlement. -/
namespace LeanPoo.Tests.GeneralizedFork
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

-- Independent arithmetic and ordered execution controls: no protocol evaluation.
def expectedRates (dependency : Int) : List Int :=
  let price := 6 + dependency
  let freight := 2 + price / 5
  let cover := 3 + price / 7
  [price,freight,cover,1 + 10*(freight/3) + cover/3]

def expectedJoin (dependency : Int) : Int × Int :=
  let values := expectedRates dependency
  (values[1]!/3,values[2]!/3)

def expectedFlags (old revised : Int) : List Bool :=
  [old == revised,(6+old)/5 == (6+revised)/5,(6+old)/7 == (6+revised)/7,expectedJoin old == expectedJoin revised]

def refusal (mask stage : Nat) : Bool := (mask / 2^stage) % 2 == 1

def expectedError (old revised : Int) (mask : Nat) : Option String :=
  let flags := expectedFlags old revised
  (["pricing","shipping","insurance","settlement"].zipIdx).findSome? fun (name,stage) =>
    if refusal mask stage && !flags[stage]! then some (name ++ ".construction") else none

def expectedOutcome (values : List Int) (units : Int) (ledger : List String) :
    Option Int × Option String × List String := Id.run do
  let mut trace := ledger
  let mut total := 0
  for (name,rate) in ["pricing","shipping","insurance","settlement"].zip values do
    trace := trace ++ [name ++ ".enter"]
    if units < 0 then return (none,some "units",trace)
    if (name == "shipping" && units > 8) || (name == "settlement" && units > 4) then
      return (none,some (name ++ ".limit"),trace)
    trace := trace ++ [name,name ++ ".exit"]
    total := total + units * rate
  return (some total,none,trace)

-- Both sibling dependencies read the same preceding root, never each other.
def finiteRates (dependency : Int) : Nat → List Int
  | 0 => [1,1,1,1]
  | depth+1 =>
      let previous := finiteRates dependency depth
      [6+dependency,2+previous[0]!/5,3+previous[0]!/7,1+10*(previous[1]!/3)+previous[2]!/3]

def reassociate (A : Type) : DictionaryBridge ((A × (A × A)) × A) (A × (A × (A × A))) :=
  ⟨(fun raw => (raw.1.1,raw.1.2.1,raw.1.2.2,raw.2)),
    (fun raw => ((raw.1,(raw.2.1,raw.2.2.1)),raw.2.2.2)),fun _ => rfl,fun _ => rfl⟩

-- A genuine interleaving of sibling fragments preserves each branch's order.
def interleave : List A → List B → List (Sum A B)
  | [], right => right.map Sum.inr
  | left, [] => left.map Sum.inl
  | first::left, second::right => .inl first :: .inr second :: interleave left right

def mixed := interleave shipping insurance

def mixedClosed {dependency : Int} (publication : Publication dependency) :
    Closed (fork.family publication.root.interface) mixed fork.base :=
  publication.branches.closeInterleaved mixed (by rfl) (by rfl)

def heterogeneousLeft : Bool → Protocol Nat Nat Unit := fun _ => ⟨id,fun _ _ parent => parent.get⟩
def heterogeneousRight : Int → Protocol String Nat Bool := fun _ => ⟨String.length,fun _ _ parent => parent.get⟩
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

def run : IO Unit := do
  let mut revisions := 0
  let mut accepted := 0
  let mut refused := 0
  let mut observations := 0
  let mut finite := 0
  let mut mixedObservations := 0
  let dependencies : List Int := [0,1,2,4,8,14,29]
  let unitsCases : List Int := [-1,0,2,5,9]
  let ledgers : List (List String) := [[],["prefix"]]
  for old in dependencies do
    let original ← IO.ofExcept (publish old)
    let mixedBranches := mixedClosed original
    let groupedBranches := (fork.components original.root.interface).regroup mixedBranches
    unless rates (assemble original).interface == expectedRates old do throw (IO.userError "initial diamond arithmetic")
    for units in unitsCases do
      for ledger in ledgers do
        for (first,second) in [
            (mixedBranches.interface.1,groupedBranches.interface.1),
            (mixedBranches.interface.2,groupedBranches.interface.2)] do
          mixedObservations := mixedObservations + 1
          unless summary ((first.price units).run ledger) == summary ((second.price units).run ledger) do
            throw (IO.userError "interleaved branch method order")
    for revised in dependencies do
      for mask in List.range 16 do
        revisions := revisions + 1
        match revise original revised (refusal mask) with
        | .error error =>
          refused := refused + 1
          unless expectedError old revised mask == some error do throw (IO.userError "diamond first construction error")
          unless summary ((checkout (assemble original).interface 2).run ["retained"]) ==
              expectedOutcome (expectedRates old) 2 ["retained"] do throw (IO.userError "old diamond changed on refusal")
        | .ok revision =>
          accepted := accepted + 1
          unless (expectedError old revised mask).isNone && revision.flags == expectedFlags old revised do
            throw (IO.userError "branch or pair dependency reuse")
          let closed := assemble revision.publication
          let fields := closed.transport (reassociate Account) (reassociate Local)
          unless rates closed.interface == expectedRates revised do throw (IO.userError "revised diamond arithmetic")
          for units in unitsCases do
            for ledger in ledgers do
              for service in [closed.interface,(reassociate Local).fromFields fields.interface] do
                observations := observations + 1
                unless summary ((checkout service units).run ledger) == expectedOutcome (expectedRates revised) units ledger do
                  throw (IO.userError "shared-root cardinality / full failure prefix / representation")
    for depth in List.range 6 do
      let service := (second old).protocol.observe fragments wholeBase wholeBase depth
      unless rates service == finiteRates old depth do throw (IO.userError "fork sibling / join finite timing")
      for units in unitsCases do
        for ledger in ledgers do
          finite := finite + 1
          let expected := if depth == 0 then (none,some "missing",ledger)
            else expectedOutcome (finiteRates old (depth-1)) units ledger
          unless summary ((checkout service units).run ledger) == expected do throw (IO.userError "fork finite method capture")
  let hetero ← IO.ofExcept (heterogeneous.publish (Error := String) 0 (fun _ => .ok ⟨7,rfl⟩) (fun _ => .ok ⟨"approved",rfl⟩))
  let heteroRefresh ← IO.ofExcept (heterogeneous.refresh hetero 1
    (fun _ => .error "unchanged left builder must be skipped") (fun _ => .ok ⟨"approved",rfl⟩))
  unless heteroRefresh.left.reused && !heteroRefresh.right.reused && heteroRefresh.publication.closed.interface == (7,8) do
    throw (IO.userError "heterogeneous branch dependency refresh")
  IO.println s!"GENERALIZED-FORK-OK revisions={revisions} accepted={accepted} refused={refused} complete-observations={observations} finite-observations={finite} interleaving-observations={mixedObservations} shared-root pair-index first-refusal heterogeneous"
#eval run

-- Swapping equal-sum branch views is observably wrong for ordered join metadata.
theorem swapped_join_not_fixed (first second rate : Int) (rest : List Fragment)
    (original : Closed (joinFamily (first,second)) (.inl rate :: rest) base) (different : first ≠ second) :
    (joinFamily (second,first)).step (.inl rate :: rest) original.raw base ≠ original.raw := by
  intro fixed
  have before := congrArg Account.rate original.fixed
  have after := congrArg Account.rate fixed
  have rate_step (left right : Int) (final : Account) :
      ((joinFamily (left,right)).step (.inl rate :: rest) final base).rate = rate+10*left+right := by
    change ((family (10*left+right)).step (.inl rate :: rest) final base).rate = _
    rw [TariffComponent.family_step]
    change rate+(10*left+right) = _
    omega
  rw [rate_step] at before after
  omega

#print axioms DependencyFork.approximate_left
#print axioms DependencyFork.approximate_right
#print axioms DependencyFork.Publication.closeInterleaved
#print axioms assemble
#print axioms retained_shipping
#print axioms retained_settlement
#print axioms swapped_join_not_fixed
#print axioms DependencyFork.Refresh.join_same_view
#print axioms DependencyFork.Refresh.left_interface
#print axioms DependencyFork.Refresh.right_interface
end LeanPoo.Tests.GeneralizedFork
