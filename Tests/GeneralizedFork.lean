import Examples.Support.GeneralizedFork

/-! Future-work client: one pricing object feeds independent shipping/insurance
branches, whose ordered selected views jointly configure settlement. -/
namespace LeanPoo.Tests.GeneralizedFork
open Prototype Prototype.Generalized
open TariffComponent (Account Local Fragment Action family closeLocal mark summary stageFragments)

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

/-- Search prepared metadata in the original left-to-right refusal order. -/
def expectedErrorWithFlags (flags : List Bool) (mask : Nat) : Option String :=
  (["pricing","shipping","insurance","settlement"].zipIdx).findSome? fun (name,stage) =>
    if refusal mask stage && !flags[stage]! then some (name ++ ".construction") else none

/-- Independent refusal oracle; flags depend on keys, never on refusal masks. -/
def expectedError (old revised : Int) (mask : Nat) : Option String :=
  expectedErrorWithFlags (expectedFlags old revised) mask

/-- Sharing expected metadata preserves every mask's first refusal. -/
theorem expectedError_prepared (old revised : Int) (mask : Nat) :
    expectedErrorWithFlags (expectedFlags old revised) mask = expectedError old revised mask := rfl

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

/-- Execute the complete fork revision corpus; share mask-independent expected data while preserving every actual action and representation check. -/
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
    let retained := (assemble original).interface
    let retainedExpected := expectedOutcome (expectedRates old) 2 ["retained"]
    let mixedBranches := mixedClosed original
    let groupedBranches := (fork.components original.root.interface).regroup mixedBranches
    unless rates retained == expectedRates old do throw (IO.userError "initial diamond arithmetic")
    for units in unitsCases do
      for ledger in ledgers do
        for (first,second) in [
            (mixedBranches.interface.1,groupedBranches.interface.1),
            (mixedBranches.interface.2,groupedBranches.interface.2)] do
          mixedObservations := mixedObservations + 1
          unless summary ((first.price units).run ledger) == summary ((second.price units).run ledger) do
            throw (IO.userError "interleaved branch method order")
    for revised in dependencies do
      let expectedValues := expectedRates revised
      let expectedReuse := expectedFlags old revised
      let actions := unitsCases.flatMap (fun units => ledgers.map (fun ledger =>
        (units,ledger,expectedOutcome expectedValues units ledger)))
      for mask in List.range 16 do
        revisions := revisions + 1
        match revise original revised (refusal mask) with
        | .error error =>
          refused := refused + 1
          unless expectedErrorWithFlags expectedReuse mask == some error do throw (IO.userError "diamond first construction error")
          unless summary ((checkout retained 2).run ["retained"]) == retainedExpected do throw (IO.userError "old diamond changed on refusal")
        | .ok revision =>
          accepted := accepted + 1
          unless (expectedErrorWithFlags expectedReuse mask).isNone && revision.flags == expectedReuse do
            throw (IO.userError "branch or pair dependency reuse")
          let closed := assemble revision.publication
          let fields := closed.transport (reassociate Account) (reassociate Local)
          unless rates closed.interface == expectedValues do throw (IO.userError "revised diamond arithmetic")
          let services := [closed.interface,(reassociate Local).fromFields fields.interface]
          for (units,ledger,expected) in actions do
            for service in services do
              observations := observations + 1
              unless summary ((checkout service units).run ledger) == expected do
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
  unless revisions == 784 && accepted == 208 && refused == 576 && observations == 4160 &&
      finite == 420 && mixedObservations == 140 do throw (IO.userError "fork coverage changed")
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

#print axioms checkout_reference
#print axioms TariffComponent.checkoutMany_nil
#print axioms expectedError_prepared
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
