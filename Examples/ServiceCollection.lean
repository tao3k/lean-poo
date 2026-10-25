import LeanPoo.Functional.VariantValidation
import LeanPoo.Functional.CacheLookup
import LeanPoo.Functional.TableBatch
import LeanPoo.Functional.TableFocus
import LeanPoo.Functional.TableFold
import LeanPoo.Functional.TableProjection
import LeanPoo.Functional.TableSelection
import LeanPoo.Functional.TableOrder

/-! Ordered host Iterable observations over source-bound recursive service rows.
The host hash/interface and iterator laws are premises; no GC/dispatch proof is asserted.
-/
namespace Examples.ServiceCollection
open LeanPoo.Functional
open LeanPoo.Functional.ConstructionCache

/-- The two alternatives distinguish stored false from a missing table entry. -/
def values : Nat → Option (Option Bool) := fun key => if key = 0 then some (some false) else some none
example : lookupOr (values 0) (fun _ => Except.error "unexpected fallback") = .ok (some false) := rfl
example : lookupOr (values 1) (fun _ => Except.error "unexpected fallback") = .ok none := rfl

/-- A symbolic shape identity stands for the exact live object held by layouts. -/
def shapes : Nat → Option Nat := fun _ => none
example : ensureLookup shapes 0 (fun _ => Except.error "constructor failure") =
    (.error "constructor failure", shapes) := rfl
example : ensureLookup (ensureLookup shapes 0 (fun _ => Except.ok 7 : Unit → Except String Nat)).2
    0 (fun _ => Except.error "must not rebuild") =
      (.ok 7, (ensureLookup shapes 0 (fun _ => Except.ok 7 : Unit → Except String Nat)).2) :=
  ensureLookup_repeat shapes 0 7 _ _ rfl rfl

/-- Iterator pulls retain order; a wrapping refusal stops before later service rows. -/
def wrap (row : Nat) : Except String Nat := if row = 2 then .error "invalid method" else .ok (row + 10)
example : Validation.traverse wrap [0, 1] = .ok [10, 11] := rfl
example : Validation.traverse wrap [0, 2, 1] = .error "invalid method" := rfl
/-- The diagnostic builder preserves issue order and multiplicity. -/
example : Validation.gatherIssues (fun (row : Nat) => [row, row + 10]) [0, 1] = [0, 10, 1, 11] := rfl

/-- Row admission delegates the guard before wrapping and observing through FUN. -/
example : Validation.checkThen (fun (_ : Nat) => Except.ok false) "shape"
    wrap (fun _ => Except.error "consumer must not run" : Nat → Except String Nat) 2 =
      .error "shape" := rfl

open LeanPoo.Functional.OrderedDictionary

/-- Team/capacity rows model the numeric observation of Function-bearing services;
opaque callbacks remain in host rows and are never reconstructed by aggregation. -/
def capacityBefore (key : Nat) : Option (Nat × Int) :=
  match key with
  | 1 => some (10, 5)
  | 2 => some (10, -5)
  | 9 => some (90, 4)
  | _ => none

/-- A service migrates while an unrelated team's complete bucket is unchanged. -/
def capacityAfter (key : Nat) : Option (Nat × Int) :=
  if key = 1 then some (20, 7) else capacityBefore key

/-- The reference sum uses one fixed, complete finite inventory. -/
def teamCapacity (groups : Nat → Nat → Option (Nat × Int)) (team : Nat) : Option Int :=
  foldGroups [1, 2, 9] (foldView [1, 2, 9] (fun _ row => row.2)) groups team

/-- A present zero aggregate is distinct from no group; missing team 20 is absent. -/
example : [10, 20, 90].map (teamCapacity (indexView (fun _ row => row.1) capacityBefore)) =
    [some 0, none, some 4] := rfl

/-- Old and new group repair retains team 90 and publishes the migration exactly. -/
example : [10, 20, 90].map (repairGroupFolds [10, 20]
    (teamCapacity (indexView (fun _ row => row.1) capacityAfter))
    (teamCapacity (indexView (fun _ row => row.1) capacityBefore))) =
    [some (-5), some 7, some 4] := rfl

/-- Removing both owners erases the zero-sum group instead of retaining a ghost 0. -/
example : teamCapacity (indexView (fun _ row => row.1)
    (replace (replace capacityBefore 1 none) 2 none)) 10 = none := rfl

/-- Ordered source inverses recover the original zero-valued group and every
other aggregate, without assuming the sum is an invertible representation. -/
example (edits : List (Change Nat (Nat × Int)))
    (ready : applyChanges edits capacityBefore = .ok capacityAfter) :
    (applyChanges (inverseChanges edits) capacityAfter).map
      (fun restored => teamCapacity (indexView (fun _ row => row.1) restored)) =
      .ok (teamCapacity (indexView (fun _ row => row.1) capacityBefore)) := by
  rw [applyChanges_inverse edits capacityBefore capacityAfter ready]
  rfl

/-- Services share a policy key; the third service references a missing policy. -/
def policyReferences (key : Nat) : Option Nat :=
  match key with
  | 1 => some 10
  | 2 => some 10
  | 3 => some 30
  | 9 => some 90
  | _ => none

/-- Stored false is an admitted policy payload, not an absent record. -/
def policiesBefore (key : Nat) : Option Bool :=
  if key = 10 then some false else if key = 90 then some true else none

/-- Revising a shared policy affects both referencing services, preserving others. -/
def policiesAfter (key : Nat) : Option Bool :=
  replace policiesBefore 10 (some true) key

example : [1, 2, 3, 9].map (lookupJoinView (fun _ row => row) policyReferences policiesBefore) =
    [some (10, some false), some (10, some false), some (30, none), some (90, some true)] := rfl

/-- An affected inventory repairs both shared readers without replacing service 9. -/
example : [1, 2, 3, 9].map (repairGroupFolds [1, 2]
    (lookupJoinView (fun _ row => row) policyReferences policiesAfter)
    (lookupJoinView (fun _ row => row) policyReferences policiesBefore)) =
    [some (10, some true), some (10, some true), some (30, none), some (90, some true)] := rfl

/-- Simultaneous source deletion and policy insertion are observed from final
snapshots; no transient row is offered to the stable downstream projection. -/
example : [1, 3].map (lookupJoinView (fun _ row => row)
    (replace policyReferences 1 none) (replace policiesAfter 30 (some false))) =
    [none, some (30, some false)] := rfl

/-- Source inverses recover shared false policy observations exactly. -/
example : (applyChanges (inverseChanges [⟨10, some false, some true⟩]) policiesAfter).map
    (fun restored => [1, 2, 3].map (lookupJoinView (fun _ row => row) policyReferences restored)) =
      .ok [some (10, some false), some (10, some false), some (30, none)] := rfl

/-- Services and workers share a finite team catalog; each matching pair has its
own identity even when the payloads or groups coincide. -/
def placementServices : Nat → Option Nat := fun k =>
  if k = 1 ∨ k = 2 then some 10 else if k = 9 then some 90 else none

/-- Two workers share team 10 and a third remains isolated on team 90. -/
def placementWorkers : Nat → Option Nat := fun k =>
  if k = 3 ∨ k = 4 then some 10 else if k = 8 then some 90 else none

/-- Finite many-to-many expansion retains all four distinct shared-group pairs. -/
example : [(1,3), (1,4), (2,3), (2,4), (9,8), (1,8)].map
    (groupJoinView (fun _ row => row) (fun _ row => row) placementServices placementWorkers) =
    [some (10,10), some (10,10), some (10,10), some (10,10), some (90,90), none] := rfl

/-- Simultaneous migration removes two pairs, changes two survivors, and does
not invalidate the unrelated team-90 observation. -/
example : [(1,3), (1,4), (2,3), (2,4), (9,8)].map
    (groupJoinView (fun _ row => row) (fun _ row => row)
      (replace placementServices 1 (some 20)) (replace placementWorkers 4 (some 20))) =
    [none, some (20,20), some (10,10), none, some (90,90)] := rfl

/-- Old/final matching buckets include exactly the affected pair identities;
coalescing removes overlap before the projection callback is demanded. -/
example : groupJoinAffected [(1,3), (1,4), (2,3), (2,4), (9,8)] [1] [4]
    (groupJoinView (fun _ row => row) (fun _ row => row) placementServices placementWorkers)
    (groupJoinView (fun _ row => row) (fun _ row => row)
      (replace placementServices 1 (some 20)) (replace placementWorkers 4 (some 20))) =
    [(1,3), (1,4), (2,4)] := rfl

/-- Source inverses recover the shared-group pair set after a double migration. -/
example : (applyChanges (inverseChanges [⟨1, some 10, some 20⟩])
    (replace placementServices 1 (some 20))).map (fun restored =>
      groupJoinView (fun _ row => row) (fun _ row => row) restored placementWorkers (1,3)) =
    .ok (some (10,10)) := rfl
/-- One service expands to a finite route list, including a disabled empty list.
Opaque host callbacks are represented by payload identities, not reconstructed. -/
def serviceRoutes (key : Nat) (routes : List Nat) : Except String (List (Nat × Nat)) :=
  .ok (routes.map (·, key))

example : expansionRows (expansionPacket [(10, 1), (11, 1)]) = [(10, 1), (11, 1)] := rfl
example : projectedEntry (expansionProject serviceRoutes)
    (fun _ => some []) 1 = .ok none := rfl
example : reserveExpansion (E := String) [(10, 1), (11, 1)] [20] =
    .ok [(10, 1), (11, 1)] := rfl
example : reserveExpansion (E := String) [(10, 1), (10, 1)] [] =
    .error (.inr 10) := rfl
example : reserveExpansion (E := String) [(20, 1), (30, 1)] [20] =
    .error (.inr 20) := rfl

/-- A service queue extracts its first admitted callback identity in backend order. -/
def pendingServices : List (Nat × Nat) := [(1, 10), (2, 20), (9, 90)]

example : deconsBindings pendingServices = (some (1, 10), [(2, 20), (9, 90)]) := rfl
example : deconsBindings ([] : List Bool) = (none, []) := rfl
example : deconsBindings [false] = (some false, []) := rfl
example : (deconsBindings pendingServices).1.toList ++ (deconsBindings pendingServices).2 =
    pendingServices := deconsBindings_reconstruct pendingServices

/-- Required empty service dispatch preserves the supplied missing-value cause. -/
example : prepareDecons (fun (_ : List Nat) => Except.ok ())
    (fun _ => Except.ok none) (fun rows (_ : Nat) => Except.ok rows) "no value" true [] =
    .error "no value" := rfl

/-- A whole-remainder capacity rule may refuse an otherwise typed extraction. -/
example : prepareDecons (fun (rows : List Nat) => if rows.length = 1 then Except.error "capacity" else .ok ())
    (fun rows => .ok (deconsBindings rows).1) (fun rows (_ : Nat) => .ok rows.tail)
    "no value" false [1, 2] = .error "capacity" := rfl

/-- Batch service draining retains the same callback identities and backend order. -/
example : prefixBindings 2 false pendingServices = [(9, 90)] := rfl
example : prefixBindings 20 true pendingServices = pendingServices := rfl
example : prefixBindings 0 false [false, true] = [false, true] := rfl
example : prefixBindings 1 true [false, true] = [false] := rfl

/-- Even-sized service batches may skip a forbidden odd-sized intermediate root. -/
example : preparePrefix "count" (fun (rows : List Nat) =>
    if rows.length % 2 = 0 then .ok () else .error "capacity")
    2 false [1, 2, 3, 4] = .ok [3, 4] := rfl
example : preparePrefix "count" (fun (rows : List Nat) =>
    if rows.length % 2 = 0 then .ok () else .error "capacity")
    1 false [1, 2, 3, 4] = .error "capacity" := rfl
example : preparePrefix "count" (fun (_ : List Nat) => Except.ok ())
    (-1) true [1, 2] = .error "count" := rfl

/-- A finite prepared service expansion delivers its exact admitted route rows;
source installation and origin admission are premises of this example stage. -/
def expandedServiceStep (_before : List (Nat × Nat)) (rows : List (Nat × Nat)) :
    Except (String ⊕ Nat) (List (Nat × Nat) × List (Nat × Nat)) := .ok (rows, rows)

/-- Endpoint reservation reuses the existing collision protocol, retaining row
payloads while mapping route identities to their explicit finite endpoint keys. -/
def serviceEndpointStep (_before : List (Nat × Nat)) (rows : List (Nat × Nat)) :
    Except (String ⊕ Nat) (List (Nat × Nat) × List (Nat × Nat)) :=
  (reserveExpansion (E := String) (rows.map fun row => (row.1 % 10, row.2)) []).map
    fun endpoints => (endpoints, endpoints)

example : composeProjectionStep expandedServiceStep serviceEndpointStep
    ([(10, 3)], [(0, 3)]) [(32, 3), (43, 3)] =
    .ok (([(32, 3), (43, 3)], [(2, 3), (3, 3)]), [(2, 3), (3, 3)]) := rfl

/-- Different routes colliding downstream cannot expose the upstream successor. -/
example : composeProjectionStep expandedServiceStep serviceEndpointStep
    ([(10, 3)], [(0, 3)]) [(10, 3), (20, 7)] = .error (.inr 0) := rfl

/-- The unchanged cache pair remains available for corrected explicit retry. -/
example : publishProjection ([(10, 3)], [(0, 3)])
    ((composeProjectionStep expandedServiceStep serviceEndpointStep
      ([(10, 3)], [(0, 3)]) [(10, 3), (20, 7)]).map Prod.fst) =
    ([(10, 3)], [(0, 3)]) := rfl

/-- Finite joint source preparation uses the existing old-value guards on both
requests before observing a joined service row. The delivered row list is the
explicit finite middle request of this example, not a backend cost model. -/
def jointServiceStep (before : (Nat → Option Nat) × (Nat → Option Nat))
    (requests : List (Change Nat Nat) × List (Change Nat Nat)) :
    Except (Nat ⊕ Nat) (((Nat → Option Nat) × (Nat → Option Nat)) × List (Nat × Nat)) :=
  ((prepareLookupSources (applyChanges requests.1 before.1)
    (fun _ => applyChanges requests.2 before.2)).mapError Sum.inl).map fun roots =>
      (roots, [1, 2].filterMap fun key =>
        (lookupJoinView (fun _ row => row) roots.1 roots.2 key).bind fun row =>
          row.2.map fun value => (key, value))

/-- Reuse finite reservation for the downstream stage with the same error sum;
both caches remain private until every source and the final reservation accept. -/
def jointEndpointStep (_before : List (Nat × Nat)) (rows : List (Nat × Nat)) :
    Except (Nat ⊕ Nat) (List (Nat × Nat) × List (Nat × Nat)) :=
  (reserveExpansion (E := Nat) rows []).map fun endpoints => (endpoints, endpoints)

/-- Two persistent source heads share one policy dependency. -/
def jointServiceRoots : (Nat → Option Nat) × (Nat → Option Nat) :=
  (replace (fun _ => none) 1 (some 10), replace (fun _ => none) 10 (some 100))

example : (composeProjectionStep jointServiceStep jointEndpointStep
    (jointServiceRoots, [(1, 100)])
    ([⟨2, none, some 10⟩], [⟨10, some 100, some 200⟩])).map Prod.snd =
    .ok [(1, 200), (2, 200)] := rfl

/-- A valid left edit plus a stale right request cannot expose any successor. -/
example : composeProjectionStep jointServiceStep jointEndpointStep
    (jointServiceRoots, [(1, 100)])
    ([⟨2, none, some 10⟩], [⟨10, some 0, some 200⟩]) = .error (.inl 10) := rfl

example : publishProjection (jointServiceRoots, [(1, 100)])
    ((composeProjectionStep jointServiceStep jointEndpointStep
      (jointServiceRoots, [(1, 100)])
      ([⟨2, none, some 10⟩], [⟨10, some 0, some 200⟩])).map Prod.fst) =
    (jointServiceRoots, [(1, 100)]) := rfl

/-- Services carry finite cohort memberships and an integer capacity. The first
service repeats a tag; the second cancels one cohort's capacity without erasing it. -/
def cohortServices : Nat → Option (List Nat × Int) := fun key =>
  if key = 1 then some ([10, 10, 20], 3)
  else if key = 2 then some ([20], -3) else none

/-- Ordered aggregation observes each service owner once per admitted cohort. -/
def cohortCapacity (rows : Nat → Option (List Nat × Int)) : Int :=
  [1, 2].foldl (fun total key => total + ((rows key).map Prod.snd).getD 0) 0

/-- Membership migration leaves a new cohort and empties the old one; an empty
membership list would retain a primary service without contributing anywhere. -/
def migratedCohortServices := replace cohortServices 1 (some ([20, 30, 30], 3))

example : foldGroups [1, 2] cohortCapacity
    (indexKeysView (fun _ row => row.1) cohortServices) 10 = some 3 := by decide

/-- A live zero aggregate differs from an absent cohort. -/
example : foldGroups [1, 2] cohortCapacity
    (indexKeysView (fun _ row => row.1) cohortServices) 20 = some 0 := by decide

example : foldGroups [1, 2] cohortCapacity
    (indexKeysView (fun _ row => row.1) migratedCohortServices) 10 = none := by decide

example : foldGroups [1, 2] cohortCapacity
    (indexKeysView (fun _ row => row.1) migratedCohortServices) 30 = some 3 := by decide

/-- The exact delivered target delta restores the old view when inverted. -/
example : applyChanges (inverseChanges
    (diffChanges [10, 20, 30]
      (foldGroups [1, 2] cohortCapacity (indexKeysView (fun _ row => row.1) cohortServices))
      (foldGroups [1, 2] cohortCapacity (indexKeysView (fun _ row => row.1) migratedCohortServices))))
    (foldGroups [1, 2] cohortCapacity
      (indexKeysView (fun _ row => row.1) migratedCohortServices)) =
    .ok (foldGroups [1, 2] cohortCapacity
      (indexKeysView (fun _ row => row.1) cohortServices)) := by
  apply applyChanges_inverse
  apply foldGroups_keys_delta
  · decide
  · intro key changed row live bucket member
    by_cases one : key = 1
    · subst key
      simp [cohortServices, migratedCohortServices, replace] at live
      rcases live with live | live <;> subst row <;>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      all_goals rcases member with rfl | rfl | rfl <;> simp
    · simp [cohortServices, migratedCohortServices, replace, one] at live
      rcases live with ⟨_, live⟩
      subst row
      simp only [List.mem_singleton] at member
      subst bucket
      simp

/-- Worker cohorts overlap service cohorts twice. Joined identity remains the
service/worker pair; the number and order of common cohorts is unobservable. -/
def cohortWorkers : Nat → Option (List Nat × Bool) := fun key =>
  if key = 3 then some ([10, 20, 10], true)
  else if key = 4 then some ([30], true) else none

example : groupJoinKeysView (fun _ row => row.1) (fun _ row => row.1)
    cohortServices cohortWorkers (1, 3) = some (([10, 10, 20], 3), ([10, 20, 10], true)) := by decide

/-- A later nonmatching group must not overwrite the surviving first match. -/
example : groupJoinKeysView (fun _ row => row.1) (fun _ row => row.1)
    (replace cohortServices 1 (some ([10, 30], 11))) cohortWorkers (1, 3) =
    some (([10, 30], 11), ([10, 20, 10], true)) := by decide

/-- Empty membership removes all associations without deleting the source row. -/
example : groupJoinKeysView (fun _ row => row.1) (fun _ row => row.1)
    (replace cohortServices 1 (some ([], 3))) cohortWorkers (1, 3) = none := by decide

/-- Corrected explicit migration reuses the persistent old source and discovers
the newly shared cohort, without an inverse projection or a full target diff. -/
example : groupJoinKeysView (fun _ row => row.1) (fun _ row => row.1)
    migratedCohortServices cohortWorkers (1, 4) = some (([20, 30, 30], 3), ([30], true)) := by decide

/-- Finite default capacities and independently typed enabled overrides share the
same service key space; disabled overrides retain the original default. -/
def defaultCapacities : Nat → Option Int := fun key =>
  if key = 1 then some 3 else if key = 2 then some 4 else none

/-- Enabled overrides have explicit state separate from their integer payload. -/
def capacityOverrides : Nat → Option (Bool × Int) := fun key =>
  if key = 1 then some (false, 7) else none

/-- This key-local resolver also represents selecting an opaque checked Function;
it never reconstructs or normalizes the selected payload. -/
def chooseCapacity (_key : Nat) (fallback : Option Int) (override : Option (Bool × Int)) : Option Int :=
  match override with
  | some (true, capacity) => some capacity
  | _ => fallback

example : tableCombinationView chooseCapacity defaultCapacities capacityOverrides 1 = some 3 := rfl

example : tableCombinationView chooseCapacity defaultCapacities
    (replace capacityOverrides 1 (some (true, 7))) 1 = some 7 := rfl

/-- Deleting both sources suppresses even a resolver willing to invent a value. -/
example : tableCombinationView (fun _ _ _ => some (99 : Int))
    (fun _ : Nat => (none : Option Int)) (fun _ => (none : Option Bool)) 8 = none := rfl

/-- Joint edits coalesce to one key, producing one guarded target update. -/
example : applyChanges
    (diffChanges [1] (tableCombinationView chooseCapacity defaultCapacities capacityOverrides)
      (tableCombinationView chooseCapacity defaultCapacities
        (replace capacityOverrides 1 (some (true, 7)))))
    (tableCombinationView chooseCapacity defaultCapacities capacityOverrides) =
    .ok (tableCombinationView chooseCapacity defaultCapacities
      (replace capacityOverrides 1 (some (true, 7)))) := by
  apply tableCombination_delta
  · decide
  · intro key _
    rfl
  · intro key outside
    simp only [List.mem_singleton] at outside
    simp [replace, outside]

/-- A finite ordered service stream retains its original capacity payloads. -/
def capacityWindow : List (Nat × Int) := [(1, 3), (2, 4), (3, 7), (4, 9)]

example : tableRangeCursorPull (fun key => decide (key ≤ 2)) (false, capacityWindow) =
    ((some (1, 3), (false, [(2, 4), (3, 7), (4, 9)])), 1) := rfl

/-- The first upper-bound rejection is terminal, even with more source rows. -/
example : tableRangeCursorPull (fun key => decide (key ≤ 2))
    (false, [(3, (7 : Int)), (4, 9)]) = ((none, (true, [(4, 9)])), 1) := rfl

example : tableRangeCursorRows (fun key => decide (key ≤ 2)) (false, capacityWindow) =
    [(1, 3), (2, 4)] := rfl

/-- Repeated EOF observes metadata first and performs no backend pull. -/
example : checkedRangeCursorPull [1, 4] [1, 5] (fun _ : Nat => true)
    (true, ([] : List (Nat × Int))) = (.error (), 0) := rfl

example : checkedRangeCursorPull [1, 4] [1, 4] (fun _ : Nat => true)
    (true, ([] : List (Nat × Int))) = (.ok (none, (true, [])), 0) := rfl

/-- The finite catalog exposes a priority index at name 0; other names retain
their original lookup failure before a backend observer can run. -/
def servicePriorityIndex (name : Nat) : Except String (List (Nat × Nat)) :=
  if name = 0 then .ok [(10, 1), (20, 2), (30, 3)] else .error "unknown table index"

example : prepareIndexObservation (.ok ()) servicePriorityIndex
    (fun _ => (.error "observer ran" : Except String Nat)) 9 =
    .error "unknown table index" := rfl

/-- Grouped values retain complete admitted shared-owner observations. -/
def indexedServiceTeams : List (Nat × List (Nat × Int)) :=
  [(100, [(1, 3), (2, 4)]), (200, [(3, 7)])]

example : checkedIndexRangePull [1, 4] [1, 4] [9] [9] (fun team => decide (team ≤ 100))
    (false, indexedServiceTeams) =
    (.ok (some (100, [(1, 3), (2, 4)]), (false, [(200, [(3, 7)])])), 1) := rfl

/-- A sibling declaration changes the family stamp even if this backend is
unchanged; no further row is pulled, including after successful terminal EOF. -/
example : checkedIndexRangePull [1, 4] [1, 5] [9] [9] (fun _ : Nat => true)
    (true, ([] : List (Nat × List (Nat × Int)))) = (.error (), 0) := rfl

/-- Supported publication creates a new persistent index snapshot. An old issued
cursor retains its original owners; it is never redirected to the new catalog. -/
example : tableRangeCursorRows (fun _ : Nat => true) (false, indexedServiceTeams) =
    [(100, [(1, 3), (2, 4)]), (200, [(3, 7)])] := rfl

example : tableRangeCursorRows (fun _ : Nat => true)
    (false, [(100, [(1, (3 : Int))]), (200, [(2, 4), (3, 7)])]) =
    [(100, [(1, 3)]), (200, [(2, 4), (3, 7)])] := rfl

/-- Divide a finite service ledger in its declared observation order. -/
example : divisionRows capacityWindow = [[(1, 3), (2, 4)], [(3, 7), (4, 9)]] := rfl

example : (divisionRows capacityWindow).flatten = capacityWindow :=
  divisionRows_reconstruct capacityWindow

/-- Complete business admission accepts the full ledger and its first half but
refuses the second half. No admitted first part may escape this failed request. -/
def admitCapacityDivision (rows : List (Nat × Int)) : Except String Unit :=
  if rows.length = 2 && rows.any (fun row => row.1 == 3) then .error "division policy" else .ok ()

example : prepareDivision admitCapacityDivision capacityWindow = .error "division policy" := rfl

example : styleDivision .linear (some capacityWindow) (prepareDivision admitCapacityDivision) =
    (some capacityWindow, .error (.callback "division policy")) := rfl

/-- Corrected smaller input keeps the same admission policy and yields two
singletons; no empty source representation has to be synthesized. -/
example : prepareDivision admitCapacityDivision [(1, 3), (2, 4)] =
    .ok [[(1, 3)], [(2, 4)]] := rfl

/-- Empty successful linear division has zero successor capabilities. -/
example : styleDivision .linear (some []) (prepareDivision admitCapacityDivision) =
    (none, .ok []) := rfl

/-- This nonmonotone service policy uses both key and capacity, so it cannot
be replaced by a key-only binary-search assumption. -/
def serviceQuery (row : Nat × Int) : Except String Bool :=
  .ok (row.1 % 2 == 1 && row.2 > 2)

example : queryBindings serviceQuery capacityWindow = .ok (some (1, 3)) := rfl
example : queryBindings serviceQuery capacityWindow.reverse = .ok (some (3, 7)) := rfl

/-- A later failure is not observed after the first matching service. -/
def failingServiceQuery (row : Nat × Int) : Except String Bool :=
  if row.1 = 1 then .ok true else .error "later service"

example : queryBindings failingServiceQuery capacityWindow = .ok (some (1, 3)) := rfl
example : queryVisits failingServiceQuery capacityWindow = 1 := rfl

/-- Complete policy refusal precedes predicates and preserves a linear owner. -/
example : observeQuery (some capacityWindow)
    (fun rows => prepareQuery (fun _ => Except.error "policy") serviceQuery rows false) =
    (some capacityWindow, .error (.callback "policy")) := rfl

/-- A finite revision stream swaps unique service priorities after replacing a
superseded first request. Intermediate business states need not be admitted. -/
def importServiceRows : List (Nat × Int) := [(1, 30), (1, 20), (2, 10)]

/-- The unchanged third service is outside the touched-key delta. -/
def importServiceSeed : Nat → Option Int := fun key =>
  if key = 1 then some 10 else if key = 2 then some 20 else if key = 9 then some 90 else none

example : streamView importServiceRows importServiceSeed 1 = some 20 := rfl
example : streamView importServiceRows importServiceSeed 2 = some 10 := rfl
example : streamView importServiceRows importServiceSeed 9 = some 90 := rfl
example : applyChanges (streamChanges [1, 2] importServiceRows importServiceSeed) importServiceSeed =
    .ok (streamView importServiceRows importServiceSeed) := streamChanges_correct [1, 2] (by decide) _ (by simp [importServiceRows]) _
example : applyChanges (inverseChanges (streamChanges [1, 2] importServiceRows importServiceSeed))
    (streamView importServiceRows importServiceSeed) = .ok importServiceSeed := streamChanges_inverse [1, 2] (by decide) _ (by simp [importServiceRows]) _

/-- Business policy admits the original service but rejects the completed import.
The existing styleStep failure law applies without another ownership model. -/
def admitImportedServices (view : Nat → Option Int) : Except String Unit :=
  if view 1 = some 10 then .ok () else .error "service policy"

example : styleStep .linear (some importServiceSeed)
    (prepareStreamImport admitImportedServices (fun _ => .ok importServiceRows)) =
    (some importServiceSeed, .error (.callback "service policy")) := rfl

/-- Compare service capacities explicitly while preserving opaque callback handles;
zero payload comparison need not imply equal callback identity. -/
def compareServicePayload (left right : Int × Nat) : Except String Int := .ok (left.1 - right.1)

example : compareBindingRows integerKeyComparer compareServicePayload
    [(1, (10, 7)), (2, (20, 7))] [(1, (10, 8)), (2, (30, 7)), (3, (40, 8))] = .ok (-10) := rfl

/-- Presence is ordered before inspecting payloads at unrelated keys. -/
example : compareBindingRows integerKeyComparer (fun (_ _ : Int) => Except.error "not common")
    [(1, 10)] [(2, 20)] = .ok 1 := rfl

/-- A first value decision shields later callbacks and bounds paired work. -/
example : comparisonSteps integerKeyComparer compareServicePayload
    [(1, (10, 7)), (2, (20, 7))] [(1, (11, 8)), (2, (30, 7))] = 1 := rfl

/-- Constructor admission rejects a later invalid capacity before any backend
result is exposed, while opaque callback handles remain unchanged in valid rows. -/
def admitConstructorService (row : Nat × (Int × Nat)) : Except String Unit :=
  if row.2.1 < 0 then .error "negative capacity" else .ok ()

example : checkConstructorRows admitConstructorService [(1, (10, 7)), (2, (-1, 8))] =
    .error "negative capacity" := rfl
example : checkConstructorRows admitConstructorService [(1, (10, 7)), (1, (20, 8))] =
    .ok [(1, (10, 7)), (1, (20, 8))] := rfl
example : bulkFirstView [(1, (10, 7)), (1, (20, 8))] 1 = some (10, 7) := rfl
example : streamView [(1, (10, 7)), (1, (20, 8))] (fun _ => none) 1 = some (20, 8) := rfl

/-- An absent rollout does not remove the deployed callback handle. -/
example : associateOption (none : Option (Int × Nat)) (some (10, 7)) = some (10, 7) := rfl

/-- A present false request is a stored value, distinct from an absent request. -/
example : associateOption (some false) (some true) = some false := rfl

/-- Invalid requests preserve the exact refusal even when no write was requested. -/
example : admitAssociation (E := String) (fun (_ : Option Nat) => .error "stale approval")
    none (some 7) = .error "stale approval" := rfl

/-- Stored false is distinct from an absent service flag. -/
example : equalBindingOption (E := String) (fun a b : Bool => .ok (a == b))
    (some false) none = .ok false := rfl

/-- Equality observes opaque callback handles rather than executing them. -/
example : equalViewKeys (E := String) (fun a b : Nat => .ok (a == b))
    (fun (_ : Nat) => some 7) (fun _ => some 8) [1, 2] = .ok false := rfl

/-- Complete right admission precedes an otherwise true equality decision. -/
example : prepareBindingComparison (E := String)
    (fun rows : List (Nat × Int) => if rows = [(1, -1)] then .error "negative capacity" else .ok ())
    (fun _ _ => .ok true) [(1, 10)] [(1, -1)] = .error "negative capacity" := rfl

/-- A finite handle codec restores the exact known callback token, without
serializing code or proving a host parser. -/
example : decodeCollection (E := String) (fun token : Nat => .ok [(1, token)])
    (fun rows => .ok rows) (fun _ => .ok ()) 7 = .ok [(1, 7)] := rfl

/-- Port failure retains its already emitted prefix rather than inventing rollback. -/
example : marshalCollection (E := String) (fun (_ : Nat) => .ok ())
    (fun (_ : Nat) (priorBytes : List Nat) => (priorBytes ++ [2, 1, 10], .error "late codec refusal"))
    7 [] = ([2, 1, 10], .error "late codec refusal") := rfl

/-- A stored false is still a selected endpoint payload. -/
example : endpointBindings (E := String) false [(1, false), (2, true)] =
    .ok (some (1, false)) := rfl

/-- Reverse observation retains the final callback handle from the declared order. -/
example : endpointBindings (E := String) true [(1, (10, 7)), (2, (20, 8))] =
    .ok (some (2, (20, 8))) := rfl

/-- Complete admission cannot be skipped even for an otherwise immediate endpoint. -/
example : prepareQuery (E := String) (fun (_ : List Nat) => .error "invalid source")
    (fun _ => .ok true) [1, 2] true = .error "invalid source" := rfl

/-- A ledger containing a stored false flag is still nonempty. -/
example : emptyBindings (E := String) [(1, false)] = .ok false := rfl

/-- Structural bucket emptiness and admitted business emptiness are separate. -/
example : emptyBindings (A := Nat) (E := String) [] = .ok true ∧
    prepareEmpty (fun (_ : List Nat) => .error "nonempty policy") [] = .error "nonempty policy" :=
  ⟨rfl, rfl⟩

/-- A nonempty indexed ledger can derive ordered and represented constructors
without ever materializing an invalid empty business value. Function handles stay
in the finite rows, while their execution is outside this constructor proof. -/
example :
    let source : CollectionConstructors String (List (Nat × Nat)) (List (Nat × Nat)) :=
      ⟨fun _ => .error "nonempty ledger", fun rows =>
        if rows.isEmpty then .error "nonempty ledger" else .ok rows⟩
    let indexed := source.derive (fun _ => .ok ()) (fun rows => .ok (rows, 2))
    let represented := indexed.derive (fun _ => .ok ()) (fun root => .ok (some root))
    (represented.derive (fun _ => .ok ()) (fun root => .ok root)).fromRows [(1, 7), (2, 8)] =
      .ok (some ([(1, 7), (2, 8)], 2)) ∧
    represented.empty () = .error "nonempty ledger" := ⟨rfl, rfl⟩

/-- Current metadata permits a fresh attempt after stale construction refused;
no successful conversion is fabricated for the old declaration. -/
example :
    let source : CollectionConstructors String (List Nat) (List Nat) :=
      ⟨fun _ => .error "no empty", fun rows => .ok rows⟩
    (source.derive (fun _ => .error "stale") (fun rows => .ok (some rows))).fromRows [1, 2] =
      .error "stale" ∧
    (source.derive (fun _ => .ok ()) (fun rows => .ok (some rows))).fromRows [1, 2] =
      .ok (some [1, 2]) := ⟨rfl, rfl⟩

/-- A complete rank swap succeeds without constructing an invalid singleton
indexed prefix. The second component represents preserved callback handles. -/
example : VariantValidation.tableView (fun rows => Except.ok rows)
    (fun (_ : List (Nat × Nat)) => Except.ok [(20, 7), (10, 8)])
    (fun a b => a == b) (fun rows => if rows.length = 2 then Except.ok rows else .error "partial cohort")
    (fun rows => if rows.length = 2 then .ok () else .error "partial cohort")
    [(10, 7), (20, 8)] = (Except.ok [(20, 7), (10, 8)] : Except String (List (Nat × Nat))) := rfl

/-- An unchanged view remains usable even when every rebuild would refuse. -/
example : VariantValidation.tableView (fun (rows : List Nat) => Except.ok rows)
    Except.ok (fun _ _ => true) (fun _ => .error "must not rebuild")
    (fun _ => .ok ()) [1, 2] = (Except.ok [1, 2] : Except String (List Nat)) := rfl

/-- Numeric representation tags may differ while the backend key is equal.
This abstracts aliases; it does not prove floating-point primitive behavior. -/
example : (fun (a b : Int × Bool) => integerKeyComparer a.1 b.1) (1, false) (1, true) = 0 := rfl

/-- One linear positioned range retains the original callback handles and
representation tags, without sorting or rewriting admitted rows. -/
example : tableLinearRange (fun (key : Int × Bool) => decide (1 ≤ key.1))
    (fun key => decide (key.1 ≤ 2))
    [((-2, false), 7), ((1, false), 8), ((2, true), 9), ((3, false), 10)] =
      ([((1, false), 8), ((2, true), 9)], 4) := rfl

end Examples.ServiceCollection
