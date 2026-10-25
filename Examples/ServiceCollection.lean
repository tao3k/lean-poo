import LeanPoo.Functional.CacheLookup
import LeanPoo.Functional.TableFold
import LeanPoo.Functional.TableProjection
import LeanPoo.Functional.TableSelection

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

end Examples.ServiceCollection
