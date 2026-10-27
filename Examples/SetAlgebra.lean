import LeanPoo.Functional.TableSelection
import LeanPoo.Functional.SetStyle

/-! Access-policy algebra composes existing table revisions, inverse recovery,
styles and service lenses. This advances the collection proposal's future work. -/
namespace LeanPoo.Examples.SetAlgebra
open Functional.OrderedDictionary

/-- A finite access policy retains an unrelated permission across revisions. -/
def original : Membership Nat := fun key => decide (key = 1 ∨ key = 2 ∨ key = 5)
/-- Duplicate grant intent has ordinary set semantics, not a second write. -/
def grants : Membership Nat := fun key => decide (key = 2 ∨ key = 3 ∨ key = 4)
/-- Explicit revocation overrides grants in the complete policy operation. -/
def revoked : Membership Nat := fun key => decide (key = 2 ∨ key = 4)
/-- The proposed policy is computed by the same union-then-difference chain. -/
def proposed : Membership Nat := combineSet .diff (combineSet .union original grants) revoked

example : (proposed 1, proposed 2, proposed 3, proposed 4, proposed 5) =
    (true, false, true, false, true) := rfl

/-- A finite key inventory covers both policies without enumerating all Nat. -/
theorem outside_same (key : Nat) (outside : key ∉ [1,2,3,4,5]) : original key = proposed key := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
  rcases outside with ⟨h1, h2, h3, h4, h5⟩
  simp [original, grants, revoked, proposed, combineSet, SetOperation.choose, h1, h2, h3, h4, h5]

/-- The ordinary table delta is the complete new policy, not a second set delta API. -/
def edits : List (Change Nat Unit) := diffChanges [1,2,3,4,5]
  (membershipTable original) (membershipTable proposed)

/-- Installation preserves all keys, including the unrelated retained permission. -/
theorem installed : applyChanges edits (membershipTable original) = .ok (membershipTable proposed) := by
  apply diff_complete [1,2,3,4,5] (by decide)
  intro key outside
  simp [membershipTable, outside_same key outside]

/-- Reverse installation reuses the original whole-table inverse theorem. -/
example : applyChanges (inverseChanges edits) (membershipTable proposed) = .ok (membershipTable original) :=
  set_revision_inverse edits original proposed installed

/-- A competing revocation of key 2 makes the captured expected membership stale. -/
def winner : Nat → Option Unit := replace (membershipTable original) 2 none
example : applyChanges edits winner = .error 2 := by rfl

/-- Explicit rediscovery permits retry against the winner with unchanged failure rules. -/
example : (applyChanges (diffChanges [1,2,3,4,5] winner (membershipTable proposed)) winner).map
    (fun view => (view 1, view 2, view 3, view 4, view 5)) =
      .ok (some (), none, some (), none, some ()) := by rfl

/-- Classy publication and its failure use the existing complete style engine. -/
example : styleStep .mutable (some winner) (applyChanges edits) =
    (some winner, .error (.callback 2)) := by rfl

/-- A service membership focus preserves unrelated service metadata. -/
example : LeanPoo.Prototype.LensLaws
    (fun service : Membership Nat × String => service.1 2)
    (fun present service => (setMembership service.1 2 present, service.2)) :=
  LeanPoo.Prototype.LensLaws.productFirst.compose (set_membership_lens 2)

/-- Pure access normalization is idempotent at the observable membership boundary. -/
example : combineSet .union proposed proposed = proposed := set_union_idempotent proposed

/-- Set-style policy merging uses exactly the original mutable publication law. -/
example : setStyleCombine (E := String) .mutable (some original) (some grants)
    (fun before additions => .ok (combineSet .union before additions)) =
      ((some (combineSet .union original grants), some grants),
       .ok (combineSet .union original grants)) := rfl

/-- Linear inverse failure leaves both owners available for explicit retry. -/
example : setStyleCombine .linear (some original) (some revoked)
    (fun _ _ => (Except.error "refused" : Except String (Membership Nat))) =
      ((some original, some revoked), .error (.callback "refused")) := rfl

/-- Receiver observation never exposes Unit payloads to an element callback. -/
example : setElements ([(1, ()), (3, ()), (5, ())] : List (Nat × Unit)) = [1,3,5] := rfl

/-- Metadata refusal occurs before a delayed element is returned or consumed. -/
example : pullSetElement (K := Nat) ⟨[1, 2], [(3, ())]⟩ [1, 3] =
    (.error (), 0) := by
  apply pullSetElement_stale
  decide

/-- Already captured elements preserve exact callable identity without equality. -/
example (f : Nat → Nat) : pullSetElement ⟨[1], [(f, ())]⟩ [1] =
    (.ok (some f, ⟨[1], []⟩), 1) := pullSetElement_current [1] f []

/-- Classification routes a shared service inventory without changing its entries. -/
def inventory : List (Nat × Nat) := [(1, 10), (2, 20), (3, 30), (4, 40)]
/-- A capacity policy is a decidable Boolean, not an Any/truthiness fallback. -/
def capacityPolicy (entry : Nat × Nat) : Except String Bool := .ok (decide (entry.2 ≤ 20))

example : selectBindings capacityPolicy inventory =
    .ok ([(1, 10), (2, 20)], [(3, 30), (4, 40)]) := rfl

/-- A second-branch refinement refuses even after the first branch is admitted. -/
def admitInventory (rows : List (Nat × Nat)) : Except String (List (Nat × Nat)) :=
  if rows.any (fun entry => decide (entry.2 > 30)) then .error "capacity" else .ok rows

example : stylePartition .linear (some inventory) (fun _ =>
    preparePartitionRoots admitInventory [(1, 10), (2, 20)] [(3, 30), (4, 40)]) =
    (some inventory, .error (.callback "capacity")) := rfl

/-- Retry adjusts the policy before the single successful owner retirement. -/
example : stylePartition .linear (some inventory) (selectBindings capacityPolicy) =
    (none, .ok ([(1, 10), (2, 20)], [(3, 30), (4, 40)])) := rfl

/-- Posh/pure preserve the source; classy/mutable publish the first branch. -/
example : (stylePartition .pure (some inventory) (selectBindings capacityPolicy)).1 = some inventory := rfl
example : (stylePartition .mutable (some inventory) (selectBindings capacityPolicy)).1 =
    some [(1, 10), (2, 20)] := rfl

/-- The filtered policy remains an ordinary reversible table revision. -/
def filteredView (key : Nat) : Option Nat := if key = 1 ∨ key = 2 then some (key * 10) else none
/-- Reuse existing complete delta installation and inverse, not a partition delta. -/
def inventoryView (key : Nat) : Option Nat := if key ∈ [1, 2, 3, 4] then some (key * 10) else none

example : (applyChanges (inverseChanges (diffChanges [1, 2, 3, 4] inventoryView filteredView))
    filteredView).map (fun view => (view 1, view 2, view 3, view 4)) =
    .ok (some 10, some 20, some 30, some 40) := by rfl


/-- The broad backing and custom predicate cannot authorize an out-of-range Elt. -/
example : admitSetContract (fun _ => true) (fun _ => true) id
    (fun key : Nat => decide (key < 256)) "outside Elt" [1, 256] = .error "outside Elt" := rfl

/-- Empty membership lookup still refuses an invalid request before the backend. -/
example : (checkSetElement (fun key : Nat => decide (key < 256)) (fun _ => true)
    "outside Elt" "outside Key" 256).bind (fun _ => Except.ok false) = .error "outside Elt" := rfl

/-- A wider Elt cannot widen the physical backend key domain either. -/
example : checkSetElement (fun _ : Nat => true) (fun key => decide (key < 16))
    "outside Elt" "outside Key" 16 = .error "outside Key" := rfl

/-- Two source permissions are normalized before one complete reconstruction. -/
def permissionRows : List (Nat × Unit) := [(1, ()), (2, ())]

/-- Reuse the existing normalized-key collision model for the chosen backend. -/
def rebuildPermissions (rows : List (Nat × Unit)) : Except String (List (Nat × Unit)) :=
  Functional.VariantValidation.map (fun key => .ok key) (fun value => .ok value)
    (fun a b => decide (a = b)) "collision" rows

/-- Final admission retains the complete two-permission refinement as well as Elt. -/
def admitPermissions (rows : List (Nat × Unit)) : Except String Unit :=
  (admitSetContract (fun _ => true) (fun values => decide (values.length = 2))
    (List.map Prod.fst) (fun key => decide (key < 256)) "permission policy" rows).map (fun _ => ())

example : normalizeSetElements false (fun rows => .ok rows) (fun key => .ok (key + 10))
    (fun a b => decide (a = b)) rebuildPermissions admitPermissions permissionRows =
      .ok [(11, ()), (12, ())] := rfl

/-- No-change validation needs neither a key registry nor a business constructor. -/
example : normalizeSetElements false (fun rows => .ok rows) (fun key => .ok key)
    (fun a b => decide (a = b)) (fun _ => .error "forbidden constructor")
    admitPermissions permissionRows = .ok permissionRows := rfl

/-- Aligned descriptors do not run a redundant Elt normalizer or row inspection. -/
example : normalizeSetElements true (fun _ => .error "unexpected read")
    (fun _ : Nat => .error "unexpected Elt validation") (fun _ _ => false)
    (fun _ => .error "unexpected rebuild") admitPermissions permissionRows = .ok permissionRows := rfl

/-- A normalization collision preserves a linear owner for a separate retry. -/
example : styleStep .linear (some permissionRows)
    (normalizeSetElements false (fun rows => .ok rows) (fun _ => .ok 0)
      (fun a b => decide (a = b)) rebuildPermissions admitPermissions) =
      (some permissionRows, .error (.callback "collision")) := rfl

/-- Retrying from that same immutable source commits one ordinary successor. -/
example : styleStep .linear (some permissionRows)
    (normalizeSetElements false (fun rows => .ok rows) (fun key => .ok (key + 10))
      (fun a b => decide (a = b)) rebuildPermissions admitPermissions) =
      (none, .ok [(11, ()), (12, ())]) := rfl

/-- One service receiver, an independent grant Type, a shared policy and backing
origins. A recycled declaration cell later names 8 instead of policy 7. -/
def accessSources : List Nat := setSources 0 1 (fun (_ : Unit) => 7) [()] [2, 3]

/-- All declared dependencies were originally at revision zero. -/
def accessIssued : Nat → Option Nat := fun _ => some 0

/-- Unrelated replacement revisions cannot invalidate the original declaration. -/
def replacementChanged : Nat → Option Nat := fun id => some (if id = 8 then 1 else 0)

/-- The independent Function Type can change even when the backing is current. -/
def grantTypeChanged : Nat → Option Nat := fun id => some (if id = 1 then 1 else 0)

/-- The original policy remains watched after the caller recycles its list. -/
def accessPolicyChanged : Nat → Option Nat := fun id => some (if id = 7 then 1 else 0)

example : accessSources = [0, 1, 7, 2, 3] := rfl
example : prepareStamped accessSources accessIssued grantTypeChanged original = .error () := rfl
example : prepareStamped accessSources accessIssued accessPolicyChanged original = .error () := rfl

/-- Accepted Function grants retain their exact callable representation. -/
example (grant : Nat → Nat) :
    prepareStamped accessSources accessIssued replacementChanged grant = .ok grant := rfl

/-- Stale preparation cannot call the publication continuation or consume any
presentation's original owner. Posh/Classy reuse their existing base styles. -/
example (style : TableStyle) (publish : Membership Nat → Except Unit (Membership Nat)) :
    styleStep style (some original) (fun snapshot =>
      (prepareStamped accessSources accessIssued grantTypeChanged snapshot).bind publish) =
        (some original, .error (.callback ())) := by
  exact setSources_style_refused 0 1 (fun (_ : Unit) => 7) [()] [2, 3]
    accessIssued grantTypeChanged (by decide) style original publish

/-- Fresh preparation explicitly binds the new policy snapshot before retry. -/
example : prepareStamped accessSources accessPolicyChanged accessPolicyChanged original = .ok original := rfl

/-- A total Boolean focus can grant an absent permission through the same table
writer; no Unit payload is part of the public membership observation. -/
example :
    (modifySetMembership (E := String) .pure (some (membershipTable original)) 9
      (fun present => .ok (!present))).2.map (fun after => (after 9).isSome) = .ok true := rfl

/-- Revocation changes one permission, retaining the independent frame key. -/
example :
    (modifySetMembership (E := String) .mutable (some (membershipTable original)) 1
      (fun present => .ok (!present))).2.map (fun after => ((after 1).isSome, (after 5).isSome)) =
        .ok (false, true) := rfl

/-- False is a legitimate KEY, not an absent Option Unit value. -/
example :
    (modifySetMembership (E := String) .linear
      (some (fun key : Bool => if key then none else some ())) false
      (fun present => .ok present)).1 = none := rfl

/-- An invalid modifier outcome retains the owner for an explicit retry. -/
example (style : TableStyle) :
    modifySetMembership style (some (membershipTable original)) 1
      (fun _ => .error "approval-refused") =
        (some (membershipTable original), .error (.callback "approval-refused")) :=
  modifySetMembership_refused style _ 1 _ _ rfl

/-- The composed service lens keeps its unrelated field through success. -/
example (style : TableStyle) :
    (focusServiceModify (E := String) style (some (membershipTable original, 77)) 1
      (fun old => .ok (membershipBinding (!old.isSome)))).2 =
        .ok (replace (membershipTable original) 1 none, 77) :=
  focusServiceModify_frame style _ 77 1 _ none rfl

/-- Reentrant grant publication wins over an earlier staged revocation. -/
example (style other : TableStyle) :
    let winner := (installStyle (E := String) style ⟨3, some (membershipTable original)⟩ 3
      (replace (membershipTable original) 1 (membershipBinding true))).1
    installStyle (E := String) other winner 3
      (replace (membershipTable original) 1 (membershipBinding false)) = (winner, .error .stale) :=
  membership_install_single_winner style other 3 _ 1 true false

end LeanPoo.Examples.SetAlgebra
