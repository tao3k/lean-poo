import LeanPoo.Functional.TableIndex
import LeanPoo.Functional.TableRepresentation

/-! Explicit comparator transport and finite ordered range observations. Sorting
is supplied by the host library under the stated ordering laws; no seek cost or
runtime/GC claim follows from these extensional proofs. -/
namespace LeanPoo.Functional.OrderedDictionary
open Prototype (DictionaryBridge)
variable {K L V : Type}

/-- The host three-way comparer must agree with key equality and a strict order. -/
structure TableComparerLaws (compare : K → K → Int) : Prop where
  sign : ∀ a b, compare a b = -1 ∨ compare a b = 0 ∨ compare a b = 1
  zero : ∀ a b, compare a b = 0 ↔ a = b
  reverse : ∀ a b, compare a b = -(compare b a)
  trans : ∀ a b c, compare a b < 0 → compare b c < 0 → compare a c < 0

/-- Explicit pullback compares target keys by their source representations. -/
def transportComparer (keys : DictionaryBridge K L) (compare : K → K → Int) : L → L → Int :=
  fun a b => compare (keys.fromFields a) (keys.fromFields b)

/-- Source ordering, including negative representations, is preserved exactly. -/
theorem transportComparer_apply (keys : DictionaryBridge K L) (compare : K → K → Int) (a b : K) :
    transportComparer keys compare (keys.toFields a) (keys.toFields b) = compare a b := by
  simp [transportComparer, keys.from_to]

/-- A genuine isomorphism transports all required order laws. -/
theorem transportComparer_laws (keys : DictionaryBridge K L) (compare : K → K → Int)
    (laws : TableComparerLaws compare) : TableComparerLaws (transportComparer keys compare) where
  sign a b := laws.sign _ _
  zero a b := by
    simp only [transportComparer, laws.zero]
    constructor
    · intro h; simpa only [keys.to_from] using congrArg keys.toFields h
    · intro h; rw [h]
  reverse a b := laws.reverse _ _
  trans a b c := laws.trans _ _ _

/-- An optional endpoint separates unboundedness from every admitted key value. -/
structure TableBound (K : Type) where
  key : K
  inclusive : Bool

/-- Lower and upper signs use the same comparer, including open equal endpoints. -/
def withinTableRange (compare : K → K → Int) (lower upper : Option (TableBound K)) (key : K) : Bool :=
  (match lower with
   | none => true
   | some bound => if bound.inclusive then decide (compare key bound.key ≥ 0)
                   else decide (compare key bound.key > 0)) &&
  (match upper with
   | none => true
   | some bound => if bound.inclusive then decide (compare key bound.key ≤ 0)
                   else decide (compare key bound.key < 0))

/-- Range observations filter an ordered enumeration without changing row payloads. -/
def tableRangeRows (compare : K → K → Int) (lower upper : Option (TableBound K))
    (rows : List (K × V)) : List (K × V) :=
  rows.filter (fun row => withinTableRange compare lower upper row.1)

/-- Bound transport keeps endpoint inclusion independent of its representation. -/
def transportTableBound (keys : DictionaryBridge K L) (bound : TableBound K) : TableBound L :=
  ⟨keys.toFields bound.key, bound.inclusive⟩

/-- A mapped key is accepted by exactly the same interval as its source key. -/
theorem withinTableRange_transport (keys : DictionaryBridge K L) (compare : K → K → Int)
    (lower upper : Option (TableBound K)) (key : K) :
    withinTableRange (transportComparer keys compare) (lower.map (transportTableBound keys))
      (upper.map (transportTableBound keys)) (keys.toFields key) =
    withinTableRange compare lower upper key := by
  cases lower <;> cases upper <;>
    simp [withinTableRange, transportTableBound, transportComparer, keys.from_to]

/-- Isomorphic range selection commutes with mapping while preserving opaque rows. -/
theorem tableRangeRows_transport (keys : DictionaryBridge K L) (compare : K → K → Int)
    (lower upper : Option (TableBound K)) (rows : List (K × V)) :
    tableRangeRows (transportComparer keys compare) (lower.map (transportTableBound keys))
      (upper.map (transportTableBound keys)) (rows.map (fun row => (keys.toFields row.1, row.2))) =
    (tableRangeRows compare lower upper rows).map (fun row => (keys.toFields row.1, row.2)) := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    simp only [List.map_cons, tableRangeRows, List.filter_cons, withinTableRange_transport]
    split <;> simp_all [tableRangeRows]

/-- Range filtering preserves the host sort's strict key order. -/
theorem tableRangeRows_ordered (compare : K → K → Int) (lower upper : Option (TableBound K))
    (rows : List (K × V)) (ordered : rows.Pairwise (fun a b => compare a.1 b.1 < 0)) :
    (tableRangeRows compare lower upper rows).Pairwise (fun a b => compare a.1 b.1 < 0) :=
  ordered.filter _

/-- Every returned binding has both original payload identity and accepted bounds. -/
theorem tableRangeRows_member (compare : K → K → Int) (lower upper : Option (TableBound K))
    (rows : List (K × V)) (row : K × V) :
    row ∈ tableRangeRows compare lower upper rows ↔
      row ∈ rows ∧ withinTableRange compare lower upper row.1 = true := by
  simp [tableRangeRows]

/-- A reversed interval fails before enumeration; equal open endpoints are allowed. -/
def checkedTableRange (compare : K → K → Int) (lower upper : Option (TableBound K))
    (rows : List (K × V)) : Except Unit (List (K × V)) :=
  match lower, upper with
  | some lo, some hi => if compare lo.key hi.key > 0 then .error ()
                       else .ok (tableRangeRows compare lower upper rows)
  | _, _ => .ok (tableRangeRows compare lower upper rows)

/-- Reversed bounds have a distinct refusal, never an apparently empty success. -/
theorem checkedTableRange_reversed (compare : K → K → Int) (lo hi : TableBound K)
    (rows : List (K × V)) (reversed : compare lo.key hi.key > 0) :
    checkedTableRange compare (some lo) (some hi) rows = .error () := by
  simp [checkedTableRange, reversed]

/-- Extensional recovery of an index enumeration recovers every range observation. -/
theorem tableRangeRows_restore (compare : K → K → Int) (lower upper : Option (TableBound K))
    (before restored : List (K × V)) (recovered : restored = before) :
    tableRangeRows compare lower upper restored = tableRangeRows compare lower upper before := by rw [recovered]

end LeanPoo.Functional.OrderedDictionary
