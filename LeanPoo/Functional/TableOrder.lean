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

/-- Normalize numeric comparison to the standard tree's three signs rather than
returning an arbitrary (possibly bignum) subtraction as its protocol result. -/
def integerKeyComparer (a b : Int) : Int :=
  if a = b then 0 else if a < b then -1 else 1

/-- Arbitrarily large keys still produce a bounded comparison result. This is a
semantic sign theorem, not a proof about the compiler's fixnum representation. -/
theorem integerKeyComparer_sign (a b : Int) :
    integerKeyComparer a b = -1 ∨ integerKeyComparer a b = 0 ∨ integerKeyComparer a b = 1 := by
  unfold integerKeyComparer
  split
  · simp
  · split <;> simp

/-- Normalizing signs preserves exact equality and never identifies distinct keys. -/
theorem integerKeyComparer_zero (a b : Int) : integerKeyComparer a b = 0 ↔ a = b := by
  unfold integerKeyComparer
  by_cases same : a = b
  · simp [same]
  · simp [same]; split <;> simp

/-- Normalizing signs preserves the strict numeric order used by both split sides. -/
theorem integerKeyComparer_negative (a b : Int) : integerKeyComparer a b < 0 ↔ a < b := by
  unfold integerKeyComparer
  by_cases same : a = b
  · subst b; simp
  · by_cases less : a < b <;> simp [same, less]

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


/-- The loop's observable prefix and actual number of iterator pulls, including
EOF or the first rejected upper-bound entry. Backend positioning is separate. -/
def tableRangePrefix (accept : K → Bool) : List (K × V) → List (K × V) × Nat
  | [] => ([], 1)
  | row :: rest => if accept row.1 then
      let next := tableRangePrefix accept rest
      (row :: next.1, next.2 + 1)
    else ([], 1)

/-- Prefix execution is the standard takeWhile observation, without payload maps. -/
theorem tableRangePrefix_rows (accept : K → Bool) (rows : List (K × V)) :
    (tableRangePrefix accept rows).1 = rows.takeWhile (fun row => accept row.1) := by
  induction rows with
  | nil => rfl
  | cons row rest ih => simp [tableRangePrefix, List.takeWhile_cons, ih]; split <;> rfl

/-- A range consumes exactly its returned rows plus one boundary/EOF pull. -/
theorem tableRangePrefix_pulls (accept : K → Bool) (rows : List (K × V)) :
    (tableRangePrefix accept rows).2 = (tableRangePrefix accept rows).1.length + 1 := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    cases h : accept row.1 <;> simp [tableRangePrefix, h, ih, Nat.add_assoc]

/-- An ordered backend must justify this finite window partition. The skipped
prefix fails the lower bound, the hits pass both, and the suffix fails upper.
This is an explicit backend law, not inferred from a method name or comparator. -/
structure TableRangeWindow (lower upper : K → Bool) (rows : List (K × V)) where
  before : List (K × V)
  hits : List (K × V)
  after : List (K × V)
  partition : rows = before ++ hits ++ after
  before_lower : ∀ row ∈ before, lower row.1 = false
  hits_lower : ∀ row ∈ hits, lower row.1 = true
  hits_upper : ∀ row ∈ hits, upper row.1 = true
  after_lower : ∀ row ∈ after, lower row.1 = true
  after_upper : ∀ row ∈ after, upper row.1 = false

/-- The reference full filter returns exactly the certified contiguous window. -/
theorem tableRangeWindow_filter (lower upper : K → Bool) (rows : List (K × V))
    (window : TableRangeWindow lower upper rows) :
    rows.filter (fun row => lower row.1 && upper row.1) = window.hits := by
  conv =>
    lhs
    rw [window.partition]
  rw [List.filter_append, List.filter_append]
  have before : window.before.filter (fun row => lower row.1 && upper row.1) = [] := by
    apply List.filter_eq_nil_iff.mpr; intro row member; simp [window.before_lower row member]
  have hits : window.hits.filter (fun row => lower row.1 && upper row.1) = window.hits := by
    apply List.filter_eq_self.mpr; intro row member
    simp [window.hits_lower row member, window.hits_upper row member]
  have after : window.after.filter (fun row => lower row.1 && upper row.1) = [] := by
    apply List.filter_eq_nil_iff.mpr; intro row member; simp [window.after_upper row member]
  simp [before, hits, after]

/-- A lawful positioned cursor skips exactly the lower-rejected prefix. -/
theorem tableRangeWindow_seek (lower upper : K → Bool) (rows : List (K × V))
    (window : TableRangeWindow lower upper rows) :
    rows.filter (fun row => lower row.1) = window.hits ++ window.after := by
  conv =>
    lhs
    rw [window.partition]
  rw [List.filter_append, List.filter_append]
  have before : window.before.filter (fun row => lower row.1) = [] :=
    List.filter_eq_nil_iff.mpr (by intro row member; simp [window.before_lower row member])
  have hits : window.hits.filter (fun row => lower row.1) = window.hits :=
    List.filter_eq_self.mpr window.hits_lower
  have after : window.after.filter (fun row => lower row.1) = window.after :=
    List.filter_eq_self.mpr window.after_lower
  simp [before, hits, after]

/-- Early stop after a lawful seek equals the complete reference filter. -/
theorem tableRangeWindow_correct (lower upper : K → Bool) (rows : List (K × V))
    (window : TableRangeWindow lower upper rows) :
    (tableRangePrefix upper (rows.filter (fun row => lower row.1))).1 =
      rows.filter (fun row => lower row.1 && upper row.1) := by
  rw [tableRangeWindow_seek lower upper rows window, tableRangePrefix_rows,
      tableRangeWindow_filter lower upper rows window]
  rw [List.takeWhile_append_of_pos window.hits_upper]
  have rest : window.after.takeWhile (fun row => upper row.1) = [] := by
    cases h : window.after with
    | nil => rfl
    | cons row tail =>
      have reject := window.after_upper row (by rw [h]; simp)
      simp [reject]
  simp [rest]

/-- Prefix pruning is safe when every covered key is below the seek boundary.
This is the interval law used when a Trie skips a preceding branch/subtree. -/
theorem tableSeek_skip_prefix (rows : List (Nat × V)) (limit boundary : Nat)
    (covered : ∀ row ∈ rows, row.1 < limit) (beyond : limit ≤ boundary) :
    rows.filter (fun row => decide (boundary ≤ row.1)) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro row member
  have h := covered row member
  intro accepted
  have reaches : boundary ≤ row.1 := of_decide_eq_true accepted
  omega

/-- With a backend-specific height-bounded positioning certificate, the total
abstract work is bounded by that height plus output and one sentinel pull.
No theorem here assigns a constant cost to a coroutine, recognition or GC. -/
theorem tableRangePrefix_work (height positionCost : Nat) (bounded : positionCost ≤ height + 1)
    (accept : K → Bool) (rows : List (K × V)) :
    positionCost + (tableRangePrefix accept rows).2 ≤
      height + (tableRangePrefix accept rows).1.length + 2 := by
  rw [tableRangePrefix_pulls]
  omega

/-- One finite backend pull returns the original row and unmodified tail, or EOF.
This models observation, not the host coroutine implementation. -/
def tableCursorPull (rows : List (K × V)) : Option (K × V) × List (K × V) :=
  match rows with
  | [] => (none, [])
  | row :: rest => (some row, rest)

/-- A delayed observation checks the captured origin revisions before pulling.
The work component counts backend pulls only; guards, shape checks and GC are separate. -/
def checkedTablePull (issued current : List Nat) (rows : List (K × V)) :
    Except Unit (Option (K × V) × List (K × V)) × Nat :=
  if issued = current then (.ok (tableCursorPull rows), 1) else (.error (), 0)

/-- Current metadata preserves the original payload, tail and single backend pull. -/
theorem checkedTablePull_current (issued : List Nat) (rows : List (K × V)) :
    checkedTablePull issued issued rows = (.ok (tableCursorPull rows), 1) := by
  simp [checkedTablePull]

/-- Refusal suppresses the backend pull and exposes no row or advanced tail. -/
theorem checkedTablePull_stale (issued current : List Nat) (rows : List (K × V))
    (stale : issued ≠ current) :
    checkedTablePull issued current rows = (.error (), 0) := by
  simp [checkedTablePull, stale]

/-- EOF never bypasses revision checking, including observations after exhaustion. -/
theorem checkedTablePull_eof (issued current : List Nat) :
    checkedTablePull (K := K) (V := V) issued current [] =
      if issued = current then (.ok (none, []), 1) else (.error (), 0) := by
  simp [checkedTablePull, tableCursorPull]

/-- Passing outer metadata guards delegates exactly the same single backend pull.
A stale outer origin prevents delegation even when the inner origin is current. -/
theorem checkedTablePull_nested (outerIssued outerCurrent innerIssued innerCurrent : List Nat)
    (rows : List (K × V)) :
    (if outerIssued = outerCurrent then checkedTablePull innerIssued innerCurrent rows
      else (.error (), 0)) =
    (if outerIssued = outerCurrent ∧ innerIssued = innerCurrent
      then (.ok (tableCursorPull rows), 1) else (.error (), 0)) := by
  by_cases outer : outerIssued = outerCurrent <;>
    by_cases inner : innerIssued = innerCurrent <;> simp [checkedTablePull, outer, inner]

/-- Identity iterator mapping leaves the complete finite range and its pull count
unchanged. This is the law for composing order views without re-enumerating rows;
no constant bound is assigned to the number of metadata guards. -/
theorem tableRangePrefix_identity (accept : K → Bool) (rows : List (K × V)) :
    tableRangePrefix accept (rows.map id) = tableRangePrefix accept rows := by simp

/-- Reference admission checks every intermediate carrier before proceeding.
A shape refusal is distinct from the original update error. -/
def checkedShapeUpdates {S Edit E : Type} (valid : S → Bool) (refusal : E)
    (step : S → Edit → Except E S) (state : S) : List Edit → Except E S
  | [] => if valid state then .ok state else .error refusal
  | edit :: rest => if valid state then
      match step state edit with
      | .error cause => .error cause
      | .ok next => checkedShapeUpdates valid refusal step next rest
    else .error refusal

/-- Shape-preserving persistent updates permit one initial admission. Errors are
preserved exactly; this law assumes immutable roots and admitted edit arguments.
It does not certify an arbitrary backend or the Gerbil implementation. -/
theorem checkedShapeUpdates_reuse {S Edit E : Type} (valid : S → Bool) (refusal : E)
    (step : S → Edit → Except E S)
    (preserves : ∀ state edit next, valid state = true →
      step state edit = .ok next → valid next = true)
    (state : S) (admitted : valid state = true) (edits : List Edit) :
    checkedShapeUpdates valid refusal step state edits = edits.foldlM step state := by
  induction edits generalizing state with
  | nil => simp [checkedShapeUpdates, admitted]; rfl
  | cons edit rest ih =>
    simp only [checkedShapeUpdates, admitted, ↓reduceIte, List.foldlM_cons]
    cases h : step state edit with
    | error cause => rfl
    | ok next => exact ih next (preserves state edit next admitted h)

/-- The optimized chain admits an arbitrary initial carrier before using closure. -/
def admittedShapeUpdates {S Edit E : Type} (valid : S → Bool) (refusal : E)
    (step : S → Edit → Except E S) (state : S) (edits : List Edit) : Except E S :=
  if valid state then edits.foldlM step state else .error refusal

/-- Initial rejection and every update error coincide for all inputs, not only
already admitted snapshots. A backend preservation law is still required. -/
theorem checkedShapeUpdates_admit_equiv {S Edit E : Type} (valid : S → Bool) (refusal : E)
    (step : S → Edit → Except E S)
    (preserves : ∀ state edit next, valid state = true →
      step state edit = .ok next → valid next = true)
    (state : S) (edits : List Edit) :
    checkedShapeUpdates valid refusal step state edits =
      admittedShapeUpdates valid refusal step state edits := by
  cases h : valid state with
  | true => simpa [admittedShapeUpdates, h] using
      checkedShapeUpdates_reuse valid refusal step preserves state h edits
  | false => cases edits <;> simp [checkedShapeUpdates, admittedShapeUpdates, h]

/-- Successful checked chains always return an admitted root, including retries. -/
theorem checkedShapeUpdates_valid {S Edit E : Type} (valid : S → Bool) (refusal : E)
    (step : S → Edit → Except E S) (state next : S) (edits : List Edit)
    (success : checkedShapeUpdates valid refusal step state edits = .ok next) :
    valid next = true := by
  induction edits generalizing state with
  | nil =>
    simp only [checkedShapeUpdates] at success
    split at success <;> simp_all
  | cons edit rest ih =>
    simp only [checkedShapeUpdates] at success
    split at success
    · cases h : step state edit with
      | error cause => simp [h] at success
      | ok intermediate => exact ih intermediate (by simpa [h] using success)
    · simp_all

/-- Work charged by replaying a growing prefix of n nodes at every insertion. -/
def repeatedShapeWork : Nat → Nat
  | 0 => 0
  | n + 1 => repeatedShapeWork n + 2 * n + 1

/-- Prefix replay has quadratic validation work; initial admission reuse removes
this term. Actual backend update, guard, allocation and GC costs remain separate. -/
theorem repeatedShapeWork_square (n : Nat) : repeatedShapeWork n = n * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [repeatedShapeWork, ih, Nat.mul_add, Nat.add_mul]; omega

/-- A persistent backend's shape law transfers through an explicit carrier
isomorphism. Typed edit admission and immutability remain caller premises. -/
theorem representedShapeUpdate_preserves {S T Edit E : Type}
    (carrier : Prototype.DictionaryBridge S T) (valid : S → Bool)
    (step : S → Edit → Except E S)
    (preserves : ∀ state edit next, valid state = true →
      step state edit = .ok next → valid next = true)
    (target : T) (edit : Edit) (next : T)
    (admitted : valid (carrier.fromFields target) = true)
    (success : (step (carrier.fromFields target) edit).map carrier.toFields = .ok next) :
    valid (carrier.fromFields next) = true := by
  cases result : step (carrier.fromFields target) edit with
  | error cause => simp [result, Except.map] at success
  | ok source =>
    simp [result, Except.map] at success
    subst next
    simpa [carrier.from_to] using preserves _ edit source admitted result

/-- Reuse the existing admitted-update theorem for a represented carrier,
retaining initial admission, all step errors and complete update order. -/
theorem representedShapeUpdates_reuse {S T Edit E : Type}
    (carrier : Prototype.DictionaryBridge S T) (valid : S → Bool) (refusal : E)
    (step : S → Edit → Except E S)
    (preserves : ∀ state edit next, valid state = true →
      step state edit = .ok next → valid next = true)
    (target : T) (edits : List Edit) :
    checkedShapeUpdates (fun t => valid (carrier.fromFields t)) refusal
        (fun t edit => (step (carrier.fromFields t) edit).map carrier.toFields) target edits =
      admittedShapeUpdates (fun t => valid (carrier.fromFields t)) refusal
        (fun t edit => (step (carrier.fromFields t) edit).map carrier.toFields) target edits := by
  apply checkedShapeUpdates_admit_equiv
  exact representedShapeUpdate_preserves carrier valid step preserves

end LeanPoo.Functional.OrderedDictionary
