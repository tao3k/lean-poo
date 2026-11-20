import Std
import LeanPoo.Proof.Gerbil.SccOrdinalRows

namespace LeanPoo.Proof.Gerbil.GraphOrdinalBuckets

variable {Key Ordinal Bucket : Type} [DecidableEq Bucket]

def bucketOf (keyAt : Ordinal → Key) (bucket : Key → Bucket)
    (name : Bucket) (ordinals : List Ordinal) : List Ordinal :=
  ordinals.filter (fun i => decide (bucket (keyAt i) = name))

/-- The native implementation decrements each bucket end while traversing
ordinals backwards. This is stable insertion at the head of each slice. -/
theorem reverse_scatter_exact (keyAt : Ordinal → Key) (bucket : Key → Bucket)
    (name : Bucket) (ordinals : List Ordinal) :
    ordinals.reverse.foldl
      (fun saved i => if bucket (keyAt i) = name then i :: saved else saved) [] =
      bucketOf keyAt bucket name ordinals := by
  rw [List.foldl_reverse]
  induction ordinals with
  | nil => rfl
  | cons i rest ih =>
    simp [bucketOf] at ih
    by_cases route : bucket (keyAt i) = name <;> simp [bucketOf, route, ih]

/-- Prefix offsets isolate the selected bucket in the one packed buffer. -/
theorem prefix_slice_exact (before slice after : List Ordinal) :
    ((before ++ slice ++ after).drop before.length).take slice.length = slice := by
  rw [List.append_assoc]
  simp

def lookup [DecidableEq Key] (keyAt : Ordinal → Key) (key : Key) (ordinals : List Ordinal) :
    Option Ordinal :=
  ordinals.find? (fun i => decide (keyAt i = key))

/-- A bucket stores only ordinal words. The original key vector is the source
of equality, including distinct symbols with the same hash. -/
theorem lookup_exact [DecidableEq Key] (keyAt : Ordinal → Key) (bucket : Key → Bucket)
    (key : Key) (ordinals : List Ordinal) :
    lookup keyAt key (bucketOf keyAt bucket (bucket key) ordinals) =
      lookup keyAt key ordinals := by
  induction ordinals with
  | nil => rfl
  | cons i rest ih =>
    by_cases found : keyAt i = key
    · simp [bucketOf, lookup, found]
    · by_cases route : bucket (keyAt i) = bucket key
      · simpa [bucketOf, lookup, found, route] using ih
      · simpa [bucketOf, lookup, found, route] using ih

/-- Duplicates cannot disappear across buckets. The source symbol itself
determines the route, independently of its position or any hash collision. -/
theorem duplicate_in_same_bucket (keyAt : Ordinal → Key) (bucket : Key → Bucket)
    (ordinals : List Ordinal) (a b : Ordinal)
    (ha : a ∈ ordinals) (hb : b ∈ ordinals) (same : keyAt a = keyAt b) :
    a ∈ bucketOf keyAt bucket (bucket (keyAt a)) ordinals ∧
    b ∈ bucketOf keyAt bucket (bucket (keyAt a)) ordinals := by
  simp [bucketOf, ha, hb, same]

def distinctKeys (keyAt : Ordinal → Key) (ordinals : List Ordinal) : Prop :=
  ∀ a ∈ ordinals, ∀ b ∈ ordinals, keyAt a = keyAt b → a = b

/-- Detect duplicate keys by examining each bucket locally after checking
every owner's symbol type. A real collision between different keys is valid. -/
theorem distinct_keys_iff_distinct_buckets (keyAt : Ordinal → Key)
    (bucket : Key → Bucket) (ordinals : List Ordinal) :
    distinctKeys keyAt ordinals ↔
      ∀ id, distinctKeys keyAt (bucketOf keyAt bucket id ordinals) := by
  constructor
  · intro all id a ha b hb same
    exact all a (List.mem_filter.mp ha).1 b (List.mem_filter.mp hb).1 same
  · intro within a ha b hb same
    have members := duplicate_in_same_bucket keyAt bucket ordinals a b ha hb same
    exact within (bucket (keyAt a)) a members.1 b members.2 same

/-- Existing admission and its refusals run before any author. Replacing a
support lookup does not permit skipping/reordering the independent effects. -/
theorem after_admission_exact [DecidableEq Key] {E Result : Type} (keyAt : Ordinal → Key)
    (bucket : Key → Bucket) (admission : Except E (List Ordinal))
    (capture : (Key → Option Ordinal) → Except E Result) :
    (admission >>= fun ids => capture (fun k =>
        lookup keyAt k (bucketOf keyAt bucket (bucket k) ids))) =
    (admission >>= fun ids => capture (fun k => lookup keyAt k ids)) := by
  cases admission with
  | error e => rfl
  | ok ids =>
    have h : (fun k => lookup keyAt k (bucketOf keyAt bucket (bucket k) ids)) =
        (fun k => lookup keyAt k ids) := funext fun k => lookup_exact keyAt bucket k ids
    simp [Bind.bind, Except.bind, h]

/-- The packed owner lookup satisfies precisely the roster contract used to
publish rows by ordinal. No separate symbolic support index is required. -/
def rowRoster [DecidableEq Key] (keyAt : Fin n → Key) (bucket : Key → Bucket)
    (owners : List (Fin n)) (covers : ∀ i, i ∈ owners)
    (distinct : distinctKeys keyAt owners) : SccOrdinalRows.Roster Key n where
  key := keyAt
  position key := lookup keyAt key (bucketOf keyAt bucket (bucket key) owners)
  exact key i := by
    rw [lookup_exact]
    unfold lookup
    constructor
    · intro found
      exact of_decide_eq_true (List.find?_some (p := fun j => decide (keyAt j = key)) found)
    · intro matchKey
      have existsHit :
          (owners.find? (fun j => decide (keyAt j = key))).isSome :=
        List.find?_isSome.mpr ⟨i, covers i, decide_eq_true matchKey⟩
      cases hit : owners.find? (fun j => decide (keyAt j = key)) with
      | none => simp [hit] at existsHit
      | some j =>
        have found : keyAt j = key :=
          of_decide_eq_true (List.find?_some (p := fun k => decide (keyAt k = key)) hit)
        have same := distinct j (covers j) i (covers i) (found.trans matchKey.symm)
        simp [same]

/-- For a singleton dependency row, compare the actual symbols at the
adjacent ordinals before consulting the admitted bucket directory. The
candidate positions are hints from the current owner, without any claim
about the current or next author's row. -/
def positionNear [DecidableEq Key] (roster : SccOrdinalRows.Roster Key n)
    (near : List (Fin n)) (key : Key) : Option (Fin n) :=
  match lookup roster.key key near with
  | some pos => some pos
  | none => roster.position key

theorem position_near_exact [DecidableEq Key] (roster : SccOrdinalRows.Roster Key n)
    (near : List (Fin n)) (key : Key) :
    positionNear roster near key = roster.position key := by
  unfold positionNear
  cases found : lookup roster.key key near with
  | none => rfl
  | some pos =>
    have matched := List.find?_some (p := fun i => decide (roster.key i = key)) found
    exact ((roster.exact key pos).mpr (of_decide_eq_true matched)).symm

/-- The author result and its effects are acquired before selecting an
ordinal. A missing key still refuses the same row; a failed author cannot
be bypassed by a candidate ordinal. -/
theorem near_after_author [DecidableEq Key] {Error Event Result : Type}
    (roster : SccOrdinalRows.Roster Key n) (near : List (Fin n))
    (author : Except Error Key × List Event)
    (accept : Option (Fin n) → Except Error Result) :
    (author.1 >>= fun key => accept (positionNear roster near key), author.2) =
      (author.1 >>= fun key => accept (roster.position key), author.2) := by
  rcases author with ⟨result, events⟩
  cases result with
  | error cause => rfl
  | ok key => simp [Bind.bind, Except.bind, position_near_exact]

#print axioms position_near_exact
#print axioms near_after_author

#print axioms lookup_exact
#print axioms reverse_scatter_exact
#print axioms distinct_keys_iff_distinct_buckets
#print axioms after_admission_exact
#print axioms rowRoster

end LeanPoo.Proof.Gerbil.GraphOrdinalBuckets
