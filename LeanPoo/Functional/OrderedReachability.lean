-- SPDX-License-Identifier: Apache-2.0 AND LGPL-2.1-or-later
import Std.Data.HashMap.Lemmas
import LeanPoo.Functional.StrongComponents

namespace LeanPoo.Functional.OrderedReachability

-- The index contains Unit markers only. It is a private visited set, not a
-- cache of source approvals or business outcomes. Adjacency is captured data.
def Covers (index : Std.HashMap Nat Unit) (seen : List Nat) : Prop :=
  ∀ key, index[key]? = some () ↔ key ∈ seen

theorem empty_covers : Covers (∅ : Std.HashMap Nat Unit) [] := by
  intro key
  simp

theorem insert_covers {index : Std.HashMap Nat Unit} {seen : List Nat}
    (covered : Covers index seen) (key : Nat) :
    Covers (index.insert key ()) (key :: seen) := by
  intro query
  by_cases same : key = query
  · subst query
    simp
  · have read : (index.insert key ())[query]? = index[query]? := by
      simp [Std.HashMap.getElem?_insert, same]
    rw [read]
    simpa [List.mem_cons, Ne.symm same] using covered query

-- Fuel exposes every finite prefix; it is a proof device, not a native timeout.
def listRun (reads : Nat → List Nat) : Nat → List Nat → List Nat → List Nat × List Nat
  | 0, todo, seen => (todo, seen)
  | _ + 1, [], seen => ([], seen)
  | fuel + 1, key :: rest, seen =>
    if key ∈ seen then listRun reads fuel rest seen
    else listRun reads fuel (reads key ++ rest) (key :: seen)

def indexedRun (reads : Nat → List Nat) :
    Nat → List Nat → List Nat → Std.HashMap Nat Unit →
      List Nat × List Nat × Std.HashMap Nat Unit
  | 0, todo, seen, index => (todo, seen, index)
  | _ + 1, [], seen, index => ([], seen, index)
  | fuel + 1, key :: rest, seen, index =>
    if index[key]? = some () then indexedRun reads fuel rest seen index
    else indexedRun reads fuel (reads key ++ rest) (key :: seen) (index.insert key ())

theorem indexed_prefix_exact (reads : Nat → List Nat) (fuel : Nat)
    (todo seen : List Nat) (index : Std.HashMap Nat Unit) (covered : Covers index seen) :
    let result := indexedRun reads fuel todo seen index
    (result.1, result.2.1) = listRun reads fuel todo seen ∧ Covers result.2.2 result.2.1 := by
  induction fuel generalizing todo seen index with
  | zero => exact ⟨rfl, covered⟩
  | succ fuel ih =>
    cases todo with
    | nil => exact ⟨rfl, covered⟩
    | cons key rest =>
      by_cases found : key ∈ seen
      · have present := (covered key).mpr found
        simp only [indexedRun, listRun, ite_eq_left present, ite_eq_left found]
        exact ih rest seen index covered
      · have absent : index[key]? ≠ some () := fun h => found ((covered key).mp h)
        simp only [indexedRun, listRun, ite_eq_right absent, ite_eq_right found]
        exact ih (reads key ++ rest) (key :: seen) (index.insert key ()) (insert_covers covered key)

theorem list_seen_unique (reads : Nat → List Nat) (fuel : Nat)
    (todo seen : List Nat) (unique : seen.Nodup) :
    (listRun reads fuel todo seen).2.Nodup := by
  induction fuel generalizing todo seen with
  | zero => exact unique
  | succ fuel ih =>
    cases todo with
    | nil => exact unique
    | cons key rest =>
      by_cases found : key ∈ seen
      · simpa only [listRun, ite_eq_left found] using ih rest seen unique
      · simpa only [listRun, ite_eq_right found] using
          ih (reads key ++ rest) (key :: seen) (List.nodup_cons.mpr ⟨found, unique⟩)

theorem indexed_seen_unique (reads : Nat → List Nat) (fuel : Nat) (root : Nat) :
    (indexedRun reads fuel [root] [] ∅).2.1.Nodup := by
  have exactPrefix := (indexed_prefix_exact reads fuel [root] [] ∅ empty_covers).1
  have same := congrArg Prod.snd exactPrefix
  change (indexedRun reads fuel [root] [] ∅).2.1 = (listRun reads fuel [root] []).2 at same
  rw [same]
  exact list_seen_unique reads fuel [root] [] (by simp)

end LeanPoo.Functional.OrderedReachability

namespace LeanPoo.Functional.OrderedReachability

-- CSR: one source-order row-offset directory plus packed target IDs. This
-- semantic row projection is not an implementation that copies Array.toList.
def compactRow (targets : Array Nat) (offset count : Nat) : List Nat :=
  (targets.toList.drop offset).take count

theorem compact_row_exact (priorRows : List (List Nat)) (row : List Nat)
    (suffix : List (List Nat)) :
    compactRow (priorRows ++ row :: suffix).flatten.toArray priorRows.flatten.length row.length = row := by
  simp [compactRow, List.flatten_append]

theorem compact_row_bounds (priorRows : List (List Nat)) (row : List Nat)
    (suffix : List (List Nat)) :
    priorRows.flatten.length + row.length ≤ (priorRows ++ row :: suffix).flatten.length := by
  simp only [List.flatten_append, List.flatten_cons, List.length_append]
  omega

-- Physical DFS frames borrow row suffixes, instead of allocating a cons for
-- each pending edge. Empty-frame retirement is silent in the old work stream.
def framePending (frames : List (List Nat)) : List Nat := frames.flatten

def frameNext : List (List Nat) → Option (Nat × List (List Nat))
  | [] => none
  | [] :: rest => frameNext rest
  | (key :: tail) :: rest => some (key, tail :: rest)

theorem next_none_pending_empty {frames : List (List Nat)}
    (finished : frameNext frames = none) : framePending frames = [] := by
  induction frames with
  | nil => rfl
  | cons row rest ih =>
    cases row with
    | nil => simpa [framePending] using ih finished
    | cons key tail => simp [frameNext] at finished

theorem next_some_pending {frames : List (List Nat)} {key : Nat}
    {rest : List (List Nat)} (next : frameNext frames = some (key, rest)) :
    framePending frames = key :: framePending rest := by
  induction frames with
  | nil => simp [frameNext] at next
  | cons row tail ih =>
    cases row with
    | nil => simpa [framePending] using ih next
    | cons head remaining =>
      simp only [frameNext, Option.some.injEq, Prod.mk.injEq] at next
      rcases next with ⟨rfl, rfl⟩
      rfl

def frameRun (reads : Nat → List Nat) :
    Nat → List (List Nat) → List Nat → List (List Nat) × List Nat
  | 0, frames, seen => (frames, seen)
  | fuel + 1, frames, seen =>
    match frameNext frames with
    | none => ([], seen)
    | some (key, rest) =>
      if key ∈ seen then frameRun reads fuel rest seen
      else frameRun reads fuel (reads key :: rest) (key :: seen)

theorem frames_preserve_ordered_prefix (reads : Nat → List Nat) (fuel : Nat)
    (frames : List (List Nat)) (seen : List Nat) :
    let result := frameRun reads fuel frames seen
    (framePending result.1, result.2) = listRun reads fuel (framePending frames) seen := by
  induction fuel generalizing frames seen with
  | zero => rfl
  | succ fuel ih =>
    cases next : frameNext frames with
    | none =>
      have empty := next_none_pending_empty next
      simp only [frameRun, next]
      rw [empty]
      rfl
    | some pending =>
      rcases pending with ⟨key, rest⟩
      have same := next_some_pending next
      simp only [frameRun, next]
      rw [same]
      by_cases known : key ∈ seen
      · simp only [listRun, ite_eq_left known]
        exact ih rest seen
      · simp only [listRun, ite_eq_right known]
        have step := ih (reads key :: rest) (key :: seen)
        simpa only [framePending, List.flatten_cons] using step

end LeanPoo.Functional.OrderedReachability
namespace LeanPoo.Functional.OrderedReachability

-- Private numeric Tarjan state: zero is unvisited, discovery slots are
-- encoded as slot+1, and retired component IDs start strictly above support.
-- This is a representation refinement; SCC acceptance still requires the
-- independent ComponentWitness spanning/quotient certificate.
def activeCode (slot : Nat) : Nat := slot + 1
def retiredCode (support component : Nat) : Nat := support + 1 + component

theorem active_code_positive (slot : Nat) : 0 < activeCode slot := by
  simp [activeCode]

theorem active_code_bounded {slot support : Nat} (bound : slot < support) :
    activeCode slot ≤ support := by
  simp only [activeCode]
  omega

theorem retired_code_outside (support component : Nat) :
    support < retiredCode support component := by
  simp only [retiredCode]
  omega

theorem active_retired_disjoint {slot support : Nat} (bound : slot < support)
    (component : Nat) : activeCode slot ≠ retiredCode support component := by
  have := active_code_bounded bound
  have := retired_code_outside support component
  omega

theorem active_code_injective {left right : Nat} :
    activeCode left = activeCode right ↔ left = right := by
  simp [activeCode]

theorem retired_code_roundtrip (support component : Nat) :
    retiredCode support component - support - 1 = component := by
  simp only [retiredCode]
  omega

theorem state_word_bound {support component : Nat}
    (supported : component < support) (fits : 2 * support ≤ 4294967295) :
    retiredCode support component ≤ 4294967295 := by
  simp only [retiredCode]
  omega

-- Every stacked activation belongs to a distinct discovered owner. Reserving
-- one frame/member cell per support owner cannot overflow on fresh entry.
theorem fresh_frame_capacity {entered : List Nat} {owner support : Nat}
    (unique : entered.Nodup) (bounded : ∀ key ∈ entered, key < support)
    (present : owner < support) (fresh : owner ∉ entered) :
    entered.length < support := by
  have allBounded : owner :: entered ⊆ List.range support := by
    intro key member
    rcases List.mem_cons.mp member with equal | prior
    · subst key; exact List.mem_range.mpr present
    · exact List.mem_range.mpr (bounded key prior)
  have size := (List.nodup_cons.mpr ⟨fresh, unique⟩).length_le_of_subset allBounded
  simpa only [List.length_cons, List.length_range, Nat.add_one_le_iff] using size

end LeanPoo.Functional.OrderedReachability
namespace LeanPoo.Functional.OrderedReachability

-- Normalization remains within the pure captured-row boundary. It may share
-- support lookup with ID encoding, but cannot move or omit an author callback.
theorem normalized_support_iff (row : List Nat) (supported : Nat → Prop) :
    (∀ key ∈ row.eraseDups, supported key) ↔ (∀ key ∈ row, supported key) := by
  simp

def captureDecisions (supported : Nat → Bool) : List (Nat × List Nat) → List (Nat × Bool)
  | [] => []
  | (owner, row) :: rest =>
    if row.all supported then (owner, true) :: captureDecisions supported rest
    else [(owner, false)]

theorem normalized_all (row : List Nat) (supported : Nat → Bool) :
    row.eraseDups.all supported = row.all supported := by
  apply Bool.eq_iff_iff.mpr
  simp

theorem normalized_capture_trace (supported : Nat → Bool)
    (rows : List (Nat × List Nat)) :
    captureDecisions supported (rows.map (fun row => (row.1, row.2.eraseDups))) =
      captureDecisions supported rows := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    rcases row with ⟨owner, deps⟩
    simp only [List.map_cons, captureDecisions, normalized_all]
    split
    · rw [ih]
    · rfl

-- This proves same admission and first rejected owner on captured data. It
-- does not authenticate a callback, mutable input, source version or Context.
example : captureDecisions (fun key => key < 3)
    [(0, [1, 1]), (1, [4, 4]), (2, [0])] = [(0, true), (1, false)] := by decide

end LeanPoo.Functional.OrderedReachability

namespace LeanPoo.Functional.OrderedReachability
open LeanPoo.Functional.StrongComponents

-- Reuse the existing unbounded Graph path relation, rather than creating a
-- second model for numeric IDs. Every edge is transported in the same direction.
theorem transport_reach {n m : Nat} {source : Fin n → Fin n → Bool}
    {target : Fin m → Fin m → Bool} (encode : Fin n → Fin m)
    (direct : ∀ a b, source a b = true → target (encode a) (encode b) = true)
    {a b : Fin n} (path : Reach source a b) : Reach target (encode a) (encode b) := by
  induction path with
  | refl a => exact .refl (encode a)
  | @step a next b edge _ ih => exact .step (direct a next edge) ih

def encodedEdge {n m : Nat} (source : Fin n → Fin n → Bool)
    (decode : Fin m → Fin n) : Fin m → Fin m → Bool :=
  fun a b => source (decode a) (decode b)

theorem encoded_reach_exact {n m : Nat} (source : Fin n → Fin n → Bool)
    (encode : Fin n → Fin m) (decode : Fin m → Fin n)
    (roundtrip : ∀ owner, decode (encode owner) = owner) (a b : Fin n) :
    Reach (encodedEdge source decode) (encode a) (encode b) ↔ Reach source a b := by
  constructor
  · intro path
    have mapped := transport_reach decode (fun _ _ edge => edge) path
    simpa only [roundtrip] using mapped
  · intro path
    exact transport_reach encode (by
      intro left right edge
      simpa only [encodedEdge, roundtrip] using edge) path

theorem encoded_components_exact {n m : Nat} (source : Fin n → Fin n → Bool)
    (encode : Fin n → Fin m) (decode : Fin m → Fin n)
    (roundtrip : ∀ owner, decode (encode owner) = owner) (a b : Fin n) :
    (Reach (encodedEdge source decode) (encode a) (encode b) ∧
     Reach (encodedEdge source decode) (encode b) (encode a)) ↔
      (Reach source a b ∧ Reach source b a) := by
  rw [encoded_reach_exact source encode decode roundtrip a b,
      encoded_reach_exact source encode decode roundtrip b a]

theorem encoded_owner_identity {n m : Nat} (encode : Fin n → Fin m)
    (decode : Fin m → Fin n) (roundtrip : ∀ owner, decode (encode owner) = owner)
    {a b : Fin n} (sameID : encode a = encode b) : a = b := by
  simpa only [roundtrip] using congrArg decode sameID

end LeanPoo.Functional.OrderedReachability
