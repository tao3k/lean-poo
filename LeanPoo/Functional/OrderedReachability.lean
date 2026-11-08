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

namespace LeanPoo.Functional.OrderedReachability

-- Invocation-local owner-indexed marks refine row normalization in POO.
-- A fresh row token denotes membership only in THAT row, never an admission
-- certificate. Scheme uses checked vector cells; this is the abstract map model.
def RowCovers (marks : Std.HashMap Nat Nat) (token : Nat) (seen : List Nat) : Prop :=
  ∀ key, marks[key]? = some token ↔ key ∈ seen

theorem fresh_row_token (marks : Std.HashMap Nat Nat) (token : Nat)
    (older : ∀ (key value : Nat), marks[key]? = some value → value < token) :
    RowCovers marks token [] := by
  intro key
  simp only [List.not_mem_nil, iff_false]
  intro found
  exact Nat.lt_irrefl token (older key token found)

theorem row_insert_covers {marks : Std.HashMap Nat Nat} {token : Nat}
    {seen : List Nat} (covered : RowCovers marks token seen) (key : Nat) :
    RowCovers (marks.insert key token) token (key :: seen) := by
  intro query
  by_cases same : key = query
  · subst query; simp
  · have read : (marks.insert key token)[query]? = marks[query]? := by
      simp [Std.HashMap.getElem?_insert, same]
    rw [read]
    simpa [List.mem_cons, Ne.symm same] using covered query

-- List membership is the exact reverse-scan reference used by Gerbil's
-- delete-duplicates/hash default: prepend each previously unseen source key.
def referenceRow : List Nat → List Nat → List Nat → List Nat × List Nat
  | [], seen, output => (seen, output)
  | key :: rest, seen, output =>
    if key ∈ seen then referenceRow rest seen output
    else referenceRow rest (key :: seen) (key :: output)

def markedRow (token : Nat) : List Nat → List Nat → List Nat → Std.HashMap Nat Nat →
    List Nat × List Nat × Std.HashMap Nat Nat
  | [], seen, output, marks => (seen, output, marks)
  | key :: rest, seen, output, marks =>
    if marks[key]? = some token then markedRow token rest seen output marks
    else markedRow token rest (key :: seen) (key :: output) (marks.insert key token)

theorem marked_row_exact (token : Nat) (pending seen output : List Nat)
    (marks : Std.HashMap Nat Nat) (covered : RowCovers marks token seen) :
    let result := markedRow token pending seen output marks
    (result.1, result.2.1) = referenceRow pending seen output ∧
      RowCovers result.2.2 token result.1 := by
  induction pending generalizing seen output marks with
  | nil => exact ⟨rfl, covered⟩
  | cons key rest ih =>
    by_cases present : key ∈ seen
    · have indexed := (covered key).mpr present
      simp only [markedRow, referenceRow, ite_eq_left indexed, ite_eq_left present]
      exact ih seen output marks covered
    · have absent : marks[key]? ≠ some token := fun found => present ((covered key).mp found)
      simp only [markedRow, referenceRow, ite_eq_right absent, ite_eq_right present]
      exact ih (key :: seen) (key :: output) (marks.insert key token) (row_insert_covers covered key)

theorem row_mark_preserves_bound (marks : Std.HashMap Nat Nat) (key token : Nat)
    (bounded : ∀ (owner value : Nat), marks[owner]? = some value → value ≤ token) :
    ∀ (owner value : Nat), (marks.insert key token)[owner]? = some value → value ≤ token := by
  intro owner value found
  by_cases same : key = owner
  · subst owner
    have equal : token = value := by simpa using found
    omega
  · have prior : marks[owner]? = some value := by
      simpa [Std.HashMap.getElem?_insert, same] using found
    exact bounded owner value prior

theorem next_owner_token_is_fresh (marks : Std.HashMap Nat Nat) (owner : Nat)
    (bounded : ∀ (key value : Nat), marks[key]? = some value → value ≤ owner) :
    RowCovers marks (owner + 1) [] := by
  apply fresh_row_token
  intro key value found
  have := bounded key value found
  omega

theorem marked_row_preserves_bound (token : Nat) (pending seen output : List Nat)
    (marks : Std.HashMap Nat Nat)
    (bounded : ∀ (key value : Nat), marks[key]? = some value → value ≤ token) :
    ∀ (key value : Nat), (markedRow token pending seen output marks).2.2[key]? = some value →
      value ≤ token := by
  induction pending generalizing seen output marks with
  | nil => exact bounded
  | cons key rest ih =>
    by_cases known : marks[key]? = some token
    · simpa only [markedRow, ite_eq_left known] using ih seen output marks bounded
    · simpa only [markedRow, ite_eq_right known] using
        ih (key :: seen) (key :: output) (marks.insert key token)
          (row_mark_preserves_bound marks key token bounded)

-- No whole-support clearing pass is required between rows: the previous bound
-- establishes a fresh token. Only the current row's key cells are written.
theorem completed_row_allows_next_token (token : Nat) (pending seen output : List Nat)
    (marks : Std.HashMap Nat Nat)
    (bounded : ∀ (key value : Nat), marks[key]? = some value → value ≤ token) :
    RowCovers (markedRow token pending seen output marks).2.2 (token + 1) [] := by
  exact next_owner_token_is_fresh _ token
    (marked_row_preserves_bound token pending seen output marks bounded)

theorem owner_token_word_bound {owner support : Nat}
    (ownerBound : owner < support) (supportBound : support ≤ 4294967295) :
    0 < owner + 1 ∧ owner + 1 ≤ 4294967295 := by omega

example : (referenceRow [1, 2, 1].reverse [] []).2 = [2, 1] := by decide

end LeanPoo.Functional.OrderedReachability

namespace LeanPoo.Functional.OrderedReachability
-- Dense owner IDs preserve equality, so normalizing encoded rows cannot
-- reorder, merge or drop a different source owner. The decoder round trip
-- transports this exact order back to the public owner identity.
theorem reference_row_map (encode : Nat → Nat) (injective : Function.Injective encode)
    (pending seen output : List Nat) :
    referenceRow (pending.map encode) (seen.map encode) (output.map encode) =
      ((referenceRow pending seen output).1.map encode,
       (referenceRow pending seen output).2.map encode) := by
  induction pending generalizing seen output with
  | nil => rfl
  | cons key rest ih =>
    have present : encode key ∈ seen.map encode ↔ key ∈ seen := by
      constructor
      · intro found
        rcases List.mem_map.mp found with ⟨prior, member, same⟩
        have equal := injective same
        simpa only [equal] using member
      · intro found
        exact List.mem_map.mpr ⟨key, found, rfl⟩
    simp only [List.map_cons, referenceRow]
    by_cases known : key ∈ seen
    · simp only [ite_eq_left known, ite_eq_left (present.mpr known)]
      exact ih seen output
    · have missing : encode key ∉ seen.map encode := fun h => known (present.mp h)
      simp only [ite_eq_right known, ite_eq_right missing]
      exact ih (key :: seen) (key :: output)


end LeanPoo.Functional.OrderedReachability

namespace LeanPoo.Functional.OrderedReachability

-- The Scheme vector is filled with ZERO rather than absent HashMap entries.
-- Positive row tokens make both representations fresh, including owner ID 0.
theorem zero_marks_fresh (marks : Std.HashMap Nat Nat) (token : Nat)
    (positive : 0 < token)
    (zeroed : ∀ (key value : Nat), marks[key]? = some value → value = 0) :
    RowCovers marks token [] := by
  apply fresh_row_token
  intro key value found
  rw [zeroed key value found]
  exact positive

end LeanPoo.Functional.OrderedReachability

namespace LeanPoo.Functional.OrderedReachability

-- Invocation-local row workspace: [0, read) is unread input and [write, end)
-- is the already retained suffix. Keeping read ≤ write prevents a compacting
-- store from changing ANY future read. This is storage, not source evidence.
def RowSuffix (buffer : Array Nat) (write : Nat) (output : List Nat) : Prop :=
  write + output.length ≤ buffer.size ∧
    ∀ offset, offset < output.length → buffer[write + offset]! = output[offset]!

theorem row_buffer_store_preserves_unread (buffer : Array Nat) (read write key : Nat)
    (ordered : read ≤ write) (positive : 0 < read) :
    ∀ offset, offset < read - 1 →
      (buffer.set! (write - 1) key)[offset]! = buffer[offset]! := by
  intro offset before
  exact Array.getElem!_set!_ne buffer (write - 1) offset key (by omega)

theorem row_buffer_store_prepends (buffer : Array Nat) (write key : Nat)
    (output : List Nat) (suffix : RowSuffix buffer write output) (positive : 0 < write) :
    RowSuffix (buffer.set! (write - 1) key) (write - 1) (key :: output) := by
  rcases suffix with ⟨bounded, cells⟩
  constructor
  · simp only [List.length_cons, Array.size_set!]; omega
  · intro offset before
    cases offset with
    | zero =>
      simp only [Nat.add_zero, List.getElem!_cons_zero]
      apply Array.getElem!_set!_self
      omega
    | succ offset =>
      have location : write - 1 + (offset + 1) = write + offset := by omega
      rw [location, Array.getElem!_set!_ne buffer (write - 1) (write + offset) key (by omega)]
      simpa using cells offset (by simpa using before)

theorem row_buffer_next_cursors (read write capacity : Nat)
    (ordered : read ≤ write) (bounded : write ≤ capacity) (positive : 0 < read) :
    read - 1 ≤ write - 1 ∧ write - 1 < capacity ∧
      read - 1 ≤ write ∧ write ≤ capacity := by omega

-- Decoding after ID normalization gives the same PUBLIC owner order. This
-- composes with marked_row_exact and reference_row_map, including owner ID 0.
theorem decode_normalized_row (encode decode : Nat → Nat)
    (roundtrip : ∀ owner, decode (encode owner) = owner) (pending : List Nat) :
    ((referenceRow (pending.map encode) [] []).2.map decode) =
      (referenceRow pending [] []).2 := by
  have injective : Function.Injective encode := by
    intro a b same
    simpa only [roundtrip] using congrArg decode same
  have mapped := reference_row_map encode injective pending [] []
  simp only [List.map_nil] at mapped
  rw [mapped]
  simp [List.map_map, Function.comp_def, roundtrip]

end LeanPoo.Functional.OrderedReachability

namespace LeanPoo.Functional.OrderedReachability

-- A standard vector-copy chunk consumes exactly the corresponding row preceding.
-- Concatenating chunks cannot reorder/drop/duplicate a retained numeric ID.
theorem chunked_row_exact (preceding row : List Nat) (count : Nat) :
    (preceding ++ row.take count) ++ row.drop count = preceding ++ row := by
  rw [List.append_assoc, List.take_append_drop]

theorem row_copy_chunk_bounds (cursor stop used capacity : Nat)
    (pending : cursor < stop) (available : used < capacity) :
    let count := min (stop - cursor) (capacity - used)
    0 < count ∧ cursor + count ≤ stop ∧ used + count ≤ capacity := by
  dsimp
  constructor
  · omega
  · constructor <;> omega

end LeanPoo.Functional.OrderedReachability

namespace LeanPoo.Functional.OrderedReachability

-- Representation switching consumes no source, builder, or approval callback.
-- Any bounded list prefix can hand its EXACT state to native indexed visitation.
theorem list_run_add (reads : Nat → List Nat) (first rest : Nat)
    (todo seen : List Nat) :
    listRun reads (first + rest) todo seen =
      listRun reads rest (listRun reads first todo seen).1
        (listRun reads first todo seen).2 := by
  induction first generalizing todo seen with
  | zero => simp [listRun]
  | succ first ih =>
    cases todo with
    | nil =>
      cases rest <;> simp [listRun]
    | cons key tail =>
      by_cases found : key ∈ seen
      · simpa [listRun, found, Nat.succ_add] using ih tail seen
      · simpa [listRun, found, Nat.succ_add] using
          ih (reads key ++ tail) (key :: seen)

theorem indexed_handoff_exact (reads : Nat → List Nat) (first rest : Nat)
    (todo seen : List Nat) (index : Std.HashMap Nat Unit)
    (covered : Covers index (listRun reads first todo seen).2) :
    let prior := listRun reads first todo seen
    let result := indexedRun reads rest prior.1 prior.2 index
    (result.1, result.2.1) = listRun reads (first + rest) todo seen := by
  rw [list_run_add]
  exact (indexed_prefix_exact reads rest _ _ index covered).1

-- Dense storage is installed only when its whole directory is bounded by the
-- reached support. The multiplier is a private resource policy, not a latency
-- theorem or public tuning flag. Small/sparse queries allocate no full bitmap.
theorem dense_workspace_charged_to_reached (support entered capacity : Nat)
    (density : support ≤ 32 * entered) (frames : capacity ≤ 2 * entered) :
    support + 8 * capacity ≤ 48 * entered := by omega

theorem sparse_state_below_switch (support entered multiplier : Nat)
    (below : multiplier * entered < support) :
    ¬ support ≤ multiplier * entered := by omega

-- Parent cursor storage grows geometrically. Only active depth is copied;
-- retained capacity remains bounded by twice the newly required depth.
theorem frame_growth_capacity (depth capacity : Nat)
    (full : depth = capacity) (positive : 0 < capacity) :
    depth + 1 ≤ 2 * capacity ∧ 2 * capacity < 2 * (depth + 1) := by omega

-- Historical graph indices retain exact owner identity. They are structural
-- data only; ownership never turns them into successful currentness evidence.
theorem graph_index_owner_separation {Owner : Type} {indexed current : Owner}
    (bound : indexed = current) {other : Owner} (different : other ≠ current) :
    indexed ≠ other := by
  intro same
  exact different (same.symm.trans bound)

end LeanPoo.Functional.OrderedReachability

namespace LeanPoo.Functional.OrderedReachability

theorem clipped_frame_growth (depth capacity support : Nat)
    (full : depth = capacity) (positive : 0 < capacity)
    (fresh : depth + 1 ≤ support) :
    depth + 1 ≤ min support (2 * capacity) ∧
      min support (2 * capacity) ≤ 2 * capacity := by omega

def capturedQuery (lookup : Nat → Option Nat) (walk : Nat → List Nat) (root : Nat) :
    Option (List Nat) := (lookup root).map walk

theorem missing_root_refuses (lookup : Nat → Option Nat) (walk : Nat → List Nat)
    (root : Nat) (missing : lookup root = none) :
    capturedQuery lookup walk root = none := by simp [capturedQuery, missing]

theorem zero_root_is_present (lookup : Nat → Option Nat) (walk : Nat → List Nat)
    (root : Nat) (present : lookup root = some 0) :
    capturedQuery lookup walk root = some (walk 0) := by simp [capturedQuery, present]

end LeanPoo.Functional.OrderedReachability

namespace LeanPoo.Functional.OrderedReachability

-- A proof-only potential: captured owner rows are finite and all targets belong
-- to the catalog. Runtime queries do NOT enumerate this catalog or use fuel.
def unreadCharge (reads : Nat → List Nat) (seen : List Nat) : List Nat → Nat
  | [] => 0
  | key :: rest => (if key ∈ seen then 0 else (reads key).length + 1) +
      unreadCharge reads seen rest

theorem absent_mark_charge (reads : Nat → List Nat) (seen catalog : List Nat)
    (key : Nat) (absent : key ∉ catalog) :
    unreadCharge reads (key :: seen) catalog = unreadCharge reads seen catalog := by
  induction catalog with
  | nil => rfl
  | cons head tail ih =>
    have different : head ≠ key := by intro same; subst head; exact absent (by simp)
    have missing : key ∉ tail := by intro member; exact absent (by simp [member])
    simpa [unreadCharge, List.mem_cons, different] using
      congrArg (fun n => (if head ∈ seen then 0 else (reads head).length + 1) + n) (ih missing)

theorem fresh_mark_charge (reads : Nat → List Nat) (seen catalog : List Nat)
    (unique : catalog.Nodup) (key : Nat) (member : key ∈ catalog) (fresh : key ∉ seen) :
    unreadCharge reads seen catalog =
      (reads key).length + 1 + unreadCharge reads (key :: seen) catalog := by
  induction catalog with
  | nil => simp at member
  | cons head tail ih =>
    rcases List.nodup_cons.mp unique with ⟨headAbsent, tailUnique⟩
    by_cases same : head = key
    · subst head
      have unchanged := absent_mark_charge reads seen tail key headAbsent
      simp [unreadCharge, fresh, unchanged]
    · have inTail : key ∈ tail := by simpa [Ne.symm same] using member
      have step := ih tailUnique inTail
      have absentHead : head ≠ key := same
      by_cases known : head ∈ seen
      · simpa [unreadCharge, List.mem_cons, absentHead, known] using step
      · simp only [unreadCharge, List.mem_cons, absentHead, false_or, known, ite_false]
        omega

def queryPotential (reads : Nat → List Nat) (catalog todo seen : List Nat) : Nat :=
  todo.length + unreadCharge reads seen catalog

theorem visited_step_decreases (reads : Nat → List Nat) (catalog tail seen : List Nat)
    (key : Nat) :
    queryPotential reads catalog tail seen <
      queryPotential reads catalog (key :: tail) seen := by
  simp [queryPotential]

theorem fresh_step_decreases (reads : Nat → List Nat) (catalog tail seen : List Nat)
    (unique : catalog.Nodup) (key : Nat) (member : key ∈ catalog) (fresh : key ∉ seen) :
    queryPotential reads catalog (reads key ++ tail) (key :: seen) <
      queryPotential reads catalog (key :: tail) seen := by
  have charged := fresh_mark_charge reads seen catalog unique key member fresh
  simp only [queryPotential, List.length_append, List.length_cons]
  omega

theorem finite_ordered_query_finishes (reads : Nat → List Nat) (catalog : List Nat)
    (unique : catalog.Nodup)
    (closed : ∀ key ∈ catalog, ∀ dep ∈ reads key, dep ∈ catalog)
    (fuel : Nat) (todo seen : List Nat)
    (supported : ∀ key ∈ todo, key ∈ catalog)
    (budget : queryPotential reads catalog todo seen ≤ fuel) :
    (listRun reads fuel todo seen).1 = [] := by
  induction fuel generalizing todo seen with
  | zero =>
    have empty : todo = [] := by
      cases todo with
      | nil => rfl
      | cons head tail => simp only [queryPotential, List.length_cons] at budget; omega
    simp [empty, listRun]
  | succ fuel ih =>
    cases todo with
    | nil => simp [listRun]
    | cons key tail =>
      have tailSupported : ∀ dep ∈ tail, dep ∈ catalog := by
        intro dep member
        exact supported dep (by simp [member])
      by_cases known : key ∈ seen
      · have decreases := visited_step_decreases reads catalog tail seen key
        have enough : queryPotential reads catalog tail seen ≤ fuel := by omega
        simpa [listRun, known] using ih tail seen tailSupported enough
      · have member : key ∈ catalog := supported key (by simp)
        have decreases := fresh_step_decreases reads catalog tail seen unique key member known
        have enough : queryPotential reads catalog (reads key ++ tail) (key :: seen) ≤ fuel := by omega
        have nextSupported : ∀ dep ∈ reads key ++ tail, dep ∈ catalog := by
          intro dep inNext
          rcases List.mem_append.mp inNext with inRow | inTail
          · exact closed key member dep inRow
          · exact tailSupported dep inTail
        simpa [listRun, known] using ih (reads key ++ tail) (key :: seen) nextSupported enough

end LeanPoo.Functional.OrderedReachability

namespace LeanPoo.Functional.OrderedReachability
open LeanPoo.Functional.StrongComponents

-- Opaque recipe tokens model HOST IDENTITY, not equality of build outputs.
theorem unique_catalog_member_lookup (catalog : List (Nat × Nat))
    (unique : catalog.Pairwise (fun a b => a.1 ≠ b.1))
    (key token : Nat) (member : (key, token) ∈ catalog) :
    (Std.HashMap.ofList catalog)[key]? = some token := by
  have distinct : catalog.Pairwise (fun a b => (a.1 == b.1) = false) := by
    simpa using unique
  exact Std.HashMap.getElem?_ofList_of_mem (by simp) distinct member

theorem indexed_first_recipe (catalog : List (Nat × Nat))
    (unique : catalog.Pairwise (fun a b => a.1 ≠ b.1)) (key : Nat) :
    (Std.HashMap.ofList catalog)[key]? =
      ((catalog.find? (fun entry => entry.1 == key)).map Prod.snd) := by
  cases found : catalog.find? (fun entry => entry.1 == key) with
  | none =>
    have missing : ∀ entry ∈ catalog, entry.1 ≠ key := by
      simpa using (List.find?_eq_none.mp found)
    apply Std.HashMap.getElem?_ofList_of_contains_eq_false
    apply Bool.eq_false_iff.mpr
    intro present
    have member := List.contains_iff_mem.mp present
    rcases List.mem_map.mp member with ⟨entry, inCatalog, same⟩
    exact missing entry inCatalog same
  | some entry =>
    have inCatalog := List.mem_of_find?_eq_some found
    have same : entry.1 = key := by simpa using List.find?_some found
    simpa only [same, Option.map_some] using
      unique_catalog_member_lookup catalog unique entry.1 entry.2 inCatalog

-- Replacing list membership by a captured index cannot reorder selected owners.
theorem indexed_filter_exact (keys seen : List Nat) (index : Std.HashMap Nat Unit)
    (covered : Covers index seen) :
    keys.filter (fun key => decide (index[key]? = some ())) =
      keys.filter (fun key => decide (key ∈ seen)) := by
  apply List.filter_congr
  intro key _
  simp only [covered key]

def affectedBy {n : Nat} (edge : Fin n → Fin n → Bool) (roots : Fin n → Prop)
    (owner : Fin n) : Prop := ∃ root, roots root ∧ Reach edge owner root

theorem affected_seed {n : Nat} (edge : Fin n → Fin n → Bool) (roots : Fin n → Prop)
    (owner : Fin n) (seed : roots owner) : affectedBy edge roots owner :=
  ⟨owner, seed, .refl owner⟩

theorem affected_reader {n : Nat} (edge : Fin n → Fin n → Bool) (roots : Fin n → Prop)
    {consumer provider : Fin n} (direct : edge consumer provider = true)
    (dirty : affectedBy edge roots provider) : affectedBy edge roots consumer := by
  rcases dirty with ⟨root, seed, path⟩
  exact ⟨root, seed, .step direct path⟩

theorem affected_least {n : Nat} (edge : Fin n → Fin n → Bool)
    (roots included : Fin n → Prop)
    (seed : ∀ owner, roots owner → included owner)
    (reader : ∀ consumer provider, edge consumer provider = true →
      included provider → included consumer)
    {owner : Fin n} (dirty : affectedBy edge roots owner) : included owner := by
  rcases dirty with ⟨root, isRoot, path⟩
  induction path with
  | refl vertex => exact seed vertex isRoot
  | @step consumer provider _ direct _ ih => exact reader consumer provider direct (ih isRoot)

-- Every consumer whose recipe/dependency declaration changed is a seed.
-- Therefore the OLD reverse index and the NEW graph have identical affected
-- closure over the union catalog. Added/removed owners are also seeds; absence
-- is encoded as an empty row. This never reuses successful admission evidence.
theorem affected_dependency_rewrite {n : Nat}
    (old fresh : Fin n → Fin n → Bool) (roots : Fin n → Prop)
    (unchanged : ∀ consumer, ¬ roots consumer → ∀ provider,
      old consumer provider = fresh consumer provider) (owner : Fin n) :
    affectedBy old roots owner ↔ affectedBy fresh roots owner := by
  constructor
  · intro dirty
    apply affected_least old roots (affectedBy fresh roots)
      (affected_seed fresh roots) _ dirty
    intro consumer provider direct affected
    by_cases changed : roots consumer
    · exact affected_seed fresh roots consumer changed
    · apply affected_reader fresh roots _ affected
      simpa only [← unchanged consumer changed provider] using direct
  · intro dirty
    apply affected_least fresh roots (affectedBy old roots)
      (affected_seed old roots) _ dirty
    intro consumer provider direct affected
    by_cases changed : roots consumer
    · exact affected_seed old roots consumer changed
    · apply affected_reader old roots _ affected
      simpa only [unchanged consumer changed provider] using direct

end LeanPoo.Functional.OrderedReachability

namespace LeanPoo.Functional.OrderedReachability

theorem indexed_catalog_capture_trace (catalog : List (Nat × Nat))
    (rows : List (Nat × List Nat)) :
    captureDecisions (fun key => (Std.HashMap.ofList catalog).contains key) rows =
      captureDecisions (fun key => decide (key ∈ catalog.map Prod.fst)) rows := by
  have equal : (fun key => (Std.HashMap.ofList catalog).contains key) =
      (fun key => decide (key ∈ catalog.map Prod.fst)) := by
    funext key
    apply Bool.eq_iff_iff.mpr
    simp
  rw [equal]

end LeanPoo.Functional.OrderedReachability

namespace LeanPoo.Functional.OrderedReachability

-- A completed captured prefix may discard its symbolic row copies only while
-- the private packed words and row lengths still reconstruct exactly that
-- prefix. Extra words in the unfinished owner must not become a completed row.
-- This is a semantic projection; native reconstruction streams existing chunks.
def restoreRows : List Nat → List Nat → List (List Nat)
  | [], _ => []
  | size :: sizes, targets =>
      targets.take size :: restoreRows sizes (targets.drop size)

theorem restore_completed_prefix (rows : List (List Nat)) (unfinished : List Nat) :
    restoreRows (rows.map List.length) (rows.flatten ++ unfinished) = rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    simp only [List.map_cons, List.flatten_cons, List.append_assoc, restoreRows,
      List.take_left, List.drop_left]
    exact congrArg (List.cons row) ih

theorem restore_before_wide_fallback (rows : List (List Nat))
    (unfinished current : List Nat) :
    restoreRows (rows.map List.length) (rows.flatten ++ unfinished) ++ [current] =
      rows ++ [current] := by
  rw [restore_completed_prefix]

theorem restore_empty_rows :
    restoreRows [0, 0, 0] [] = [[], [], []] := rfl

-- Original symbols are decoded from the same owner roster; numeric words do
-- not become public identities. Row order, not just set membership, survives.
theorem restore_original_owners (rows : List (List Nat))
    (encode decode : Nat → Nat) (roundtrip : ∀ key, decode (encode key) = key) :
    (restoreRows ((rows.map (List.map encode)).map List.length)
      (rows.map (List.map encode)).flatten).map (List.map decode) = rows := by
  have restored := restore_completed_prefix (rows.map (List.map encode)) []
  simp only [List.append_nil] at restored
  rw [restored]
  simp only [List.map_map]
  have identity : (fun row : List Nat => List.map decode (List.map encode row)) = id := by
    funext row
    simp only [List.map_map]
    have same : decode ∘ encode = id := by funext key; exact roundtrip key
    rw [same]
    simp
  change List.map (fun row => List.map decode (List.map encode row)) rows = rows
  rw [identity]
  simp

def projectedRow (rows : List (List Nat)) (owner : Nat) : List Nat :=
  (restoreRows (rows.map List.length) rows.flatten)[owner]?.getD []

theorem projected_row_exact (rows : List (List Nat)) (owner : Nat) :
    projectedRow rows owner = rows[owner]?.getD [] := by
  have restored := restore_completed_prefix rows []
  simp only [List.append_nil] at restored
  simp only [projectedRow, restored]

theorem projected_missing_owner (rows : List (List Nat)) (owner : Nat)
    (missing : rows[owner]? = none) : projectedRow rows owner = [] := by
  rw [projected_row_exact, missing]
  rfl

theorem projected_query_prefix (rows : List (List Nat)) (fuel : Nat)
    (todo seen : List Nat) :
    listRun (projectedRow rows) fuel todo seen =
      listRun (fun owner => rows[owner]?.getD []) fuel todo seen := by
  have equal : projectedRow rows = (fun owner => rows[owner]?.getD []) := by
    funext owner
    exact projected_row_exact rows owner
  rw [equal]

-- The pure fallback does not call authors. Once each effectful owner read has
-- independently completed, reconstructing its rows preserves the ordinary
-- first-refusal trace. It is not permission to cache or merge those reads.
theorem restored_admission_trace (owners : List Nat) (rows : List (List Nat))
    (unfinished : List Nat) (supported : Nat → Bool) :
    captureDecisions supported
      (owners.zip (restoreRows (rows.map List.length) (rows.flatten ++ unfinished))) =
      captureDecisions supported (owners.zip rows) := by
  rw [restore_completed_prefix]

-- Modeled symbolic retention is a separate charge from original author reads,
-- packed edges, decoding at a real fallback, and the final query output.
def retainedSymbolicEdges (required : Bool) (rows : List (List Nat)) : Nat :=
  if required then rows.flatten.length else 0

theorem query_projection_retains_no_symbolic_edges (rows : List (List Nat)) :
    retainedSymbolicEdges false rows = 0 := rfl

theorem required_rows_charge_every_edge (rows : List (List Nat)) :
    retainedSymbolicEdges true rows = rows.flatten.length := rfl

example : restoreRows [0, 2, 1] [2, 1, 0, 7, 8] = [[], [2, 1], [0]] := by decide

end LeanPoo.Functional.OrderedReachability

namespace LeanPoo.Functional.OrderedReachability

-- Root admission must retain Option presence. The total row helper used in
-- finite-prefix algebra is not permission to turn a missing owner into an empty
-- present row. Native queries keep the existing owner-index refusal first.
def projectedRowOption (rows : List (List Nat)) (owner : Nat) : Option (List Nat) :=
  (restoreRows (rows.map List.length) rows.flatten)[owner]?

theorem projected_row_presence (rows : List (List Nat)) (owner : Nat) :
    projectedRowOption rows owner = rows[owner]? := by
  have restored := restore_completed_prefix rows []
  simp only [List.append_nil] at restored
  simp only [projectedRowOption, restored]

theorem projected_missing_refused (rows : List (List Nat)) (owner : Nat)
    (missing : rows[owner]? = none) : projectedRowOption rows owner = none := by
  rw [projected_row_presence, missing]

theorem projected_empty_owner_present (rows : List (List Nat)) (owner : Nat)
    (present : rows[owner]? = some []) : projectedRowOption rows owner = some [] := by
  rw [projected_row_presence, present]

theorem guarded_projected_query (rows : List (List Nat)) (fuel root : Nat) :
    (projectedRowOption rows root).map
      (fun _ => listRun (projectedRow rows) fuel [root] []) =
    rows[root]?.map (fun _ => listRun (fun owner => rows[owner]?.getD []) fuel [root] []) := by
  rw [projected_row_presence, projected_query_prefix]

example : projectedRowOption [[], [0]] 0 = some [] := by decide
example : projectedRowOption [[], [0]] 2 = none := by decide

end LeanPoo.Functional.OrderedReachability


namespace LeanPoo.Functional.OrderedReachability

/-- Pure captured data only. The Scheme proper-list/cycle check remains before
this interval; no author, object getter or source approval is shared here. -/
def stagedRow {α β : Type} (symbolic : α → Bool) (lookup : α → Option β)
    (row : List α) : Option (List β) :=
  if row.all symbolic then row.mapM lookup else none

def fusedRow {α β : Type} (symbolic : α → Bool) (lookup : α → Option β)
    (row : List α) : Option (List β) :=
  row.mapM (fun key => if symbolic key then lookup key else none)

theorem fused_row_eq {α β : Type} (symbolic : α → Bool) (lookup : α → Option β)
    (row : List α) : fusedRow symbolic lookup row = stagedRow symbolic lookup row := by
  induction row with
  | nil => rfl
  | cons key rest ih =>
    cases hs : symbolic key <;> cases ht : rest.all symbolic <;>
      cases hv : lookup key <;>
      simp only [fusedRow, stagedRow, ht, ↓reduceIte] at ih <;>
      simp [fusedRow, stagedRow, List.mapM_cons, List.all_cons, hs, ht, hv, ih]

/-- Both paths stop at the same first rejected owner. A refused row never
permits the next author callback, even when its first invalid item differs. -/
def admissionTrace {α β : Type} (encode : List α → Option (List β)) :
    List (Nat × List α) → List (Nat × Bool)
  | [] => []
  | (owner, row) :: rest =>
    if (encode row).isSome then (owner, true) :: admissionTrace encode rest
    else [(owner, false)]

theorem fused_owner_trace {α β : Type} (symbolic : α → Bool) (lookup : α → Option β)
    (rows : List (Nat × List α)) :
    admissionTrace (fusedRow symbolic lookup) rows =
      admissionTrace (stagedRow symbolic lookup) rows := by
  have same : fusedRow symbolic lookup = stagedRow symbolic lookup := by
    funext row
    exact fused_row_eq symbolic lookup row
  rw [same]

/-- The same owner-to-ID table used for edge encoding also admits the roster.
No separate duplicate table is required before author acquisition. -/
def assignOwners (index : Std.HashMap Nat Nat) (position : Nat) :
    List Nat → Std.HashMap Nat Nat
  | [] => index
  | key :: rest => assignOwners (index.insert key position) (position + 1) rest

theorem assigned_size_bound (index : Std.HashMap Nat Nat) (position : Nat)
    (keys : List Nat) :
    (assignOwners index position keys).size ≤ index.size + keys.length := by
  induction keys generalizing index position with
  | nil => simp [assignOwners]
  | cons key rest ih =>
    have tail := ih (index.insert key position) (position + 1)
    have head := Std.HashMap.size_insert_le (m := index) (k := key) (v := position)
    simp only [assignOwners, List.length_cons]
    omega

theorem assigned_size_exact (index : Std.HashMap Nat Nat) (position : Nat)
    (keys : List Nat) :
    (assignOwners index position keys).size = index.size + keys.length ↔
      keys.Nodup ∧ ∀ key ∈ keys, key ∉ index := by
  induction keys generalizing index position with
  | nil => simp [assignOwners]
  | cons key rest ih =>
    have bound := assigned_size_bound (index.insert key position) (position + 1) rest
    by_cases present : key ∈ index
    · have size : (index.insert key position).size = index.size := by
        simp [Std.HashMap.size_insert, present]
      simp only [assignOwners, List.length_cons]
      constructor
      · intro exactSize
        omega
      · intro valid
        exact False.elim (valid.2 key (by simp) present)
    · have size : (index.insert key position).size = index.size + 1 := by
        simp [Std.HashMap.size_insert, present]
      constructor
      · intro exactSize
        have tailSize :
            (assignOwners (index.insert key position) (position + 1) rest).size =
              (index.insert key position).size + rest.length := by
          simpa [assignOwners, size, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using exactSize
        obtain ⟨unique, fresh⟩ := (ih (index.insert key position) (position + 1)).mp tailSize
        refine ⟨List.nodup_cons.mpr ⟨?_, unique⟩, ?_⟩
        · intro repeated
          exact fresh key repeated (by simp)
        · intro other member
          rcases List.mem_cons.mp member with same | tail
          · simpa [same] using present
          · intro old
            exact fresh other tail (by simp [old])
      · rintro ⟨unique, fresh⟩
        obtain ⟨notRepeated, uniqueTail⟩ := List.nodup_cons.mp unique
        have freshTail : ∀ other ∈ rest, other ∉ index.insert key position := by
          intro other member prior
          have alternatives := Std.HashMap.mem_insert.mp prior
          rcases alternatives with same | old
          · have eqKey : key = other := by simpa using same
            exact notRepeated (eqKey ▸ member)
          · exact fresh other (by simp [member]) old
        have tailSize := (ih (index.insert key position) (position + 1)).mpr ⟨uniqueTail, freshTail⟩
        simpa [assignOwners, size, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using tailSize

theorem empty_owner_index_admits_exactly_nodup (keys : List Nat) :
    (assignOwners ∅ 0 keys).size = keys.length ↔ keys.Nodup := by
  simpa using assigned_size_exact (∅ : Std.HashMap Nat Nat) 0 keys

end LeanPoo.Functional.OrderedReachability
