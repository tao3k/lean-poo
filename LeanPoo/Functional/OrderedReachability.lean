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
