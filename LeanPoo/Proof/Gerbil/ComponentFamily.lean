import Std

namespace ComponentFamily
variable {K V S E : Type}

-- A prepared family owns its key sequence. choose may fail or arbitrarily
-- modify caller state, including a caller's original key-list value.
abbrev Choose (K V S E : Type) := K → S → Except E V × S
def capture (choose : Choose K V S E) : List K → S → Except E (List (K × V)) × S
  | [], state => (.ok [], state)
  | key :: rest, state =>
      match choose key state with
      | (.error reason, next) => (.error reason, next)
      | (.ok value, next) =>
          match capture choose rest next with
          | (.error reason, final) => (.error reason, final)
          | (.ok entries, final) => (.ok ((key, value) :: entries), final)

theorem capture_keys (choose : Choose K V S E) (keys : List K) (state : S)
    (entries : List (K × V)) (final : S)
    (accepted : capture choose keys state = (.ok entries, final)) :
    entries.map Prod.fst = keys := by
  induction keys generalizing state entries final with
  | nil =>
    simp only [capture, Prod.mk.injEq, Except.ok.injEq] at accepted
    simp [← accepted.1]
  | cons key rest ih =>
    cases step : choose key state with
    | mk outcome next =>
      cases outcome with
      | error reason => simp [capture, step] at accepted
      | ok value =>
        cases suffix : capture choose rest next with
        | mk result last =>
          cases result with
          | error reason => simp [capture, step, suffix] at accepted
          | ok tail =>
            simp only [capture, step, suffix, Prod.mk.injEq, Except.ok.injEq] at accepted
            rw [← accepted.1]
            simpa using congrArg (List.cons key) (ih next tail last suffix)

variable [DecidableEq K]
def domain (entries : List (K × V)) (key : K) : Bool :=
  decide (key ∈ entries.map Prod.fst)

theorem captured_domain (choose : Choose K V S E) (keys : List K) (state : S)
    (entries : List (K × V)) (final : S)
    (accepted : capture choose keys state = (.ok entries, final)) (query : K) :
    domain entries query = decide (query ∈ keys) := by
  simp only [domain, capture_keys choose keys state entries final accepted]

-- None models a non-symbol member. Refusal position is retained even though
-- today's Scheme public error message does not expose that position.
def firstRefusal (contains : K → Bool) : List (Option K) → Nat → Option Nat
  | [], _ => none
  | member :: rest, offset =>
      if (match member with | none => false | some key => contains key) then
        firstRefusal contains rest (offset + 1)
      else some offset

theorem same_first_refusal (keys : List K) (entries : List (K × V))
    (same : entries.map Prod.fst = keys) (members : List (Option K)) (offset : Nat) :
    firstRefusal (domain entries) members offset =
      firstRefusal (fun key => decide (key ∈ keys)) members offset := by
  have lookup : domain entries = (fun key => decide (key ∈ keys)) := by
    funext query
    simp [domain, same]
  rw [lookup]

-- The admitted continuation is arbitrary, including errors and state effects.
-- Both guards refuse before invoking it, in the SAME original caller state.
def enter (contains : K → Bool) (members : List (Option K))
    (next : S → Except (Option Nat) V × S) (state : S) : Except (Option Nat) V × S :=
  match firstRefusal contains members 0 with
  | some position => (.error (some position), state)
  | none => next state

theorem same_entry (keys : List K) (entries : List (K × V))
    (same : entries.map Prod.fst = keys) (members : List (Option K))
    (next : S → Except (Option Nat) V × S) (state : S) :
    enter (domain entries) members next state =
      enter (fun key => decide (key ∈ keys)) members next state := by
  simp only [enter, same_first_refusal keys entries same members 0]

-- Distinct singleton requests at successive list positions do quadratic
-- memq work. This is cons-cell work, NOT a claim of O(1) hashing or CPU time.
def linearFamilyWork : Nat → Nat
  | 0 => 0
  | n + 1 => linearFamilyWork n + (n + 1)

theorem triangular_work (n : Nat) : 2 * linearFamilyWork n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [linearFamilyWork, Nat.mul_add, ih]
    simp [Nat.mul_add, Nat.mul_comm]
    omega

example : firstRefusal (fun n : Nat => decide (n ∈ [1, 2]))
    [some 2, none, some 7] 0 = some 1 := by decide
example : domain [(1, false), (2, true)] 1 = true := by decide

-- A map-domain theorem alone does not show that an adapter query is pure.
-- Origin retirement is monotone, even if later metadata looks native again.
def eligible (prior current : Bool) : Bool := prior && current
theorem retired_stays_retired (current : Bool) : eligible false current = false := by
  simp [eligible]

abbrev MemberAction (S E : Type) := S → Except E Bool × S
def guardedMember (origin : Bool) (nativeNow : S → Bool)
    (lookup : MemberAction S E) (belongs : Bool) : MemberAction S E :=
  fun state => if eligible origin (nativeNow state) then lookup state
    else (.ok belongs, state)

theorem guarded_member_exact (origin : Bool) (nativeNow : S → Bool)
    (lookup : MemberAction S E) (belongs : Bool)
    (native_frame : ∀ state, eligible origin (nativeNow state) = true →
      lookup state = (.ok belongs, state)) :
    guardedMember origin nativeNow lookup belongs = (fun state => (.ok belongs, state)) := by
  funext state
  cases h : eligible origin (nativeNow state) with
  | false => simp [guardedMember, h]
  | true => simpa [guardedMember, h] using native_frame state h

-- Retiring the shortcut does NOT suppress the original effectful focus/write
-- operation. Its exact result, error and external state are preserved.
def trackedOperation (origin : Bool) (nativeNow : S → Bool)
    (operation : S → Except E V × S) (state : S) : (Except E V × Bool) × S :=
  let retained := eligible origin (nativeNow state)
  let result := operation state
  ((result.1, retained), result.2)

theorem tracked_operation_exact (origin : Bool) (nativeNow : S → Bool)
    (operation : S → Except E V × S) (state : S) :
    ((trackedOperation origin nativeNow operation state).1.1,
      (trackedOperation origin nativeNow operation state).2) = operation state := by
  cases h : operation state <;> simp [trackedOperation, h]

-- Reusing a pre-callback true verdict would execute this effect. A fresh
-- metadata check after the callback's state change keeps membership pure.
example : guardedMember true (fun state : Nat => decide (state = 0))
    (fun state => ((Except.ok true : Except Nat Bool), state + 1)) true 1 =
      (.ok true, 1) := rfl

-- Refine successful capture to the actual private index construction. Author
-- callbacks can change the method route; they do not own this private table.
-- A certified write follows the native insertion law. An unknown write may
-- leave ANY table contents, including dropping a declared key or adding one.
abbrev Membership (K : Type) := K → Bool
structure FamilyIndex (K : Type) where
  trusted : Bool
  members : Membership K

def insertMember (members : Membership K) (key : K) : Membership K :=
  fun query => if query = key then true else members query
def writeIndex (prior : FamilyIndex K) (current : Bool) (key : K)
    (unknownResult : Membership K) : FamilyIndex K :=
  let next := eligible prior.trusted current
  ⟨next, if next then insertMember prior.members key else unknownResult⟩
def indexAgrees (keys : List K) (index : FamilyIndex K) : Prop :=
  index.trusted = true → ∀ query, index.members query = decide (query ∈ keys)

theorem write_preserves_domain (keys : List K) (prior : FamilyIndex K)
    (agrees : indexAgrees keys prior) (current : Bool) (key : K)
    (unknownResult : Membership K) :
    indexAgrees (key :: keys) (writeIndex prior current key unknownResult) := by
  intro accepted query
  have both : prior.trusted = true ∧ current = true := by
    simpa [writeIndex, eligible] using accepted
  have previous := agrees both.1 query
  by_cases same : query = key
  · subst query
    simp [writeIndex, eligible, both, insertMember]
  · simp [writeIndex, eligible, both, insertMember, same, previous]

theorem unknown_write_retires (prior : FamilyIndex K) (key : K)
    (unknownResult : Membership K) :
    (writeIndex prior false key unknownResult).trusted = false := by
  simp [writeIndex, eligible]

-- Each triple is one completed focus followed by its fresh route verdict and
-- actual unknown-write result. Failed callbacks/writes return no index here;
-- they cannot manufacture a successfully prepared builder.
abbrev IndexWrite (K : Type) := K × Bool × Membership K
def writeAll : FamilyIndex K → List (IndexWrite K) → FamilyIndex K
  | prior, [] => prior
  | prior, (key, current, unknownResult) :: rest =>
      writeAll (writeIndex prior current key unknownResult) rest
def writtenKeys : List (IndexWrite K) → List K → List K
  | [], keys => keys
  | (key, _, _) :: rest, keys => writtenKeys rest (key :: keys)

theorem construction_domain (writes : List (IndexWrite K))
    (keys : List K) (prior : FamilyIndex K) (agrees : indexAgrees keys prior) :
    indexAgrees (writtenKeys writes keys) (writeAll prior writes) := by
  induction writes generalizing keys prior with
  | nil => exact agrees
  | cons entry rest ih =>
    rcases entry with ⟨key, current, unknownResult⟩
    exact ih (key :: keys) (writeIndex prior current key unknownResult)
      (write_preserves_domain keys prior agrees current key unknownResult)

theorem retired_construction_stays_retired (writes : List (IndexWrite K))
    (prior : FamilyIndex K) (retired : prior.trusted = false) :
    (writeAll prior writes).trusted = false := by
  induction writes generalizing prior with
  | nil => exact retired
  | cons entry rest ih =>
    rcases entry with ⟨key, current, unknownResult⟩
    apply ih
    simp [writeIndex, eligible, retired]

omit [DecidableEq K] in
theorem written_keys (writes : List (IndexWrite K)) (keys : List K) :
    writtenKeys writes keys = (writes.map Prod.fst).reverse ++ keys := by
  induction writes generalizing keys with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨key, current, unknownResult⟩
    simp [writtenKeys, ih, List.reverse_cons, List.append_assoc]

theorem completed_index_domain (writes : List (IndexWrite K))
    (accepted : (writeAll ⟨true, fun _ => false⟩ writes).trusted = true)
    (query : K) :
    (writeAll ⟨true, fun _ => false⟩ writes).members query =
      decide (query ∈ writes.map Prod.fst) := by
  have initial : indexAgrees ([] : List K) ⟨true, fun _ => false⟩ := by
    simp [indexAgrees]
  have complete := construction_domain writes [] ⟨true, fun _ => false⟩ initial
  have result := complete accepted query
  rw [written_keys writes []] at result
  simpa only [List.append_nil, List.mem_reverse] using result

-- Dropping a declared write while keeping the certificate is unsound even
-- if all later metadata and queries look ordinary. This is the native setter
-- control's mathematical counterexample, not an assumption of successful IO.
example : ¬ indexAgrees [1] ⟨true, fun _ : Nat => false⟩ := by
  intro accepted
  have impossible := accepted rfl 1
  simp at impossible

#print axioms capture_keys
#print axioms captured_domain
#print axioms same_first_refusal
#print axioms same_entry
#print axioms triangular_work
#print axioms retired_stays_retired
#print axioms guarded_member_exact
#print axioms tracked_operation_exact
#print axioms write_preserves_domain
#print axioms unknown_write_retires
#print axioms construction_domain
#print axioms retired_construction_stays_retired
#print axioms written_keys
#print axioms completed_index_domain
end ComponentFamily
