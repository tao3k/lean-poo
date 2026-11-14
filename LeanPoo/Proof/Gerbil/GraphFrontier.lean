import Std

namespace GraphFrontier

-- Observable predicate state includes counters/trace and the first refusal.
abbrev Predicate (A S E : Type) := A → S → Except (E × S) (Bool × S)

def select (pred : Predicate A S E) : List A → S → Except (E × S) (List A × S)
  | [], state => .ok ([], state)
  | key :: rest, state => match pred key state with
      | .error error => .error error
      | .ok (keep, next) => match select pred rest next with
          | .error error => .error error
          | .ok (selected, final) => .ok (if keep then key :: selected else selected, final)

def accumulate (pred : Predicate A S E) : List A → List A → S → Except (E × S) (List A × S)
  | [], reversed, state => .ok (reversed, state)
  | key :: rest, reversed, state => match pred key state with
      | .error error => .error error
      | .ok (keep, next) => accumulate pred rest (if keep then key :: reversed else reversed) next

def finish (tail : List A) (result : Except (E × S) (List A × S)) :=
  Except.map (fun (reversed, state) => (reversed.reverse ++ tail, state)) result

theorem accumulator_exact (pred : Predicate A S E) (row reversed : List A) (state : S) :
    accumulate pred row reversed state =
      Except.map (fun (selected, final) => (selected.reverse ++ reversed, final))
        (select pred row state) := by
  induction row generalizing reversed state with
  | nil => rfl
  | cons key rest ih =>
    simp only [accumulate, select]
    cases hp : pred key state with
    | error error => rfl
    | ok pair =>
      rcases pair with ⟨keep, next⟩
      dsimp only
      rw [ih]
      cases hs : select pred rest next with
      | error error => rfl
      | ok pair =>
        rcases pair with ⟨selected, final⟩
        cases keep <;> simp [Except.map, List.reverse_cons, List.append_assoc]

theorem frontier_exact (pred : Predicate A S E) (row tail : List A) (state : S) :
    finish tail (accumulate pred row [] state) =
      Except.map (fun (selected, final) => (selected ++ tail, final))
        (select pred row state) := by
  rw [accumulator_exact]
  cases h : select pred row state with
  | error error => rfl
  | ok pair =>
    rcases pair with ⟨selected, final⟩
    dsimp [finish, Except.map]
    simp

#print axioms accumulator_exact
#print axioms frontier_exact

-- A complete search can borrow the row as a frame. Popping it before
-- the older frames is equivalent to prepending its live readers.
def flattenFrames (frames : List (List A)) : List A := frames.flatten

theorem open_frame_exact (row : List A) (older : List (List A)) :
    flattenFrames (row :: older) = row ++ flattenFrames older := rfl

theorem pop_frame_exact (head : A) (row : List A) (older : List (List A)) :
    flattenFrames ((head :: row) :: older) =
      head :: flattenFrames (row :: older) := rfl

theorem skip_mask_exact (live : A → Bool) (masked : A) (row : List A)
    (older : List (List A)) (hidden : live masked = false) :
    flattenFrames (((masked :: row).filter live) :: older) =
      flattenFrames ((row.filter live) :: older) := by
  simp [hidden]


-- A mark at an admitted rank identifies only that owner. Rank gaps do
-- not contribute marks and do not need to be enumerated.
theorem rank_marks_exact [DecidableEq A] (rank : A → Nat)
    (injective : ∀ a b, rank a = rank b → a = b) (seen : List A) (key : A) :
    rank key ∈ seen.map rank ↔ key ∈ seen := by
  constructor
  · intro marked
    obtain ⟨owner, member, equal⟩ := List.mem_map.mp marked
    exact (injective owner key equal) ▸ member
  · intro member
    exact List.mem_map.mpr ⟨key, member, rfl⟩


-- The former search conses each newly entered owner onto its result.
-- Testing that reversed list returns the last intersection in visit order.
def lastIntersection (common : A → Bool) (order : List A) : Option A :=
    order.foldl (fun last owner => if common owner then some owner else last) none

theorem last_intersection_exact (common : A → Bool) (order : List A) :
    lastIntersection common order = order.reverse.find? common := by
  have loop (items : List A) (initial : Option A) :
      items.foldl (fun last owner => if common owner then some owner else last) initial =
        (items.reverse.find? common).orElse (fun _ => initial) := by
    induction items generalizing initial with
    | nil => rfl
    | cons head rest ih =>
      simp only [List.foldl_cons, List.reverse_cons, List.find?_append]
      rw [ih]
      cases found : rest.reverse.find? common <;> cases hit : common head <;>
        simp [hit, Option.orElse]
  simpa [lastIntersection] using loop order none

end GraphFrontier

namespace GraphSourceAdmission

-- Once fresh rows are captured, only changed rows need to enter rank repair.
def replaceChanged (old fresh : K → List K) [DecidableEq K] (key : K) : List K :=
  if fresh key = old key then old key else fresh key

theorem captured_rows_exact [DecidableEq K] (old fresh : K → List K) :
    replaceChanged old fresh = fresh := by
  funext key
  unfold replaceChanged
  split <;> simp_all

-- The unchanged rows already passed admission on this same roster.
theorem changed_support_iff [DecidableEq K] (old fresh : K → List K) (supported : K → Prop)
    (prior : ∀ key dep, dep ∈ old key → supported dep) :
    (∀ key, fresh key ≠ old key → ∀ dep, dep ∈ fresh key → supported dep) ↔
      (∀ key dep, dep ∈ fresh key → supported dep) := by
  constructor
  · intro changed key dep member
    by_cases same : fresh key = old key
    · exact prior key dep (same ▸ member)
    · exact changed key same dep member
  · intro all key _ dep member
    exact all key dep member

-- Two live getters may return the same program after the old row was captured.
-- Equality at the effect boundary cannot authorize reusing that captured row.
theorem live_getter_not_a_certificate :
    ∃ (oldNow freshNow : Nat) (oldRow freshRow : List Nat),
      oldNow = freshNow ∧ oldRow ≠ freshRow :=
  ⟨0, 0, [], [1], rfl, by decide⟩

#print axioms captured_rows_exact
#print axioms changed_support_iff
#print axioms live_getter_not_a_certificate
end GraphSourceAdmission
