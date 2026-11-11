-- SPDX-License-Identifier:  Apache-2.0 AND LGPL-2.1-or-later
/- Sharing the existing observation table inside ONE effect-free reader check.
   Query includes procedure identity, arguments and collector identity.
   No approval, cache or world survives a callback or an independent check. -/
namespace LeanPoo.Functional.SourceReadWindow

variable {Query Value Error : Type} [DecidableEq Query]

structure CheckedCache (oracle : Query → Except Error Value) where
  lookup : Query → Option Value
  correct : ∀ key value, lookup key = some value → oracle key = .ok value

def empty (oracle : Query → Except Error Value) : CheckedCache oracle :=
  ⟨fun _ => none, by simp⟩

def insert (oracle : Query → Except Error Value) (cache : CheckedCache oracle)
    (key : Query) (value : Value) (observed : oracle key = .ok value) : CheckedCache oracle where
  lookup other := if other = key then some value else cache.lookup other
  correct := by
    intro other found hit
    by_cases same : other = key
    · subst other
      simp only [ite_true] at hit
      cases hit
      exact observed
    · simp only [ite_eq_right same] at hit
      exact cache.correct other found hit

def fetch (oracle : Query → Except Error Value) (cache : CheckedCache oracle)
    (key : Query) : Except Error (Value × CheckedCache oracle) :=
  match cache.lookup key with
  | some value => .ok (value, cache)
  | none =>
    match observed : oracle key with
    | .error cause => .error cause
    | .ok value => .ok (value, insert oracle cache key value observed)

theorem fetch_value_exact (oracle : Query → Except Error Value)
    (cache : CheckedCache oracle) (key : Query) :
    (fetch oracle cache key).map Prod.fst = oracle key := by
  cases found : cache.lookup key with
  | none =>
    unfold fetch
    rw [found]
    dsimp only
    split <;> rename_i value observed <;> simp [observed, Except.map]
  | some value => simp [fetch, found, Except.map, cache.correct key value found]

def run (oracle : Query → Except Error Value) (cache : CheckedCache oracle) :
    List Query → Except Error (List Value)
  | [] => .ok []
  | key :: rest => do
    let (value, next) ← fetch oracle cache key
    let tail ← run oracle next rest
    pure (value :: tail)

def direct (oracle : Query → Except Error Value) : List Query → Except Error (List Value)
  | [] => .ok []
  | key :: rest => do
    let value ← oracle key
    let tail ← direct oracle rest
    pure (value :: tail)

/-- The complete ordered value/error result is unchanged, including the first
    refusal. Reuse is justified by current-window observations, not a label. -/
theorem ordered_result_exact (oracle : Query → Except Error Value)
    (cache : CheckedCache oracle) (queries : List Query) :
    run oracle cache queries = direct oracle queries := by
  induction queries generalizing cache with
  | nil => rfl
  | cons key rest ih =>
    have head := fetch_value_exact oracle cache key
    cases step : fetch oracle cache key with
    | error cause =>
      simp [step, Except.map] at head
      simp [run, direct, step, ← head, Bind.bind, Except.bind]
    | ok pair =>
      rcases pair with ⟨value, next⟩
      simp [step, Except.map] at head
      simp [run, direct, step, ← head, ih next, Bind.bind, Except.bind]

/-- Metadata and byte queries can share the same admitted window. -/
theorem joined_interval_exact (oracle : Query → Except Error Value)
    (earlier later : List Query) :
    run oracle (empty oracle) (earlier ++ later) = direct oracle (earlier ++ later) :=
  ordered_result_exact oracle (empty oracle) _

-- Changed worlds get EMPTY windows on BOTH callback sides.
def around {World : Type} (oracle : World → Query → Except Error Value)
    (effect : World → Except Error World) (world : World) (queries : List Query) :
    Except Error (List Value) := do
  let _ ← run (oracle world) (empty (oracle world)) queries
  let next ← effect world
  run (oracle next) (empty (oracle next)) queries

example : around (fun world _ : Nat => (.ok world : Except Bool Nat))
    (fun _ => .ok 1) 0 [0, 0] = .ok [1, 1] := rfl

example : run (fun _ : Nat => (.error false : Except Bool Nat))
    (empty _) [0, 0] = .error false := rfl

/- Count actual oracle invocations, not requests, slots or Graph nodes. This
   instruments the existing checked window; it proposes no runtime cache. A
   failed miss counts once and prevents all later queries from executing. -/
def counted (oracle : Query → Except Error Value) (cache : CheckedCache oracle) :
    List Query → Except Error (List Value) × Nat
  | [] => (.ok [], 0)
  | key :: rest =>
    let calls := if (cache.lookup key).isNone then 1 else 0
    match fetch oracle cache key with
    | .error cause => (.error cause, calls)
    | .ok (value, next) =>
      let (result, tailCalls) := counted oracle next rest
      (result.map (value :: ·), calls + tailCalls)

theorem counted_result_exact (oracle : Query → Except Error Value)
    (cache : CheckedCache oracle) (queries : List Query) :
    (counted oracle cache queries).1 = direct oracle queries := by
  have same : (counted oracle cache queries).1 = run oracle cache queries := by
    induction queries generalizing cache with
    | nil => rfl
    | cons key rest ih =>
      cases step : fetch oracle cache key with
      | error cause => simp [counted, run, step, Bind.bind, Except.bind]
      | ok pair =>
        rcases pair with ⟨value, next⟩
        simp [counted, run, step, ← ih next, Except.map, Bind.bind, Except.bind,
          Pure.pure, Except.pure]
  exact same.trans (ordered_result_exact oracle cache queries)

theorem hits_issue_no_queries (oracle : Query → Except Error Value)
    (cache : CheckedCache oracle) (queries : List Query)
    (hits : ∀ key ∈ queries, ∃ value, cache.lookup key = some value) :
    (counted oracle cache queries).2 = 0 := by
  induction queries with
  | nil => rfl
  | cons key rest ih =>
    obtain ⟨value, hit⟩ := hits key (by simp)
    have tailHits : ∀ key ∈ rest, ∃ value, cache.lookup key = some value :=
      fun key member => hits key (by simp [member])
    simpa [counted, fetch, hit] using ih tailHits

theorem repeated_success_issues_once (oracle : Query → Except Error Value)
    (key : Query) (value : Value) (success : oracle key = .ok value) (repeats : Nat) :
    (counted oracle (empty oracle) (key :: List.replicate repeats key)).2 = 1 := by
  have hits : ∀ other ∈ List.replicate repeats key,
      ∃ found, (insert oracle (empty oracle) key value success).lookup other = some found := by
    intro other member
    have same : other = key := (List.mem_replicate.mp member).2
    subst other
    exact ⟨value, by simp [insert]⟩
  have tail := hits_issue_no_queries oracle _ _ hits
  have step : fetch oracle (empty oracle) key =
      .ok (value, insert oracle (empty oracle) key value success) := by
    unfold fetch
    dsimp [empty]
    split
    next cause observed => simp_all
    next found observed =>
      have same : found = value := by simpa using observed.symm.trans success
      subst found
      rfl
  simp only [counted, step]
  change 1 + (counted oracle (insert oracle (empty oracle) key value success)
    (List.replicate repeats key)).2 = 1
  rw [tail]

theorem failed_first_query_stops (oracle : Query → Except Error Value)
    (key : Query) (cause : Error) (failure : oracle key = .error cause)
    (remaining : List Query) :
    counted oracle (empty oracle) (key :: remaining) = (.error cause, 1) := by
  have step : fetch oracle (empty oracle) key = .error cause := by
    unfold fetch
    dsimp [empty]
    split <;> simp_all
  simp only [counted, step]
  simp [empty]

-- Equal query names across an unknown effect are not an admitted shared
-- window. The two empty windows must each issue their own successful read.
theorem independent_windows_issue_twice
    (before after : Query → Except Error Value) (key : Query)
    (old new : Value) (oldRead : before key = .ok old) (newRead : after key = .ok new)
    (repeats : Nat) :
    (counted before (empty before) (key :: List.replicate repeats key)).2 +
      (counted after (empty after) (key :: List.replicate repeats key)).2 = 2 := by
  rw [repeated_success_issues_once before key old oldRead repeats,
      repeated_success_issues_once after key new newRead repeats]

end LeanPoo.Functional.SourceReadWindow
