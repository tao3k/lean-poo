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

end LeanPoo.Functional.SourceReadWindow
