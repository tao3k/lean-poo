import Std

namespace ComponentRouting
variable {K : Type} [DecidableEq K]

abbrev Membership (K : Type) := K → Bool
def empty : Membership K := fun _ => false
def insert (seen : Membership K) (key : K) : Membership K :=
  fun query => if query = key then true else seen query
def build : List K → Membership K → Membership K
  | [], seen => seen
  | key :: rest, seen => build rest (insert seen key)

theorem build_lookup (keys : List K) (seen : Membership K) (query : K) :
    build keys seen query = (seen query || decide (query ∈ keys)) := by
  induction keys generalizing seen with
  | nil => simp [build]
  | cons key rest ih =>
    by_cases eq : query = key
    · subst query
      simp [build, ih, insert]
    · cases h : seen query <;> simp [build, ih, insert, eq, h]

theorem frozen_index_exact (keys : List K) (query : K) :
    build keys empty query = decide (query ∈ keys) := by
  simp [build_lookup, empty]

-- The threshold chooses representation, not the logical component domain.
def selected (threshold : Nat) (keys : List K) (query : K) : Bool :=
  if keys.length ≤ threshold then decide (query ∈ keys) else build keys empty query

theorem selection_exact (threshold : Nat) (keys : List K) (query : K) :
    selected threshold keys query = decide (query ∈ keys) := by
  simp [selected, frozen_index_exact]

-- Semantic state includes source/callback effects. Private allocation/GC are
-- separate work evidence, not axioms about native execution speed.
abbrev Action (S E V : Type) := S → Except E V × S
def bind (first : Action S E A) (next : A → Action S E B) : Action S E B :=
  fun state => match first state with
    | (.error reason, after) => (.error reason, after)
    | (.ok value, after) => next value after

def listed (declared : Action S E Unit) (inside outside : Action S E V)
    (belongs : Bool) : Action S E V :=
  bind declared (fun _ => if belongs then inside else outside)

def indexed (declared : Action S E Unit) (lookup : Action S E Bool)
    (inside outside : Action S E V) : Action S E V :=
  bind declared (fun _ => bind lookup (fun belongs => if belongs then inside else outside))

-- Lazy forcing is AFTER the independent declaration/reads callback. Its
-- native promise/table interval must preserve semantic state and membership.
-- This frame is not granted to arbitrary interface constructors or callbacks.
theorem after_declared_exact (declared : Action S E Unit) (lookup : Action S E Bool)
    (inside outside : Action S E V) (belongs : Bool)
    (pure_lookup : ∀ state, lookup state = (.ok belongs, state)) :
    indexed declared lookup inside outside = listed declared inside outside belongs := by
  funext state
  cases h : declared state with
  | mk result after =>
    cases result <;> simp [indexed, listed, bind, h, pure_lookup]

theorem owned_route_exact (threshold : Nat) (keys : List K) (query : K)
    (declared : Action S E Unit) (lookup : Action S E Bool)
    (inside outside : Action S E V)
    (pure_lookup : ∀ state, lookup state = (.ok (selected threshold keys query), state)) :
    indexed declared lookup inside outside =
      listed declared inside outside (decide (query ∈ keys)) := by
  rw [← selection_exact threshold keys query]
  exact after_declared_exact declared lookup inside outside _ pure_lookup

-- First refusal belongs to the ORIGINAL declared-read check. An eagerly
-- forced failing lookup must not replace that earlier refusal.
example : indexed (fun state : Nat => (Except.error 1, state))
    (fun state => (Except.error 2, state))
    (fun state => (Except.ok 7, state)) (fun state => (Except.ok 8, state)) 0 =
      (Except.error 1, 0) := rfl

-- Declaration/finalizer labels are not automatically component identities.
example : build [1, 2] empty 3 ≠ build [1, 3] empty 3 := by decide

-- Owning the original domain differs intentionally from rereading a caller
-- list after a callback removes one of its members.
example : build [1, 2] empty 2 ≠ decide (2 ∈ ([] : List Nat)) := by decide

#print axioms build_lookup
#print axioms frozen_index_exact
#print axioms selection_exact
#print axioms after_declared_exact
#print axioms owned_route_exact
end ComponentRouting
