import LeanPoo.Functional.PropertyTesting
import LeanPoo.Functional.TableIndex

/-! Finite collection-trace controls reuse the existing carrier, delta and index
semantics. They do not prove that a Gerbil adapter implements those operations;
that remains the explicit step-simulation premise and runtime differential test.
The two-key carrier is complete, not an incomplete enumeration of Nat keys. -/
namespace Examples.CollectionTesting
open LeanPoo.Functional.PropertyTesting LeanPoo.Functional.OrderedDictionary

/-- Two service identifiers keep enumeration complete and mechanically decidable. -/
abbrev Key := Fin 2
/-- Persistent primary bindings retain stored false separately from missing. -/
abbrev Primary := Key → Option Bool
/-- One named unique index has Boolean buckets and exact original row payloads. -/
abbrev Cache := Unit → Bool → Key → Option Bool
/-- Current metadata and correlated primary/index state belong to one fixture. -/
structure Ledger where
  epoch : Nat
  primary : Primary
  cache : Cache

/-- Captured deltas may be retained across revision; inverseChanges restores them. -/
inductive Command where
  | install (captured : Nat) (changes : List (Change Key Bool))
  | revise
/-- Expected refusals remain data rather than exceptions or passing trials. -/
inductive Reply where
  | installed | conflict | indexConflict | stale | revised
  deriving DecidableEq

/-- The ordinary functional carrier supplies the established delta equations. -/
def carrier : TableCarrier Key Bool Primary :=
  { read := id, write := replace, read_write := fun _ _ _ => rfl }
/-- Existing uniqueness and cache updates observe the value of each service row. -/
def projection (_ : Unit) (_ : Key) (value : Bool) : Bool := value
/-- Both keys are enumerated once; no live binding is omitted by the oracle. -/
def rows (primary : Primary) : List (Key × Bool) :=
  ([0, 1] : List Key).filterMap fun key => (primary key).map (key, ·)
/-- The uniqueness oracle's complete-enumeration premise is discharged for this
finite carrier, rather than assumed for a truncated set of arbitrary keys. -/
theorem rows_complete (primary : Primary) (key : Key) (value : Bool)
    (present : primary key = some value) : (key, value) ∈ rows primary := by
  apply List.mem_filterMap.mpr
  refine ⟨key, ?_, by simp [present]⟩
  obtain ⟨n, bound⟩ := key
  have choices : n = 0 ∨ n = 1 := by omega
  rcases choices with h | h <;> subst n <;> simp

/-- Construct the same atomic indexed operation used by the collection proofs. -/
def install (state : Ledger) (changes : List (Change Key Bool)) : Ledger × Reply :=
  match applyIndexed carrier [()] (fun _ => true) projection rows changes (state.primary, state.cache) with
  | .ok (primary, cache) => (⟨state.epoch, primary, cache⟩, .installed)
  | .error (.inl _) => (state, .conflict)
  | .error (.inr _) => (state, .indexConflict)

/-- This model treats source revision plus explicit refresh as one command; the
Scheme fixture separately tests expire/read-old/refresh and snapshot rejection. -/
def model : TraceModel Ledger Command Reply :=
  { initial := ⟨0, fun _ => none, fun _ _ _ => none⟩
    enabled := fun _ _ => true
    advance := fun state command => match command with
      | .revise => ({ state with epoch := state.epoch + 1 }, .revised)
      | .install captured changes =>
          if captured = state.epoch then install state changes else (state, .stale) }

/-- Independent finite observations compare every primary and every index cell. -/
def observe (state : Ledger) : Nat × List (Option Bool) × List (Option Bool) :=
  (state.epoch, [state.primary 0, state.primary 1],
    [state.cache () false 0, state.cache () false 1, state.cache () true 0, state.cache () true 1])
/-- The second receipt conflicts only with the unique value owner, not old data. -/
def firstDelta : List (Change Key Bool) := [⟨0, none, some true⟩]
/-- This receipt remains unchanged while its first installation fails and retries. -/
def secondDelta : List (Change Key Bool) := [⟨1, none, some true⟩]
/-- Conflicting installation, delete/retry, inversion, old-value conflict and
cross-round stale refusal all feed the same existing trace observation fold. -/
def lifecycle : List Command :=
  [.install 0 firstDelta, .install 0 secondDelta,
   .install 0 (inverseChanges firstDelta), .install 0 secondDelta,
   .install 0 (inverseChanges secondDelta), .install 0 [⟨0, none, some false⟩],
   .install 0 firstDelta, .revise,
   .install 0 [⟨0, some false, none⟩], .install 1 [⟨0, some false, none⟩]]

/-- Expected failures are valid operations and cannot be silently discarded. -/
example : traceValid model model.initial lifecycle = true := by decide
/-- The retained receipt retries after removing its competing unique owner. -/
example : (traceObservations model.advance observe model.initial lifecycle).map Prod.fst =
    [.installed, .indexConflict, .installed, .installed, .installed, .installed,
     .conflict, .revised, .stale, .installed] := rfl
/-- Inversion and the final current-round deletion restore the complete empty view. -/
example : (traceObservations model.advance observe model.initial lifecycle).getLast? =
    some (.installed, (1, [none, none], [none, none, none, none])) := rfl

/-- A deliberately broken adapter publishes primary data after a late index
refusal, while preserving the expected reply and the old cache. -/
def publishBeforeApproval (state : Ledger) (command : Command) : Ledger × Reply :=
  let next := model.advance state command
  if next.2 = .indexConflict then
    ({ next.1 with primary := replace next.1.primary 1 (some true) }, next.2)
  else next
/-- Comparing replies alone misses the bug; the complete observation detects its
first divergence at command 1, before any later recovery could conceal it. -/
example : firstDifference
    (traceObservations model.advance observe model.initial lifecycle)
    (traceObservations publishBeforeApproval observe model.initial lifecycle) = some 1 := rfl
/-- A receipt expects false and replaces it with true, independently of history. -/
def promote : List (Change Key Bool) := [⟨0, some false, some true⟩]
/-- An intervening false/true/false sequence restores the expected old value.
The same receipt remains admissible within an epoch; revision still invalidates it. -/
def aba : List Command :=
  [.install 0 [⟨0, none, some false⟩], .install 0 promote,
   .install 0 (inverseChanges promote), .install 0 promote, .revise,
   .install 0 (inverseChanges promote), .install 1 (inverseChanges promote)]
example : (traceObservations model.advance observe model.initial aba).map Prod.fst =
    [.installed, .installed, .installed, .installed, .revised, .stale, .installed] := rfl
/-- A high-ID prefix cannot collide with step-derived producer selection anymore. -/
example : freshHandle 1 [2] = 3 := rfl
example : freshHandle 2 [3, 2] = 4 := rfl
example : freshHandle 1 [1000, 2] ∉ [1000, 2] := freshHandle_not_mem _ _
#print axioms freshHandle_not_mem
/-- A zero-budget lazy consumer does not inspect the (possibly failing) tail. -/
example (next : Nat → Option Nat) : (forceChildren next 0 0).pulls = 0 := rfl
/-- Exact-budget completion without observed EOF cannot certify minimality. -/
example : (forceChildren (fun n => some n) 2 0).exhausted = false := rfl
/-- Dependent packet payloads preserve their selected parent's count. -/
example : ∀ entry ∈ dependentCandidates [6, 3, 2]
    (fun count seed => [List.replicate count seed]) 41, entry.2.length = entry.1 := by
  intro entry member
  apply dependentCandidates_relation _ _ _ (fun count payload => payload.length = count) _ entry member
  intro count _ payload selected
  simp only [List.mem_singleton] at selected
  subst payload
  simp
/-- An earlier successful trial remains protected after observing a later branch. -/
example : ([true] ++ [false]).all id = false := rfl
#print axioms forceChildren_bounded
#print axioms forceChildren_accounting
#print axioms dependentCandidates_relation
#print axioms stale_observation_retained
end Examples.CollectionTesting
