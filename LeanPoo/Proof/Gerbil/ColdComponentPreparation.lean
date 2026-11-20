import Std

namespace ColdComponentPreparation

-- A refusal retains the state reached before it. State may record observations,
-- including source checks, callback order, and external effects.
inductive Run (S E A : Type) where
  | ok (value : A) (state : S)
  | refused (error : E) (state : S)

def Run.bind (x : Run S E A) (f : A → S → Run S E B) : Run S E B :=
  match x with
  | .ok a s => f a s
  | .refused e s => .refused e s

def traverse (f : A → S → Run S E B) : List A → S → Run S E (List B)
  | [], s => .ok [] s
  | a :: as, s => (f a s).bind fun b s' =>
      (traverse f as s').bind fun bs s'' => .ok (b :: bs) s''

abbrev Entry (K D : Type) := K × D

-- Only the canonical fragment branch: no inherited dispatcher or finalizer.
-- Admission still runs in the actual order and can fail with any error.
def admit (validate : D → S → Run S E D) (row : Entry K D) (s : S) :
    Run S E (Entry K D) :=
  (validate row.2 s).bind fun d s' => .ok (row.1, d) s'

def singletonChunks (f : A → S → Run S E B) (a : A) (s : S) :
    Run S E (List B) :=
  (f a s).bind fun b s' => .ok [b] s'

theorem flatten_singleton_traversal (f : A → S → Run S E B)
    (xs : List A) (s : S) :
    (traverse (singletonChunks f) xs s).bind (fun chunks s' =>
      .ok chunks.flatten s') = traverse f xs s := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
      simp only [traverse, singletonChunks]
      cases h : f x s with
      | refused => rfl
      | ok b s' =>
          have ht := ih s'
          cases hr : traverse (singletonChunks f) xs s' with
          | refused e st =>
              rw [hr] at ht
              simp only [Run.bind, hr, ← ht]
          | ok chunks st =>
              rw [hr] at ht
              simp only [Run.bind, hr, ← ht, List.flatten_cons, List.singleton_append]

-- The outer source admission/recheck is explicit, including any independent
-- check needed after effectful work. Finish is still the original whole-stream
-- validator, capture/assembler, closure, residual, registration and approval.
theorem canonical_pipeline (before : S → Run S E Unit)
    (validate : D → S → Run S E D) (rows : List (Entry K D))
    (finish : List (Entry K D) → S → Run S E P)
    (after : P → S → Run S E V) (s : S) :
    (before s).bind (fun _ s' =>
      ((traverse (singletonChunks (admit validate)) rows s').bind
        (fun chunks s'' => .ok chunks.flatten s'')).bind
        (fun entries s'' => (finish entries s'').bind after)) =
    (before s).bind (fun _ s' =>
      (traverse (admit validate) rows s').bind
        (fun entries s'' => (finish entries s'').bind after)) := by
  simp only [flatten_singleton_traversal]

-- The runtime compares the actual method values it captured. Only the
-- certified route may be replaced, even if another route usually returns
-- the same entries. This theorem does not certify a Gerbil method read.
theorem route_specialization (authenticated : Bool) (ordinary fast : S → Run S E A)
    (same : authenticated = true → ∀ s, ordinary s = fast s) (s : S) :
    (if authenticated then fast s else ordinary s) = ordinary s := by
  cases authenticated with
  | false => rfl
  | true => exact (same rfl s).symm

-- gp.prepare resolves a compiler on a local protocol, compiles the ordered
-- descriptors, composes the delayed program, then resolves the cook action.
-- The successful public observations use the program and cook; the enclosing
-- generalized receipt must not expose the protocol carrier itself.
def prepareViaProtocol
    (compilerRead : S → Run S E (D → S → Run S E C))
    (cookRead : S → Run S E Cook) (composeDelayed : List C → Program)
    (rows : List D) (s : S) : Run S E (Program × Cook) :=
  (compilerRead s).bind fun compile s' =>
    (traverse compile rows s').bind fun compiled s'' =>
      (cookRead s'').bind fun cook s''' => .ok (composeDelayed compiled, cook) s'''

def prepareViaOperations (compile : D → S → Run S E C) (cook : Cook)
    (composeDelayed : List C → Program) (rows : List D) (s : S) :
    Run S E (Program × Cook) :=
  (traverse compile rows s).bind fun compiled s' => .ok (composeDelayed compiled, cook) s'

-- The cook authority must still hold at the state reached AFTER compiling.
-- The unchanged outer admission/registration/return checks can observe any
-- failure or state changes from the ordered descriptor compilers.
theorem internal_assembly (compilerRead : S → Run S E (D → S → Run S E C))
    (cookRead : S → Run S E Cook) (compile : D → S → Run S E C)
    (cook : Cook) (composeDelayed : List C → Program) (rows : List D) (s : S)
    (compilerCurrent : compilerRead s = .ok compile s)
    (cookCurrent : ∀ compiled s', traverse compile rows s = .ok compiled s' →
      cookRead s' = .ok cook s') :
    prepareViaProtocol compilerRead cookRead composeDelayed rows s =
      prepareViaOperations compile cook composeDelayed rows s := by
  unfold prepareViaProtocol prepareViaOperations
  rw [compilerCurrent]
  simp only [Run.bind]
  cases h : traverse compile rows s with
  | refused => rfl
  | ok compiled s' => simp only [cookCurrent compiled s' h]

-- Select the operations independently. A stale post-compilation route
-- executes the original cook read from that state, never compiles again.
def conditionalAssembly
    (compilerCurrent cookCurrent : S → Bool)
    (compilerRead : S → Run S E (D → S → Run S E C))
    (cookRead : S → Run S E Cook) (compile : D → S → Run S E C)
    (cook : Cook) (composeDelayed : List C → Program) (rows : List D) :
    S → Run S E (Program × Cook) :=
  prepareViaProtocol
    (fun s => if compilerCurrent s then .ok compile s else compilerRead s)
    (fun s => if cookCurrent s then .ok cook s else cookRead s)
    composeDelayed rows

theorem conditional_assembly_exact
    (compilerCurrent cookCurrent : S → Bool)
    (compilerRead : S → Run S E (D → S → Run S E C))
    (cookRead : S → Run S E Cook) (compile : D → S → Run S E C)
    (cook : Cook) (composeDelayed : List C → Program) (rows : List D)
    (compilerSound : ∀ s, compilerCurrent s = true → compilerRead s = .ok compile s)
    (cookSound : ∀ s, cookCurrent s = true → cookRead s = .ok cook s) :
    conditionalAssembly compilerCurrent cookCurrent compilerRead cookRead
      compile cook composeDelayed rows =
      prepareViaProtocol compilerRead cookRead composeDelayed rows := by
  have first : (fun s => if compilerCurrent s then .ok compile s else compilerRead s) =
      compilerRead := by
    funext s
    cases h : compilerCurrent s with
    | false => simp
    | true => simp [compilerSound s h]
  have last : (fun s => if cookCurrent s then .ok cook s else cookRead s) =
      cookRead := by
    funext s
    cases h : cookCurrent s with
    | false => simp
    | true => simp [cookSound s h]
  unfold conditionalAssembly
  rw [first, last]

-- A live observer on the protocol cook read falsifies transparency even if
-- the result value is unchanged. A changed cook route can also refuse.
example :
    prepareViaProtocol
      (fun s => (.ok (fun (_ : Unit) t => .ok () t) s : Run Nat Unit _))
      (fun s => .ok () (s + 1)) (fun _ => ()) [()] 0 =
        .ok ((), ()) 1 := rfl

example :
    prepareViaProtocol
      (fun s => (.ok (fun (_ : Unit) _ => .ok () false) s : Run Bool Nat _))
      (fun current => if current then .ok () current else .refused 9 current)
      (fun _ => ()) [()] true = .refused 9 false := rfl

example :
    conditionalAssembly (fun _ => true) id
      (fun s => (.ok (fun (_ : Unit) _ => .ok () false) s : Run Bool Nat _))
      (fun current => if current then .ok () current else .refused 9 current)
      (fun (_ : Unit) _ => .ok () false) () (fun _ => ()) [()] true =
      .refused 9 false := rfl

-- Count only the canonical singleton chunks and their outer list cells,
-- excluding the result stream (both paths must produce it).
def chunkCells (n : Nat) : Nat := n + n
theorem removed_chunk_cells (sizes : List Nat) :
    (sizes.map chunkCells).sum = 2 * sizes.sum := by
  induction sizes with
  | nil => simp
  | cons n sizes ih => simp only [List.map_cons, List.sum_cons, ih, chunkCells]; omega

-- All-accepting cold executions cannot omit an arbitrary opaque group:
-- a provider refusing only at an unqueried group is indistinguishable.
def allows (provider : K → Bool) (keys : List K) := keys.all provider

theorem unqueried_group_can_refuse [DecidableEq K]
    (requested queried : List K) (k : K) (required : k ∈ requested)
    (unseen : k ∉ queried) :
    ∃ p q : K → Bool, (∀ j ∈ queried, p j = q j) ∧
      allows p requested = true ∧ allows q requested = false := by
  refine ⟨fun _ => true, fun j => decide (j ≠ k), ?_, ?_, ?_⟩
  · intro j hj
    have ne : j ≠ k := fun eq => unseen (eq ▸ hj)
    simp [ne]
  · simp [allows]
  · cases h : allows (fun j => decide (j ≠ k)) requested with
    | false => rfl
    | true =>
        have impossible := (List.all_eq_true.mp h) k required
        simp at impossible

-- A separate algorithmic opportunity: a certified no-self transition with
-- frozen external inputs has a constant *raw* transition. This only derives
-- the adjacent-equality step count and budget outcome; it cannot erase any
-- callback, guard, residual, or cooking observation.
def stabilize [DecidableEq R] (step : R → R) : Nat → R → Option (R × Nat)
  | 0, _ => none
  | fuel + 1, seed =>
      let next := step seed
      if next = seed then some (seed, 1)
      else (stabilize step fuel next).map (fun (raw, steps) => (raw, steps + 1))

theorem constant_raw_stabilization [DecidableEq R] (v seed : R) (fuel : Nat) :
    stabilize (fun _ => v) fuel seed =
      if fuel = 0 then none
      else if v = seed then some (seed, 1)
      else if fuel = 1 then none
      else some (v, 2) := by
  cases fuel with
  | zero => simp [stabilize]
  | succ n =>
      by_cases same : v = seed
      · simp [stabilize, same]
      · cases n with
        | zero => simp [stabilize, same]
        | succ n => simp [stabilize, same]

-- Matched negative examples: moving the whole-stream check earlier would
-- replace the second row's failure; skipping the independent return check
-- would publish work whose source was changed by the finishing callback.
private def rejectTwo (n : Nat) (seen : List Nat) : Run (List Nat) Nat Nat :=
  if n = 2 then .refused n (seen ++ [n]) else .ok n (seen ++ [n])

example : (traverse (admit rejectTwo) [(10, 1), (20, 2), (30, 3)] []).bind
    (fun _ s => (.refused 99 s : Run (List Nat) Nat Unit)) =
      .refused 2 [1, 2] := rfl

private def changedOnReturn (_ : Unit) (current : Bool) : Run Bool Nat Unit :=
  if current then .ok () current else .refused 1 current

example : (Run.ok () false).bind changedOnReturn = .refused 1 false := rfl
example : (Run.ok () false : Run Bool Nat Unit) ≠ .refused 1 false := by
  intro h
  cases h

#print axioms canonical_pipeline
#print axioms route_specialization
#print axioms internal_assembly
#print axioms conditional_assembly_exact
#print axioms removed_chunk_cells
#print axioms unqueried_group_can_refuse
#print axioms constant_raw_stabilization

end ColdComponentPreparation
