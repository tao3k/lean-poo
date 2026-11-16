import Std

namespace ShapeAdmission

-- Nat models symbol identity, not its printed spelling. None is a bad key.
def admitNames : List (Option Nat) → Nat → Except Nat (List Nat)
  | [], _ => .ok []
  | none :: _, position => .error position
  | some key :: rest, position => do
      let suffix ← admitNames rest (position + 1)
      pure (key :: suffix)

-- Gerbil delete-duplicates/hash defaults to reverse traversal. Its first bad
-- key is therefore the RIGHTMOST invalid original position; last copies win.
def normalize (names : List (Option Nat)) : Except Nat (List Nat) :=
  match admitNames names.reverse 0 with
  | .error reversedPosition => .error (names.length - 1 - reversedPosition)
  | .ok keys => .ok keys.eraseDups.reverse

-- Larger requests must use the existing path, even if a prefix is cached.
def selectScalar : List (Option Nat) → Option (Except Nat (List Nat))
  | [] => some (.ok [])
  | [none] => some (.error 0)
  | [some key] => some (.ok [key])
  | _ => none

theorem scalar_selection_exact (names : List (Option Nat)) (result)
    (selected : selectScalar names = some result) : normalize names = result := by
  cases names with
  | nil =>
    rw [← Option.some.inj selected]
    rfl
  | cons key rest =>
    cases rest with
    | nil =>
      cases key <;> (rw [← Option.some.inj selected]; rfl)
    | cons next tail => simp [selectScalar] at selected

example : selectScalar [some 0] = some (.ok [0]) := rfl
example : selectScalar [some 7, some 7] = none := rfl
example : selectScalar [some 7, some 23] = none := rfl
example : normalize [some 7, none, some 23] = .error 1 := rfl
example : normalize [none, some 7, none] = .error 2 := rfl
example : normalize [some 7, some 23, some 7] = .ok [23, 7] := rfl

-- State includes semantic effects/trace; physical allocation is measured apart.
abbrev Action (State Error Value : Type) := State → Except Error Value × State

def bind (first : Action S E A) (next : A → Action S E B) : Action S E B :=
  fun state => match first state with
    | (.error error, state') => (.error error, state')
    | (.ok value, state') => next value state'

def original (scratch : Action S E Unit) (admit : Action S E Keys)
    (publish : Keys → Action S E Layout) : Action S E Layout :=
  bind scratch (fun _ => bind admit publish)

def scalar (admit : Action S E Keys) (publish : Keys → Action S E Layout) :=
  bind admit publish

def guarded (closed : Bool) (scratch : Action S E Unit) (admit : Action S E Keys)
    (publish : Keys → Action S E Layout) : Action S E Layout :=
  if closed then scalar admit publish else original scratch admit publish

-- This is a REQUIRED premise, not a claim about arbitrary Gerbil adapters.
theorem closed_scratch_exact (scratch : Action S E Unit) (admit : Action S E Keys)
    (publish : Keys → Action S E Layout)
    (pure : ∀ state, scratch state = (.ok (), state)) :
    original scratch admit publish = scalar admit publish := by
  funext state
  simp [original, scalar, bind, pure]

theorem guarded_exact (closed : Bool) (scratch : Action S E Unit)
    (admit : Action S E Keys) (publish : Keys → Action S E Layout)
    (admitted : closed = true → ∀ state, scratch state = (.ok (), state)) :
    guarded closed scratch admit publish = original scratch admit publish := by
  cases closed with
  | false => rfl
  | true =>
    simp only [guarded, ↓reduceIte]
    exact (closed_scratch_exact scratch admit publish (admitted rfl)).symm

theorem unsupported_fallback (scratch : Action S E Unit) (admit : Action S E Keys)
    (publish : Keys → Action S E Layout) :
    guarded false scratch admit publish = original scratch admit publish := rfl

-- Native table construction also draws a random seed. Keep that effect once,
-- before admission, and carry the seed to publication rather than drawing twice.
def originalWithSeed (seed : Action S E Seed) (allocate : Seed → Action S E Unit)
    (admit : Action S E Keys) (publish : Seed → Keys → Action S E Layout) :=
  bind seed (fun token => original (allocate token) admit (publish token))

def splitWithSeed (seed : Action S E Seed) (admit : Action S E Keys)
    (publish : Seed → Keys → Action S E Layout) :=
  bind seed (fun token => scalar admit (publish token))

theorem seed_effect_preserved (seed : Action S E Seed) (allocate : Seed → Action S E Unit)
    (admit : Action S E Keys) (publish : Seed → Keys → Action S E Layout)
    (pure : ∀ token state, allocate token state = (.ok (), state)) :
    originalWithSeed seed allocate admit publish = splitWithSeed seed admit publish := by
  have same : (fun token => original (allocate token) admit (publish token)) =
      (fun token => scalar admit (publish token)) := by
    funext token
    exact closed_scratch_exact (allocate token) admit (publish token) (pure token)
  simp only [originalWithSeed, splitWithSeed, same]

-- Admission of a runtime route is pointwise, not a verdict carried over an effect.
def guardedAt (route : S → Bool) (scratch : Action S E Unit)
    (admit : Action S E Keys) (publish : Keys → Action S E Layout) : Action S E Layout :=
  fun state => if route state then scalar admit publish state
    else original scratch admit publish state

theorem guardedAt_exact (route : S → Bool) (scratch : Action S E Unit)
    (admit : Action S E Keys) (publish : Keys → Action S E Layout)
    (admitted : ∀ state, route state = true → scratch state = (.ok (), state)) :
    guardedAt route scratch admit publish = original scratch admit publish := by
  funext state
  cases selected : route state with
  | false => simp [guardedAt, selected]
  | true => simp [guardedAt, selected, original, scalar, bind, admitted state selected]

def seededGuarded (seed : Action S E Seed) (route : Seed → S → Bool)
    (allocate : Seed → Action S E Unit) (admit : Action S E Keys)
    (publish : Seed → Keys → Action S E Layout) :=
  bind seed (fun token => guardedAt (route token) (allocate token) admit (publish token))

theorem seededGuarded_exact (seed : Action S E Seed) (route : Seed → S → Bool)
    (allocate : Seed → Action S E Unit) (admit : Action S E Keys)
    (publish : Seed → Keys → Action S E Layout)
    (admitted : ∀ token state, route token state = true →
      allocate token state = (.ok (), state)) :
    seededGuarded seed route allocate admit publish =
      originalWithSeed seed allocate admit publish := by
  have same : (fun token => guardedAt (route token) (allocate token) admit (publish token)) =
      (fun token => original (allocate token) admit (publish token)) := by
    funext token
    exact guardedAt_exact (route token) (allocate token) admit (publish token) (admitted token)
  simp only [seededGuarded, originalWithSeed, same]

-- An effect can change routes: reusing the old true guard would lose the callback.
abbrev RouteState := Bool × Nat
def changeRoute : Action RouteState Unit Unit := fun state => (.ok (), (false, state.2 + 1))
def quiet : Action RouteState Unit Unit := fun state => (.ok (), state)
def routedAllocation (_ : Unit) : Action RouteState Unit Unit := fun state =>
  (.ok (), (state.1, state.2 + if state.1 then 0 else 10))
def keepRoute (_ : Unit) (_ : Unit) : Action RouteState Unit Unit := quiet
example : originalWithSeed changeRoute routedAllocation quiet keepRoute (true, 0) =
    (.ok (), (false, 11)) := rfl
example : bind changeRoute (fun _ => guarded true (routedAllocation ()) quiet (keepRoute ()))
    (true, 0) = (.ok (), (false, 1)) := rfl
example : seededGuarded changeRoute (fun _ state => state.1) routedAllocation quiet keepRoute
    (true, 0) = (.ok (), (false, 11)) := rfl

-- Concrete scalar index: the old membership mark is overwritten by offset 0.
-- Only lookup meaning is shared; no physical HashMap-layout equality is claimed.
abbrev Entry := Sum Unit Nat
def eagerIndex (key : Nat) : Std.HashMap Nat Entry :=
  (({} : Std.HashMap Nat Entry).insert key (.inl ())).insert key (.inr 0)
def delayedIndex (key : Nat) : Std.HashMap Nat Entry :=
  ({} : Std.HashMap Nat Entry).insert key (.inr 0)
theorem scalar_index_exact (key query : Nat) :
    (eagerIndex key)[query]? = (delayedIndex key)[query]? := by
  by_cases same : key = query <;>
    simp [eagerIndex, delayedIndex, same]

-- Caller spines and published key values have different ownership. A native
-- refinement must copy the scalar pair; retaining a caller address is NOT this model.
def callerWrite (caller : Nat → List Nat) (address : Nat) (names : List Nat) :=
  fun query => if query = address then names else caller query
def publishKey (caller : Nat → List Nat) (address : Nat) := caller address
theorem captured_key_survives_caller_write (caller : Nat → List Nat) (address : Nat)
    (replacement : List Nat) :
    let published := publishKey caller address
    let _caller := callerWrite caller address replacement
    published = caller address := rfl

def writeCells (heap : Nat → List (Option Nat)) (owner : Nat) (cells : List (Option Nat)) :=
  fun query => if query = owner then cells else heap query
theorem other_receiver_cells_unchanged (heap : Nat → List (Option Nat))
    (owner other : Nat) (cells : List (Option Nat)) (different : other ≠ owner) :
    writeCells heap owner cells other = heap other := by
  simp [writeCells, different]
theorem fresh_receiver_identity (next : Nat) : next ≠ next + 1 := by omega

-- Native RNG changes its own state, not constructor routes or caller spines.
-- This frame is NOT granted to arbitrary author callbacks or expansion.
def framedSeed (step : Action Random E Seed) : Action (Metadata × Random) E Seed :=
  fun state => let observed := step state.2
    (observed.1, (state.1, observed.2))
theorem framed_seed_preserves_metadata (step : Action Random E Seed)
    (state : Metadata × Random) : (framedSeed step state).2.1 = state.1 := rfl

def checkBeforeSeed (step : Action Random E Seed) (route : Metadata → Bool)
    (allocate : Seed → Action (Metadata × Random) E Unit)
    (admit : Action (Metadata × Random) E Keys)
    (publish : Seed → Keys → Action (Metadata × Random) E Layout) :=
  fun state => bind (framedSeed step)
    (fun token => guarded (route state.1) (allocate token) admit (publish token)) state

theorem framed_seed_guard_shared (step : Action Random E Seed) (route : Metadata → Bool)
    (allocate : Seed → Action (Metadata × Random) E Unit)
    (admit : Action (Metadata × Random) E Keys)
    (publish : Seed → Keys → Action (Metadata × Random) E Layout) :
    checkBeforeSeed step route allocate admit publish =
      seededGuarded (framedSeed step) (fun _ state => route state.1) allocate admit publish := by
  funext state
  cases observed : step state.2 with
  | mk result next =>
    cases result <;> cases selected : route state.1 <;>
      simp [checkBeforeSeed, seededGuarded, framedSeed, guardedAt, guarded, bind, observed, selected]

-- Native routing abstraction: inspect Gerbil's CURRENT cached prototype rather
-- than creating a substitute adapter or retaining a previous admission verdict.
inductive Method where
  | symbolicRead | symbolicWrite | weakRead | weakWrite | author (identity : Nat)
  deriving DecidableEq, BEq
structure Prototype where
  wrapper : Nat
  refMethod : Method
  setMethod : Method
structure Routing where
  descriptorWrapper : Nat
  slotOffsets : List Nat
  cachedCastPath : Bool
  index : Nat
  prototypes : Nat → Option Prototype
  cacheBackendMatches : Bool
  cacheRef : Method
  cacheSet : Method

def closedRoutes (wrapper : Nat) (offsets : List Nat) (routing : Routing) : Bool :=
  decide (routing.descriptorWrapper = wrapper) && decide (routing.slotOffsets = offsets) &&
    routing.cachedCastPath && routing.cacheBackendMatches &&
    decide (routing.cacheRef = .weakRead) && decide (routing.cacheSet = .weakWrite) &&
    match routing.prototypes routing.index with
    | none => false
    | some prototype => decide (prototype.wrapper = wrapper) &&
        decide (prototype.refMethod = .symbolicRead) && decide (prototype.setMethod = .symbolicWrite)

theorem closed_selects_current_methods (wrapper : Nat) (offsets : List Nat) (routing : Routing)
    (closed : closedRoutes wrapper offsets routing = true) :
    ∃ prototype, routing.prototypes routing.index = some prototype ∧
      prototype.wrapper = wrapper ∧ prototype.refMethod = .symbolicRead ∧
      prototype.setMethod = .symbolicWrite ∧ routing.cacheRef = .weakRead ∧
      routing.cacheSet = .weakWrite := by
  cases selected : routing.prototypes routing.index with
  | none => simp [closedRoutes, selected] at closed
  | some prototype =>
    simp only [closedRoutes, selected, Bool.and_eq_true, decide_eq_true_eq] at closed
    exact ⟨prototype, rfl, closed.2.1.1, closed.2.1.2, closed.2.2,
      closed.1.1.2, closed.1.2⟩

def methodEffects : Method → List Nat
  | .author identity => [identity]
  | _ => []
theorem closed_method_effects_empty (wrapper : Nat) (offsets : List Nat) (routing : Routing)
    (closed : closedRoutes wrapper offsets routing = true) :
    ∃ prototype, routing.prototypes routing.index = some prototype ∧
      methodEffects prototype.refMethod ++ methodEffects prototype.setMethod ++
        methodEffects routing.cacheRef ++ methodEffects routing.cacheSet = [] := by
  obtain ⟨prototype, selected, _, read, write, cacheRead, cacheWrite⟩ :=
    closed_selects_current_methods wrapper offsets routing closed
  exact ⟨prototype, selected, by simp [read, write, cacheRead, cacheWrite, methodEffects]⟩

-- A shape hit alone cannot authorize skipping an effectful scratch adapter.
def effectful : Action Nat Unit Unit := fun state => (.ok (), state + 1)
def accept : Action Nat Unit Unit := fun state => (.ok (), state)
def publish : Unit → Action Nat Unit Unit := fun _ state => (.ok (), state)
example : original effectful accept publish 0 = (.ok (), 1) := rfl
example : scalar accept publish 0 = (.ok (), 0) := rfl

#print axioms scalar_selection_exact
#print axioms guarded_exact
#print axioms unsupported_fallback
#print axioms seed_effect_preserved
#print axioms seededGuarded_exact
#print axioms scalar_index_exact
#print axioms other_receiver_cells_unchanged
#print axioms framed_seed_guard_shared
#print axioms closed_selects_current_methods
#print axioms closed_method_effects_empty

namespace BoundedNames

structure Acc where
  members : Nat → Bool
  values : List Nat

def Related (acc : Acc) : Prop := ∀ key, acc.members key = acc.values.contains key

def hashInsert (key : Nat) (acc : Acc) : Acc :=
  if acc.members key then acc
  else ⟨fun query => (query == key) || acc.members query, key :: acc.values⟩

def listInsert (key : Nat) (values : List Nat) : List Nat :=
  if values.contains key then values else key :: values

theorem insert_values (key : Nat) (acc : Acc) (related : Related acc) :
    (hashInsert key acc).values = listInsert key acc.values := by
  simp only [hashInsert, listInsert, ← related key]
  split <;> rfl

theorem insert_related (key : Nat) (acc : Acc) (related : Related acc) :
    Related (hashInsert key acc) := by
  cases found : acc.members key with
  | true => simpa [hashInsert, found] using related
  | false =>
      intro query
      simp only [hashInsert, found, Bool.false_eq_true, ↓reduceIte]
      change (query == key || acc.members query) = (key :: acc.values).contains query
      rw [List.contains_cons, related query]

abbrev Owned := { acc : Acc // Related acc }

def empty : Owned := ⟨⟨fun _ => false, []⟩, by intro key; rfl⟩
def insert (key : Nat) (acc : Owned) : Owned :=
  ⟨hashInsert key acc.val, insert_related key acc.val acc.property⟩

def returned (value : A) : Action S E A := fun state => (.ok value, state)
def project (action : Action S E Owned) : Action S E (List Nat) :=
  fun state => let observed := action state
    (observed.1.map (fun acc => acc.val.values), observed.2)

def hashStep (admit : Key → Action S E Nat)
    (action : Action S E Owned) (key : Key) : Action S E Owned :=
  bind action (fun acc => bind (admit key) (fun symbol => returned (insert symbol acc)))

def listStep (admit : Key → Action S E Nat)
    (action : Action S E (List Nat)) (key : Key) : Action S E (List Nat) :=
  bind action (fun values => bind (admit key) (fun symbol =>
    returned (listInsert symbol values)))

/-- Native hash membership and memq see the same identity set. Admission,
including its state/error, runs before either membership implementation. -/
theorem project_step (admit : Key → Action S E Nat)
    (action : Action S E Owned) (key : Key) :
    project (hashStep admit action key) = listStep admit (project action) key := by
  funext state
  cases ran : action state with
  | mk outcome after =>
      cases outcome with
      | error cause =>
          simp [project, hashStep, listStep, bind, ran, Except.map]
      | ok acc =>
          cases checked : admit key after with
          | mk result finalState =>
              cases result with
              | error cause =>
                  simp [project, hashStep, listStep, bind, ran, checked, Except.map]
              | ok symbol =>
                  simp [project, hashStep, listStep, bind, returned, ran, checked,
                    Except.map, insert, insert_values symbol acc.val acc.property]

theorem project_fold (admit : Key → Action S E Nat)
    (keys : List Key) (action : Action S E Owned) :
    project (keys.foldl (hashStep admit) action) =
      keys.foldl (listStep admit) (project action) := by
  induction keys generalizing action with
  | nil => rfl
  | cons key rest ih =>
      simp only [List.foldl_cons]
      rw [ih, project_step]

def reference (admit : Key → Action S E Nat) (keys : List Key) :=
  project (keys.reverse.foldl (hashStep admit) (returned empty))

def direct (admit : Key → Action S E Nat) (keys : List Key) :=
  keys.foldr (fun key action => listStep admit action key) (returned [])

/-- This is a state-and-first-error equality for arbitrary admitted keys,
including duplicates. Std foldr preserves the original right-to-left order. -/
theorem exact (admit : Key → Action S E Nat) (keys : List Key) :
    reference admit keys = direct admit keys := by
  rw [reference, project_fold]
  have initial : project (returned empty : Action S E Owned) = returned [] := rfl
  rw [initial]
  exact List.foldl_reverse

def adaptive (limit : Nat) (admit : Key → Action S E Nat) (keys : List Key) :=
  if keys.length ≤ limit then direct admit keys else reference admit keys

theorem adaptive_exact (limit : Nat) (admit : Key → Action S E Nat) (keys : List Key) :
    adaptive limit admit keys = reference admit keys := by
  unfold adaptive
  split
  · exact (BoundedNames.exact admit keys).symm
  · rfl

/-- Sorting, publication, fresh receiver cells and their exceptions are the
same arbitrary continuation after equal normalization. -/
theorem continuation_exact (admit : Key → Action S E Nat) (keys : List Key)
    (finish : List Nat → Action S E Result) :
    bind (reference admit keys) finish = bind (direct admit keys) finish := by
  rw [BoundedNames.exact]

theorem seed_prefix_exact (seed : Action S E Seed)
    (admit : Seed → Key → Action S E Nat) (keys : List Key) :
    bind seed (fun token => reference (admit token) keys) =
      bind seed (fun token => direct (admit token) keys) := by
  apply congrArg (bind seed)
  funext token
  exact BoundedNames.exact (admit token) keys

private def accept (key : Nat) : Action Unit Nat Nat := returned key
private def reject (key : Except Nat Nat) : Action Unit Nat Nat := fun state => (key, state)

example : direct accept [1, 2, 1] () = (.ok [2, 1], ()) := rfl
example : direct reject [.error 17, .ok 1, .error 23] () = (.error 23, ()) := rfl

#print axioms exact
#print axioms seed_prefix_exact
end BoundedNames

end ShapeAdmission
