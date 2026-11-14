import Std

namespace SccEditRegion
variable {V : Type}

inductive Path (edge : V → V → Prop) : V → V → Prop where
  | nil (a : V) : Path edge a a
  | step : edge a b → Path edge b c → Path edge a c

theorem Path.append {edge : V → V → Prop} {a b c : V}
    (p : Path edge a b) (q : Path edge b c) : Path edge a c := by
  induction p with
  | nil => exact q
  | step e _ ih => exact .step e (ih q)

theorem Path.lift {edge next : V → V → Prop} {a b : V}
    (p : Path edge a b) (includeEdge : ∀ x y, edge x y → next x y) : Path next a b := by
  induction p with
  | nil => exact .nil _
  | step e _ ih => exact .step (includeEdge _ _ e) ih

def Union (old next : V → V → Prop) (a b : V) : Prop := old a b ∨ next a b
def Added (old next : V → V → Prop) (a b : V) : Prop := next a b ∧ ¬ old a b

-- Scheme borrows the old index and layers only additions during each walk.
theorem old_with_additions_exact {old next : V → V → Prop} {a b : V} :
    Union old (Added old next) a b ↔ Union old next a b := by
  classical
  unfold Union Added
  constructor
  · rintro (h | ⟨h, _⟩)
    · exact Or.inl h
    · exact Or.inr h
  · by_cases h : old a b <;> simp [h]
def Mutual (edge : V → V → Prop) (a b : V) : Prop := Path edge a b ∧ Path edge b a

/-- A roster edit can keep retired ordinals as isolated vertices while the
local SCC repair runs. The public graph contains only active vertices. -/
def ActiveEdges (active : V → Prop) (edge : V → V → Prop) (a b : V) : Prop :=
  active a ∧ active b ∧ edge a b

inductive ActivePath (active : V → Prop) (edge : V → V → Prop) : V → V → Prop where
  | nil : active a → ActivePath active edge a a
  | step : active a → edge a b → ActivePath active edge b c → ActivePath active edge a c

theorem ActivePath.source {active : V → Prop} {edge : V → V → Prop} {a b : V}
    (path : ActivePath active edge a b) : active a := by
  cases path with
  | nil present => exact present
  | step present _ _ => exact present

theorem ActivePath.padded {active : V → Prop} {edge : V → V → Prop} {a b : V}
    (path : ActivePath active edge a b) : Path (ActiveEdges active edge) a b := by
  induction path with
  | nil _ => exact .nil _
  | step here e rest ih => exact .step ⟨here, rest.source, e⟩ ih

theorem Path.restrictActive {active : V → Prop} {edge : V → V → Prop} {a b : V}
    (path : Path (ActiveEdges active edge) a b) (present : active a) : ActivePath active edge a b := by
  induction path with
  | nil => exact .nil present
  | step e _ ih => exact .step e.1 e.2.2 (ih e.2.1)

theorem padded_scc_exact {active : V → Prop} {edge : V → V → Prop} {a b : V}
    (keepA : active a) (keepB : active b) :
    Mutual (ActiveEdges active edge) a b ↔
      ActivePath active edge a b ∧ ActivePath active edge b a := by
  exact ⟨fun p => ⟨p.1.restrictActive keepA, p.2.restrictActive keepB⟩,
    fun p => ⟨p.1.padded, p.2.padded⟩⟩

theorem retired_ordinal_is_isolated {active : V → Prop} {edge : V → V → Prop} {a b : V}
    (retired : ¬ active a) (path : Path (ActiveEdges active edge) a b) : a = b := by
  cases path with
  | nil => rfl
  | step e _ => exact False.elim (retired e.1)

/-- Before applying edited rows, reserve each new key as an isolated
vertex. Old routes can then be borrowed in the enlarged repair domain. -/
theorem appended_ordinal_has_no_incoming_path {active : V → Prop}
    {edge : V → V → Prop} {a b : V}
    (fresh : ¬ active b) (path : Path (ActiveEdges active edge) a b) : a = b := by
  induction path with
  | nil => rfl
  | @step a middle b e _ ih =>
    have same := ih fresh
    exact False.elim (fresh (same ▸ e.2.1))

theorem appended_ordinal_starts_as_singleton {active : V → Prop}
    {edge : V → V → Prop} {a b : V} (fresh : ¬ active a) :
    Mutual (ActiveEdges active edge) a b ↔ a = b := by
  constructor
  · intro related
    exact retired_ordinal_is_isolated fresh related.1
  · rintro rfl
    exact ⟨.nil _, .nil _⟩

theorem append_preserves_old_representative {active : V → Prop}
    {edge : V → V → Prop} {old fresh : List V} {a : V}
    (present : active a)
    (newKeys : ∀ key ∈ fresh, ¬ active key)
    [DecidableRel (Mutual (ActiveEdges active edge))] :
    (old ++ fresh).filter (fun key => decide (Mutual (ActiveEdges active edge) a key)) =
      old.filter (fun key => decide (Mutual (ActiveEdges active edge) a key)) := by
  have empty : fresh.filter (fun key => decide (Mutual (ActiveEdges active edge) a key)) = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro key member
    have included := List.mem_filter.mp member
    have related := of_decide_eq_true included.2
    have same := appended_ordinal_has_no_incoming_path (newKeys key included.1) related.1
    exact newKeys key included.1 (same ▸ present)
  simp [List.filter_append, empty]

#print axioms appended_ordinal_starts_as_singleton
#print axioms append_preserves_old_representative

-- The sparse position index overrides the immutable cold table. Removing
-- an override for an appended name is safe exactly when the base lacks it.
def retiredPosition (cold : Option Nat) : Option (Option Nat) :=
  if cold.isSome then some none else none

theorem retired_position_absent (cold : Option Nat) :
    (retiredPosition cold).getD cold = none := by
  cases cold <;> rfl

theorem fresh_retirement_needs_no_override : retiredPosition none = none := rfl

-- When every successor program is supplied, the schedule owns a new
-- support table. Copying only surviving bases is equivalent to masking
-- every retirement, including across a later re-add of a removed owner.
def successorBase (live : V → Bool) (old : V → Option A) (key : V) : Option A :=
  if live key then old key else none

theorem successor_base_matches_retirement_mask
    (live : V → Bool) (old : V → Option A) (key : V) :
    successorBase live old key = (if !live key then none else old key) := by
  unfold successorBase
  cases live key <;> rfl

theorem successor_base_does_not_revive
    (live later : V → Bool) (old : V → Option A) (key : V)
    (retired : live key = false) :
    successorBase later (successorBase live old) key = none := by
  simp only [successorBase, retired, Bool.false_eq_true, if_false]
  split <;> rfl

theorem retired_index_uses_absence_value {A : Type} (cold : Option A) (absent : A) :
    ((if cold.isSome then some absent else none).or cold).getD absent = absent := by
  cases cold <;> rfl

#print axioms retired_index_uses_absence_value

theorem live_suffix_removal_preserves_order {V : Type} [DecidableEq V]
    (position : V → Option Nat) (entries : List (Nat × V)) (key : V)
    (retired : position key = none) :
    (entries.filter (fun row => !decide (row.2 = key))).filter
        (fun row => decide (position row.2 = some row.1)) =
      entries.filter (fun row => decide (position row.2 = some row.1)) := by
  induction entries with
  | nil => rfl
  | cons row rest ih =>
    by_cases same : row.2 = key
    · simpa [List.filter_cons, same, retired] using ih
    · simp only [List.filter_cons, decide_eq_false same, Bool.not_false, ite_true, ih]

#print axioms retired_position_absent
#print axioms live_suffix_removal_preserves_order

-- The native witness split is floor(width / 2). Doubling an arbitrary
-- old span therefore preserves its complete address map in the left child.
def growSpan (span : Nat) : Nat → Nat
  | 0 => span
  | n + 1 => 2 * growSpan span n

theorem grown_left_span (span : Nat) : (2 * span) / 2 = span := by omega

theorem append_ordinals_are_fresh (next first second old : Nat)
    (prior : old < next) :
    old ≠ next + first ∧ (next + first = next + second ↔ first = second) := by
  omega

def lookupGrownWitness (span : Nat) (old : Nat → Option W) (position : Nat) : Nat → Option W
  | 0 => if position < span then old position else none
  | n + 1 =>
    if position < growSpan span n then lookupGrownWitness span old position n else none

theorem witness_growth_preserves_address (old : Nat → Option W) (position : Nat)
    (within : position < span) (steps : Nat) :
    lookupGrownWitness span old position steps = old position := by
  have fits : ∀ n, span ≤ growSpan span n := by
    intro n
    induction n with
    | zero => exact Nat.le_refl _
    | succ n ih =>
      simp only [growSpan]
      omega
  induction steps with
  | zero => simp [lookupGrownWitness, within]
  | succ n ih => simp [lookupGrownWitness, Nat.lt_of_lt_of_le within (fits n), ih]

theorem witness_growth_leaves_new_address_empty (old : Nat → Option W) (position : Nat)
    (fresh : span ≤ position) (steps : Nat) :
    lookupGrownWitness span old position steps = none := by
  induction steps with
  | zero => simp [lookupGrownWitness, Nat.not_lt.mpr fresh]
  | succ n ih => simp [lookupGrownWitness, ih]

#print axioms witness_growth_preserves_address
#print axioms witness_growth_leaves_new_address_empty

/-- Once both incident indexes establish isolation, the repair graph is
already the exact padded graph. Retiring owner/member entries changes only
the public active projection. -/
theorem isolated_retirements_preserve_edges {active : V → Prop} {edge : V → V → Prop}
    (outgoing : ∀ a b, ¬ active a → ¬ edge a b)
    (incoming : ∀ a b, ¬ active b → ¬ edge a b) :
    ActiveEdges active edge = edge := by
  classical
  funext a b
  apply propext
  constructor
  · exact fun present => present.2.2
  · intro present
    by_cases source : active a
    · by_cases target : active b
      · exact ⟨source, target, present⟩
      · exact False.elim (incoming a b target present)
    · exact False.elim (outgoing a b source present)

theorem retirement_preflight_exact {V : Type} {active edited : V → Prop}
    {old next : V → V → Prop}
    (oldReader : ∀ a b, active a → ¬ active b → old a b → edited a)
    (unchanged : ∀ a b, active a → ¬ edited a → next a b → old a b)
    (checked : ∀ a b, active a → edited a → next a b → active b)
    (empty : ∀ a b, ¬ active a → ¬ next a b) :
    ActiveEdges active next = next := by
  classical
  apply isolated_retirements_preserve_edges empty
  intro a b removed edge
  by_cases present : active a
  · by_cases changed : edited a
    · exact removed (checked a b present changed edge)
    · exact changed (oldReader a b present removed (unchanged a b present changed edge))
  · exact empty a b present edge

#print axioms retirement_preflight_exact

-- Reuse a surviving group's old result only when its actual builder factors
-- through the retained inputs. A whole-roster callback need not do so.
theorem retired_member_can_change_opaque_builder :
    let build := fun (roster : List Nat) (_local : Unit) => roster.contains 1
    build [0, 1] () ≠ build [0] () := by decide

theorem local_builder_reuse {Context Inputs Outcome : Type}
    (run : Context → Outcome) (project : Context → Inputs) (build : Inputs → Outcome)
    (factors : ∀ context, run context = build (project context))
    (old next : Context) (same : project old = project next) : run old = run next := by
  rw [factors old, factors next, same]

/-- Even when the member computation is fixed, the construction policy can
refuse it. Native publication must account for both of these inputs. -/
theorem local_value_with_changed_policy_cannot_be_reused :
    let run := fun (allow : Bool) (value : Nat) => if allow then some value else none
    run true 7 ≠ run false 7 := by decide

/-- Even identical graph values cannot preserve every approval outcome when
the approval sees a different state at the existing effect boundary. -/
theorem approvals_agree_iff_same_effect_state {State : Type} [DecidableEq State]
    (full sparse : State) :
    (∀ approve : State → Bool, approve full = approve sparse) ↔ full = sparse := by
  constructor
  · intro agrees
    have probe := agrees (fun state => decide (state = full))
    simpa [eq_comm] using probe
  · intro same approve
    rw [same]

/-- A private seed transition can differ between full and sparse work. Both
paths still enter author approval with the same application state. -/
theorem private_seed_transitions_preserve_approval
    {Seed Application Decision : Type} (full sparse : Seed → Seed)
    (approve : Application → Decision) (seed : Seed) (application : Application) :
    (fun state : Seed × Application => approve state.2) (full seed, application) =
      (fun state : Seed × Application => approve state.2) (sparse seed, application) := by
  rfl

inductive PublicationEffect (Seed Application : Type) where
  | seed (step : Seed → Seed)
  | application (step : Application → Application)

def runPublicationEffects {Seed Application : Type}
    (effects : List (PublicationEffect Seed Application)) (state : Seed × Application) :
    Seed × Application :=
  match effects with
  | [] => state
  | .seed step :: rest => runPublicationEffects rest (step state.1, state.2)
  | .application step :: rest => runPublicationEffects rest (state.1, step state.2)

def applicationEffects {Seed Application : Type} :
    List (PublicationEffect Seed Application) → List (Application → Application)
  | [] => []
  | .seed _ :: rest => applicationEffects rest
  | .application step :: rest => step :: applicationEffects rest

/-- Isolating private seed use makes the application state depend only on its
ordered effects. This does not allow skipping or reordering author callbacks. -/
theorem run_publication_application_projection {Seed Application : Type}
    (effects : List (PublicationEffect Seed Application)) (state : Seed × Application) :
    (runPublicationEffects effects state).2 =
      (applicationEffects effects).foldl (fun app step => step app) state.2 := by
  induction effects generalizing state with
  | nil => rfl
  | cons effect rest ih =>
    cases effect <;> simp [runPublicationEffects, applicationEffects, ih]

/-- Dynamic restoration restores the seed policy, including on refusal. The
application's actual state transitions still take effect. -/
def withSeedMode {Mode State Failure Result : Type} (outer inner : Mode)
    (action : Mode → State → Except Failure Result × State) (state : State) :
    Except Failure Result × State × Mode :=
  let outcome := action inner state
  (outcome.1, outcome.2, outer)

theorem application_entry_uses_ordinary_seed_mode {Mode State Failure Result : Type}
    (native ordinary : Mode) (state : State)
    (action : Mode → State → Except Failure Result × State) :
    let observed := withSeedMode native ordinary action state
    (observed.1, observed.2.1) = action ordinary state ∧ observed.2.2 = native := by
  simp [withSeedMode]

/-- Scope selection changes only verified assembly. A successful receipt is
handed to the same ordinary closure, and assembly failure never runs it. -/
def prepareThenClose {Mode State Failure Prepared Result : Type}
    (preparation ordinary : Mode)
    (prepare : Mode → State → Except Failure Prepared × State)
    (close : Mode → Prepared → State → Except Failure Result × State)
    (state : State) : Except Failure Result × State :=
  match prepare preparation state with
  | (.error cause, after) => (.error cause, after)
  | (.ok receipt, after) => close ordinary receipt after

theorem private_fragment_assembly_preserves_ordinary_close
    {Mode State Failure Prepared Result : Type} (native ordinary : Mode)
    (prepare : Mode → State → Except Failure Prepared × State)
    (close : Mode → Prepared → State → Except Failure Result × State)
    (state : State) (same : prepare native state = prepare ordinary state) :
    prepareThenClose native ordinary prepare close state =
      prepareThenClose ordinary ordinary prepare close state := by
  simp only [prepareThenClose, same]

/-- Inspect the replacement rows and the old inverse buckets of retired
providers. The remaining old rows need no new endpoint check. -/
theorem membership_delta_support_exact {active edited : V → Prop}
    {old replacement next : V → V → Prop}
    (exactRows : ∀ a b, next a b ↔
      active a ∧ ((edited a ∧ replacement a b) ∨ (¬ edited a ∧ old a b))) :
    (∀ a b, next a b → active b) ↔
      ((∀ a b, active a → edited a → replacement a b → active b) ∧
       (∀ b, ¬ active b → ∀ a, old a b → active a → edited a)) := by
  classical
  constructor
  · intro closed
    refine ⟨?_, ?_⟩
    · intro a b source touched edge
      exact closed a b ((exactRows a b).mpr ⟨source, Or.inl ⟨touched, edge⟩⟩)
    · intro b removed a edge source
      by_cases touched : edited a
      · exact touched
      · exact False.elim (removed (closed a b
          ((exactRows a b).mpr ⟨source, Or.inr ⟨touched, edge⟩⟩)))
  · rintro ⟨rows, reverse⟩ a b edge
    rcases (exactRows a b).mp edge with ⟨source, ⟨touched, changed⟩ | ⟨untouched, retained⟩⟩
    · exact rows a b source touched changed
    · by_cases provider : active b
      · exact provider
      · exact False.elim (untouched (reverse b provider a retained source))

def Region (edge : V → V → Prop) (root : V → Prop) (a : V) : Prop :=
  (∃ r, root r ∧ Path edge r a) ∧ (∃ r, root r ∧ Path edge a r)

theorem one_root_region {edge : V → V → Prop} {root a : V} :
    Region edge (· = root) a ↔ Mutual edge root a := by
  simp [Region, Mutual]

-- The specialized cut needs one successor per old row, every owner reaching
-- cut, and an exact deletion of the cut row. No enumeration of new SCCs is
-- needed to establish the singleton owner/member projections.
inductive Steps (edge : V → V → Prop) : V → V → Nat → Prop where
  | nil (a : V) : Steps edge a a 0
  | step : edge a b → Steps edge b c n → Steps edge a c (n + 1)

def Cut (edge : V → V → Prop) (sink : V) (a b : V) := edge a b ∧ a ≠ sink

theorem cut_reaches_sink {edge : V → V → Prop} {a sink : V} (p : Path edge a sink) :
    ∃ n, Steps (Cut edge sink) a sink n := by
  classical
  induction p with
  | nil => exact ⟨0, .nil _⟩
  | @step x y z e _ ih =>
    by_cases atSink : x = z
    · subst x
      exact ⟨0, .nil _⟩
    · obtain ⟨n, tail⟩ := ih
      exact ⟨n + 1, .step ⟨e, atSink⟩ tail⟩

def Functional (edge : V → V → Prop) : Prop := ∀ a b c, edge a b → edge a c → b = c

theorem cut_distance_unique {edge : V → V → Prop} {a b sink : V} {n m : Nat}
    (one : Functional edge) (p : Steps (Cut edge sink) a b n)
    (q : Steps (Cut edge sink) a b m) (endpoint : b = sink) : n = m := by
  induction p generalizing m with
  | nil =>
    cases q with
    | nil => rfl
    | step e _ => exact False.elim (e.2 endpoint)
  | @step x y z k first _ ih =>
    cases q with
    | nil => exact False.elim (first.2 endpoint)
    | @step _ w _ l other tail =>
      have same := one x y w first.1 other.1
      subst w
      exact congrArg (· + 1) (ih tail endpoint)

theorem cut_path_descends {edge : V → V → Prop} {sink a b : V} {n : Nat}
    (one : Functional edge) (p : Path (Cut edge sink) a b)
    (dist : Steps (Cut edge sink) a sink n) :
    ∃ m, Steps (Cut edge sink) b sink m ∧ m ≤ n ∧ (a ≠ b → m < n) := by
  induction p generalizing n with
  | nil => exact ⟨n, dist, Nat.le_refl _, fun h => False.elim (h rfl)⟩
  | @step x y z first _ ih =>
    cases dist with
    | nil => exact False.elim (first.2 rfl)
    | @step _ w _ k other tail =>
      have same := one x y w first.1 other.1
      subst w
      obtain ⟨m, d, le, _⟩ := ih tail
      exact ⟨m, d, Nat.le_trans le (Nat.le_succ k), fun _ => Nat.lt_succ_of_le le⟩

theorem functional_cut_singletons {edge : V → V → Prop} {sink a b : V}
    (one : Functional edge) (reaches : ∀ v, Path edge v sink) :
    Mutual (Cut edge sink) a b ↔ a = b := by
  constructor
  · intro pair
    classical
    by_cases sameVertex : a = b
    · exact sameVertex
    · obtain ⟨n, atA⟩ := cut_reaches_sink (reaches a)
      obtain ⟨m, atB, _, down⟩ := cut_path_descends one pair.1 atA
      obtain ⟨k, back, le, _⟩ := cut_path_descends one pair.2 atB
      have same := cut_distance_unique one back atA rfl
      exact False.elim (Nat.not_lt_of_ge (same ▸ le) (down sameVertex))
  · rintro rfl
    exact ⟨.nil _, .nil _⟩

theorem functional_replacement_exact {old next : V → V → Prop} {cut : V}
    (one : Functional old) (removed : ∃ dep, old cut dep ∧ ¬ next cut dep)
    (deletesOnly : ∀ a b, next a b → old a b)
    (otherRows : ∀ a b, a ≠ cut → old a b → next a b) :
    next = Cut old cut := by
  funext a b
  apply propext
  constructor
  · intro e
    have prior := deletesOnly a b e
    refine ⟨prior, ?_⟩
    rintro rfl
    obtain ⟨dep, before, absent⟩ := removed
    have same := one a b dep prior before
    exact absent (same ▸ e)
  · rintro ⟨before, outside⟩
    exact otherRows a b outside before

theorem functional_repair_exact {old next : V → V → Prop} {cut a b : V}
    (one : Functional old) (reaches : ∀ v, Path old v cut)
    (removed : ∃ dep, old cut dep ∧ ¬ next cut dep)
    (deletesOnly : ∀ a b, next a b → old a b)
    (otherRows : ∀ a b, a ≠ cut → old a b → next a b) :
    Mutual next a b ↔ a = b := by
  rw [functional_replacement_exact one removed deletesOnly otherRows]
  exact functional_cut_singletons one reaches

-- Further deletions preserve the singleton result. The exact delta only
-- needs to witness one old edge missing from the successor.
theorem functional_deletion_batch_exact {old next : V → V → Prop} {cut a b : V}
    (one : Functional old) (reaches : ∀ v, Path old v cut)
    (removed : ∃ dep, old cut dep ∧ ¬ next cut dep)
    (deletesOnly : ∀ a b, next a b → old a b) :
    Mutual next a b ↔ a = b := by
  constructor
  · intro paths
    have sub : ∀ x y, next x y → Cut old cut x y := by
      intro x y e
      have prior := deletesOnly x y e
      refine ⟨prior, ?_⟩
      rintro rfl
      obtain ⟨dep, before, absent⟩ := removed
      have same := one x y dep prior before
      exact absent (same ▸ e)
    exact (functional_cut_singletons one reaches).mp
      ⟨paths.1.lift sub, paths.2.lift sub⟩
  · rintro rfl
    exact ⟨.nil _, .nil _⟩

-- Even the old representative's group changes. Every owner belongs to a
-- different group after a certified cut of a nontrivial whole component.
theorem every_group_changed {old next : V → V → Prop} (owner : V)
    (nontrivial : ∃ a b : V, a ≠ b) (whole : ∀ a b, Mutual old a b)
    (split : ∀ a b, Mutual next a b ↔ a = b) :
    ∃ other, Mutual old owner other ∧ ¬ Mutual next owner other := by
  classical
  obtain ⟨a, b, different⟩ := nontrivial
  by_cases same : owner = a
  · exact ⟨b, whole owner b, fun s => different (same.symm.trans ((split owner b).mp s))⟩
  · exact ⟨a, whole owner a, fun s => same ((split owner a).mp s)⟩

-- The old graph may still be one SCC after an internal chord. The chord
-- can preserve a nontrivial SCC when a different row is later removed.
private def chordedRing (a b : Fin 3) : Prop :=
  (a = 0 ∧ (b = 1 ∨ b = 2)) ∨ (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 0)

example : ¬ Functional chordedRing := by
  intro one
  have contradiction : (1 : Fin 3) = 2 := one 0 1 2
    (by unfold chordedRing; decide) (by unfold chordedRing; decide)
  exact (by decide : (1 : Fin 3) ≠ 2) contradiction

example : Mutual (Cut chordedRing 1) 0 2 := by
  have forward : Cut chordedRing 1 0 2 := by unfold Cut chordedRing; decide
  have backward : Cut chordedRing 1 2 0 := by unfold Cut chordedRing; decide
  exact ⟨.step forward (.nil _), .step backward (.nil _)⟩

#print axioms one_root_region
#print axioms functional_replacement_exact
#print axioms functional_repair_exact
#print axioms every_group_changed

-- Follow the first row in the path that is allowed to differ. If there is
-- no such row, the complete path survives with its exact orientation.
theorem path_or_root {edge next : V → V → Prop} {root : V → Prop} {a b : V}
    (unchanged : ∀ x y, ¬ root x → edge x y → next x y) (p : Path edge a b) :
    Path next a b ∨ ∃ r, root r ∧ Path edge a r ∧ Path edge r b := by
  classical
  induction p with
  | nil => exact Or.inl (.nil _)
  | @step x y z e tail ih =>
    by_cases atRoot : root x
    · exact Or.inr ⟨x, atRoot, .nil x, .step e tail⟩
    · rcases ih with found | ⟨r, edited, before, after⟩
      · exact Or.inl (.step (unchanged x y atRoot e) found)
      · exact Or.inr ⟨r, edited, .step e before, after⟩

theorem preserve_outside_one_way {edge next union : V → V → Prop}
    {root : V → Prop} {a b : V}
    (unchanged : ∀ x y, ¬ root x → edge x y → next x y)
    (includes : ∀ x y, edge x y → union x y)
    (outside : ¬ Region union root a) (scc : Mutual edge a b) : Mutual next a b := by
  have forward := scc.1.lift includes
  have backward := scc.2.lift includes
  constructor
  · rcases path_or_root unchanged scc.1 with p | ⟨r, edited, before, after⟩
    · exact p
    · exact False.elim (outside ⟨⟨r, edited, (after.lift includes).append backward⟩,
                                  ⟨r, edited, before.lift includes⟩⟩)
  · rcases path_or_root unchanged scc.2 with p | ⟨r, edited, before, after⟩
    · exact p
    · exact False.elim (outside ⟨⟨r, edited, after.lift includes⟩,
                                  ⟨r, edited, forward.append (before.lift includes)⟩⟩)

theorem outside_membership_exact {old next : V → V → Prop} {root : V → Prop} {a b : V}
    (unchanged : ∀ x y, ¬ root x → (old x y ↔ next x y))
    (outside : ¬ Region (Union old next) root a) : Mutual old a b ↔ Mutual next a b := by
  constructor
  · exact preserve_outside_one_way (fun x y h => (unchanged x y h).mp)
      (fun _ _ => Or.inl) outside
  · exact preserve_outside_one_way (fun x y h => (unchanged x y h).mpr)
      (fun _ _ => Or.inr) outside

def Induced (edge : V → V → Prop) (inside : V → Prop) (a b : V) : Prop :=
  edge a b ∧ inside a ∧ inside b

-- Region is path-convex in the union, hence also in the successor. This
-- needs no assumption that the two reaching roots are the same root.
theorem restrict_path {edge union : V → V → Prop} {root : V → Prop} {a b : V}
    (includes : ∀ x y, edge x y → union x y) (p : Path edge a b)
    (start : Region union root a) (finish : Region union root b) :
    Path (Induced edge (Region union root)) a b := by
  induction p with
  | nil => exact .nil _
  | @step x y z e tail ih =>
    obtain ⟨r, rootR, toX⟩ := start.1
    obtain ⟨s, rootS, fromZ⟩ := finish.2
    have insideY : Region union root y :=
      ⟨⟨r, rootR, toX.append (.step (includes x y e) (.nil y))⟩,
       ⟨s, rootS, (tail.lift includes).append fromZ⟩⟩
    exact .step ⟨e, start, insideY⟩ (ih insideY finish)

theorem induced_membership_exact {old next : V → V → Prop} {root : V → Prop} {a b : V}
    (ha : Region (Union old next) root a) (hb : Region (Union old next) root b) :
    Mutual (Induced next (Region (Union old next) root)) a b ↔ Mutual next a b := by
  constructor
  · intro p
    exact ⟨p.1.lift (fun _ _ e => e.1), p.2.lift (fun _ _ e => e.1)⟩
  · intro p
    exact ⟨restrict_path (fun _ _ => Or.inr) p.1 ha hb,
           restrict_path (fun _ _ => Or.inr) p.2 hb ha⟩

theorem no_crossing_component {edge union : V → V → Prop} {root : V → Prop} {a b : V}
    (includes : ∀ x y, edge x y → union x y) (ha : Region union root a)
    (p : Mutual edge a b) : Region union root b := by
  obtain ⟨⟨r, rootR, toA⟩, ⟨s, rootS, fromA⟩⟩ := ha
  exact ⟨⟨r, rootR, toA.append (p.1.lift includes)⟩,
         ⟨s, rootS, (p.2.lift includes).append fromA⟩⟩

-- Patch by replacing only whole old components in the region. The resulting
-- equivalence relation is the cold successor relation, including mixed pairs.
theorem patch_exact {old next : V → V → Prop} {root : V → Prop} {a b : V}
    (unchanged : ∀ x y, ¬ root x → (old x y ↔ next x y)) :
    let inside := Region (Union old next) root
    ((¬ inside a ∧ Mutual old a b) ∨
      (inside a ∧ inside b ∧ Mutual (Induced next inside) a b)) ↔ Mutual next a b := by
  dsimp only
  constructor
  · rintro (⟨outside, prior⟩ | ⟨ha, hb, localPair⟩)
    · exact (outside_membership_exact unchanged outside).mp prior
    · exact (induced_membership_exact ha hb).mp localPair
  · intro cold
    classical
    by_cases ha : Region (Union old next) root a
    · have hb := no_crossing_component (union := Union old next) (fun _ _ => Or.inr) ha cold
      exact Or.inr ⟨ha, hb, (induced_membership_exact ha hb).mpr cold⟩
    · exact Or.inl ⟨ha, (outside_membership_exact unchanged ha).mpr cold⟩

-- Padding the admitted domain does not require admitting the old rows again.
-- The exact edited rows are the only places where the padded graph can differ.
theorem append_patch_exact {active : V → Prop} {old next : V → V → Prop}
    {edited : V → Prop} {a b : V}
    (newOwnersAreEdits : ∀ owner, ¬ active owner → edited owner)
    (unchanged : ∀ x y, ¬ edited x → (active y ∧ old x y ↔ next x y)) :
    let padded := ActiveEdges active old
    let inside := Region (Union padded next) edited
    ((¬ inside a ∧ Mutual padded a b) ∨
      (inside a ∧ inside b ∧ Mutual (Induced next inside) a b)) ↔ Mutual next a b := by
  classical
  apply patch_exact
  intro x y untouched
  have present : active x :=
    Classical.byContradiction (fun missing => untouched (newOwnersAreEdits x missing))
  simpa [ActiveEdges, present] using unchanged x y untouched

#print axioms append_ordinals_are_fresh
#print axioms append_patch_exact

-- One changed row with deletions only: the old member index supplies the
-- exact induced repair region without any forward or reverse walk.
theorem single_removal_exact {old next : V → V → Prop} {cut a b : V}
    (deletesOnly : ∀ x y, next x y → old x y)
    (unchanged : ∀ x y, x ≠ cut → (old x y ↔ next x y)) :
    let inside := Mutual old cut
    ((¬ inside a ∧ Mutual old a b) ∨
      (inside a ∧ inside b ∧ Mutual (Induced next inside) a b)) ↔ Mutual next a b := by
  have union : Union old next = old := by
    funext x y
    exact propext ⟨fun e => e.elim id (deletesOnly x y), Or.inl⟩
  have region : Region old (· = cut) = Mutual old cut := by
    funext x
    exact propext one_root_region
  have general := patch_exact (old := old) (next := next) (root := (· = cut))
    (a := a) (b := b) unchanged
  simpa only [union, region] using general

#print axioms single_removal_exact

-- On the same source roster, exact membership also fixes the representative
-- chosen by the first-member rule. This does not assume discovery order.
theorem first_representative_exact (roster : List V) (patched cold : V → Bool)
    (same : ∀ v, patched v = cold v) :
    roster.find? patched = roster.find? cold := by
  rw [show patched = cold from funext same]

theorem quotient_roster_exact [DecidableEq V] (roster : List V) (patched cold : V → V)
    (same : ∀ key ∈ roster, patched key = cold key) :
    roster.filter (fun key => decide (patched key = key)) =
      roster.filter (fun key => decide (cold key = key)) := by
  induction roster with
  | nil => rfl
  | cons key rest ih =>
    have head := same key (by simp)
    have tail := ih (fun v member => same v (by simp [member]))
    simp only [List.filter_cons, head, tail]

#print axioms quotient_roster_exact

-- A consumer is dirty if it can follow dependencies to any edited owner.
-- This is exactly the direction enumerated by a reverse walk from the roots.
def Dirty (edge : V → V → Prop) (root : V → Prop) (consumer : V) : Prop :=
  ∃ provider, root provider ∧ Path edge consumer provider

theorem dirty_one_way {old next : V → V → Prop} {root : V → Prop} {consumer : V}
    (unchanged : ∀ x y, ¬ root x → old x y → next x y)
    (dirty : Dirty old root consumer) : Dirty next root consumer := by
  obtain ⟨target, edited, path⟩ := dirty
  induction path with
  | nil => exact ⟨_, edited, .nil _⟩
  | @step x y z edge _ ih =>
    classical
    by_cases atRoot : root x
    · exact ⟨x, atRoot, .nil x⟩
    · obtain ⟨provider, isRoot, suffix⟩ := ih edited
      exact ⟨provider, isRoot, .step (unchanged x y atRoot edge) suffix⟩

-- Fixed support, with every edited reader in the seed set. Walking the
-- predecessor is exact even if the ticket changes multiple dependency rows.
theorem old_inverse_exact {old next : V → V → Prop} {root : V → Prop} {consumer : V}
    (unchanged : ∀ x y, ¬ root x → (old x y ↔ next x y)) :
    Dirty old root consumer ↔ Dirty next root consumer :=
  ⟨dirty_one_way (fun x y h => (unchanged x y h).mp),
   dirty_one_way (fun x y h => (unchanged x y h).mpr)⟩

-- Before deduplication, group-code visits ordered members and their ordered
-- rows. Its output keeps both the actual provider node and its representative.
def routes (group : V) (owner : V → V) [DecidableEq V] : List V → List (V × V)
  | [] => []
  | node :: rest =>
    if owner node = group then routes group owner rest
    else (node, owner node) :: routes group owner rest

theorem routes_unchanged [DecidableEq V] (group : V) (old next : V → V)
    (row : List V) (stable : ∀ node ∈ row, old node = next node) :
    routes group old row = routes group next row := by
  induction row with
  | nil => rfl
  | cons node rest ih =>
    have same := stable node (List.mem_cons_self ..)
    have tail := ih (fun dep member => stable dep (List.mem_cons_of_mem node member))
    simp only [routes, same, tail]

-- Contrapositive of exact row projection: a changed route on an unchanged
-- row needs a remapped successor provider. The native successor inverse of
-- that provider must include this reader, even outside the SCC repair region.
theorem changed_route_requires_remapped_provider [DecidableEq V]
    (group : V) (old next : V → V) (row : List V)
    (changed : routes group old row ≠ routes group next row) :
    ∃ provider ∈ row, old provider ≠ next provider := by
  classical
  by_cases found : ∃ provider ∈ row, old provider ≠ next provider
  · exact found
  · apply False.elim
    apply changed
    apply routes_unchanged
    intro provider member
    exact Classical.byContradiction (fun remapped => found ⟨provider, member, remapped⟩)

-- The actual walk marks the reader's successor group, not the provider's
-- old group. Assume the successor inverse is the exact transpose of rows.
theorem changed_group_is_seeded [DecidableEq V] (old next : V → V)
    (row : V → List V) (readers : V → V → Prop) (reader : V)
    (transpose : ∀ r p, p ∈ row r ↔ readers p r)
    (changed : routes (next reader) old (row reader) ≠
               routes (next reader) next (row reader)) :
    ∃ p r, old p ≠ next p ∧ readers p r ∧ next r = next reader := by
  obtain ⟨provider, member, remapped⟩ :=
    changed_route_requires_remapped_provider (next reader) old next (row reader) changed
  exact ⟨provider, reader, remapped, (transpose reader provider).mp member, rfl⟩

private def twoCycle (a b : Bool) : Prop := a ≠ b
private def cut (a b : Bool) : Prop := a = true ∧ b = false
private def cutRoot (a : Bool) : Prop := a = false

private theorem cut_sink {b : Bool} (p : Path cut false b) : b = false := by
  cases p with
  | nil => rfl
  | step e _ => simp [cut] at e

-- Cutting false → true splits the old cycle. Walking only the new graph
-- misses true, even though its old SCC membership changes.
example : ¬ Region cut cutRoot true ∧
    Mutual twoCycle false true ∧ ¬ Mutual cut false true := by
  refine ⟨?_, ⟨.step (by simp [twoCycle]) (.nil _), .step (by simp [twoCycle]) (.nil _)⟩, ?_⟩
  · intro h
    obtain ⟨r, isRoot, p⟩ := h.1
    change r = false at isRoot
    subst r
    cases cut_sink p
  · intro h
    cases cut_sink h.1

#print axioms old_with_additions_exact
#print axioms outside_membership_exact
#print axioms induced_membership_exact
#print axioms no_crossing_component
#print axioms patch_exact
#print axioms first_representative_exact
#print axioms old_inverse_exact
#print axioms routes_unchanged
#print axioms changed_route_requires_remapped_provider
#print axioms changed_group_is_seeded

/-- The closure driver can interleave private native preparation with application
steps. A callback refusal retains the application's effects up to that point. -/
def runClosureEffects {Seed Application Failure : Type}
    (steps : List (PublicationEffect Seed (Except Failure Unit × Application)))
    (seed : Seed) (state : Except Failure Unit × Application) :
    Except Failure Unit × Application :=
  match state.1, steps with
  | .error _, _ => state
  | .ok _, [] => state
  | .ok _, .seed next :: rest => runClosureEffects rest (next seed) state
  | .ok _, .application call :: rest => runClosureEffects rest seed (call state)

def applyClosureEffect {Application Failure : Type}
    (state : Except Failure Unit × Application)
    (call : (Except Failure Unit × Application) → (Except Failure Unit × Application)) :=
  match state.1 with
  | .error _ => state
  | .ok _ => call state

private theorem closure_fold_after_failure {Application Failure : Type}
    (calls : List ((Except Failure Unit × Application) → (Except Failure Unit × Application)))
    (cause : Failure) (app : Application) :
    calls.foldl applyClosureEffect (.error cause, app) = (.error cause, app) := by
  induction calls with
  | nil => rfl
  | cons call rest ih => simpa [applyClosureEffect] using ih

theorem private_closure_steps_preserve_application_result
    {Seed Application Failure : Type}
    (steps : List (PublicationEffect Seed (Except Failure Unit × Application)))
    (seed : Seed) (state : Except Failure Unit × Application) :
    runClosureEffects steps seed state =
      (applicationEffects steps).foldl applyClosureEffect state := by
  induction steps generalizing seed state with
  | nil => rcases state with ⟨outcome, app⟩; cases outcome <;> rfl
  | cons step rest ih =>
    rcases state with ⟨outcome, app⟩
    cases step <;> cases outcome <;> simp [runClosureEffects, applicationEffects, ih, applyClosureEffect, closure_fold_after_failure]


inductive LensReadiness where
  | cold
  | incompatible
  | missing
  | ready

/-- Admission is only a projection of already stored native slots. An unknown
route or missing cell selects the original action without probing the lens. -/
def runLensPreparation {State Failure Result : Type}
    (readiness : LensReadiness) (prepare : Bool → State → Except Failure Result × State)
    (state : State) :=
  match readiness with
  | .ready => prepare true state
  | _ => prepare false state

theorem cold_lens_admission_runs_only_original_preparation
    {State Failure Result : Type} (readiness : LensReadiness)
    (prepare : Bool → State → Except Failure Result × State) (state : State)
    (unready : readiness ≠ .ready) :
    runLensPreparation readiness prepare state = prepare false state := by
  cases readiness <;> simp_all [runLensPreparation]


/-- A program owns a finite issued traversal. Retaining it replaces only the
selection work. Every observation still authenticates the traversal against
the current world on entry and after the actual callback. -/
def replayProgram {Read World Failure Value : Type}
    (read : List Read → World → Except Failure Unit)
    (traversal : List Read) (action : World → Except Failure Value × World)
    (world : World) : Except Failure Value × World :=
  match read traversal world with
  | .error cause => (.error cause, world)
  | .ok _ =>
    match action world with
    | (.error cause, after) => (.error cause, after)
    | (.ok value, after) =>
      match read traversal after with
      | .error cause => (.error cause, after)
      | .ok _ => (.ok value, after)

theorem retained_program_traversal_preserves_replay
    {Read World Failure Value : Type}
    (read : List Read → World → Except Failure Unit)
    (cold retained : List Read) (same : retained = cold)
    (action : World → Except Failure Value × World) (world : World) :
    replayProgram read retained action world = replayProgram read cold action world := by
  rw [same]

theorem retained_program_rechecks_after_callback
    {Read World Failure Value : Type}
    (read : List Read → World → Except Failure Unit) (traversal : List Read)
    (action : World → Except Failure Value × World) (before after : World)
    (value : Value) (cause : Failure)
    (entry : read traversal before = .ok ())
    (returns : action before = (.ok value, after))
    (stale : read traversal after = .error cause) :
    replayProgram read traversal action before = (.error cause, after) := by
  simp [replayProgram, entry, returns, stale]


/-- The quotient's owned row already holds the method and read support.
The public wrapper adds a receiver for observing its own slots. A closed
stock materializer can invoke the same guarded body directly. -/
def runOwnedMethod {State Failure Result : Type}
    (closed : Bool) (inspect : State → Except Failure Unit × State)
    (body : State → Except Failure Result × State) (state : State) :=
  if closed then body state
  else match inspect state with
       | (.ok _, after) => body after
       | (.error cause, after) => (.error cause, after)

theorem closed_owned_method_elides_only_identity_observation
    {State Failure Result : Type}
    (inspect : State → Except Failure Unit × State)
    (body : State → Except Failure Result × State) (state : State)
    (identityObservation : inspect state = (.ok (), state)) :
    runOwnedMethod true inspect body state = runOwnedMethod false inspect body state := by
  simp [runOwnedMethod, identityObservation]

theorem open_owned_method_preserves_observer_refusal
    {State Failure Result : Type}
    (inspect : State → Except Failure Unit × State)
    (body : State → Except Failure Result × State) (before after : State) (cause : Failure)
    (refused : inspect before = (.error cause, after)) :
    runOwnedMethod false inspect body before = (.error cause, after) := by
  simp [runOwnedMethod, refused]


theorem component_row_dedup_at_most_one {Owner : Type} [BEq Owner]
    (row : List Owner) (small : row.length ≤ 1) : row.eraseDups = row := by
  cases row with
  | nil => rfl
  | cons owner rest =>
    cases rest with
    | nil => rfl
    | cons next rest => simp at small


/-- Structural phases may differ in length and private seed state. Their
application projections must be empty before any shared author checkpoint. -/
theorem native_prefix_preserves_author_checkpoint
    {Seed Application Failure : Type}
    (full incremental : List (PublicationEffect Seed (Except Failure Unit × Application)))
    (fullSeed localSeed : Seed) (initial : Except Failure Unit × Application)
    (fullPrivate : applicationEffects full = [])
    (localPrivate : applicationEffects incremental = []) :
    runClosureEffects full fullSeed initial =
      runClosureEffects incremental localSeed initial := by
  rw [private_closure_steps_preserve_application_result,
      private_closure_steps_preserve_application_result, fullPrivate, localPrivate]

end SccEditRegion
