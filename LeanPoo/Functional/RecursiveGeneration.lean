import LeanPoo.Functional.PropertyTesting
import LeanPoo.Functional.PropertyScopes
import LeanPoo.Prototype.Recursive

/-! Guarded finite descriptor generation. A grammar lists the permitted ordered
child requests of each descriptor (bounded List widths are expanded alternatives).
Scalar values/PRNG behavior remain callback premises. A preorder trace records
actual grammar visits; a checked trace never asserts that its depth-bound domain
is the whole recursive Type. Scheme uses minimum-cost rows to choose feasible
alternatives; this model checks the resulting choices independently. -/
namespace LeanPoo.Functional.RecursiveGeneration

/-- Each finite alternative lists child descriptor identities in request order. -/
abbrev Grammar := Nat → List (List Nat)
/-- A request retains its own unfolding depth independently of the global quota. -/
abbrev Frame := Nat × Nat
/-- A trace entry is one chosen production, not a success receipt from a callback. -/
abbrev Entry := Nat × List Nat
/-- Controlled exhaustion is distinct from a malformed choice or callback error. -/
inductive Failure where
  | nodes | depth | choice | callback (message : String)
  deriving Repr, DecidableEq

/-- Children unfold one level, while siblings retain their individual limits. -/
def push (children : List Nat) (depth : Nat) (pending : List Frame) : List Frame :=
  children.map (·, depth) ++ pending

/-- Independent finite grammar checker. Both failed choices and exhausted bounds
refuse admission; accepting an empty prefix with pending work is impossible. -/
def check (grammar : Grammar) : Nat → List Frame → List Entry → Bool
  | _, [], [] => true
  | fuel + 1, (root, depth + 1) :: pending, (node, children) :: trace =>
    decide (node = root ∧ children ∈ grammar root) &&
      check grammar fuel (push children depth pending) trace
  | _, _, _ => false

/-- A seed transition proposes one production. Errors retain the callback message;
proposals are still checked against the actual descriptor grammar. -/
abbrev Choose (Seed : Type) := Nat → Nat → Nat → Seed → Except String (List Nat × Seed)

/-- Bounded constructive DFS. Every production spends one global visit before
pushing any child. A later failure returns no partial successful trace. -/
def construct (grammar : Grammar) (choose : Choose Seed) :
    Nat → List Frame → Seed → Except Failure (List Entry × Seed)
  | _, [], seed => .ok ([], seed)
  | 0, _ :: _, _ => .error .nodes
  | _ + 1, (_, 0) :: _, _ => .error .depth
  | fuel + 1, (root, depth + 1) :: pending, seed =>
    match choose root depth fuel seed with
    | .error message => .error (.callback message)
    | .ok (children, next) =>
      if children ∈ grammar root then
        (construct grammar choose fuel (push children depth pending) next).map
          (fun result => ((root, children) :: result.1, result.2))
      else .error .choice

/-- Every successful automatic construction has an independent finite derivation
at the original depths and quota, regardless of the chooser's heuristics. -/
theorem construct_checked (grammar : Grammar) (choose : Choose Seed)
    (fuel pending seed trace final)
    (success : construct grammar choose fuel pending seed = .ok (trace, final)) :
    check grammar fuel pending trace = true := by
  induction fuel generalizing pending seed trace final with
  | zero =>
    cases pending with
    | nil => simp [construct] at success; obtain ⟨rfl, rfl⟩ := success; rfl
    | cons frame rest => simp [construct] at success
  | succ fuel ih =>
    cases pending with
    | nil => simp [construct] at success; obtain ⟨rfl, rfl⟩ := success; rfl
    | cons frame rest =>
      rcases frame with ⟨root, depth⟩
      cases depth with
      | zero => simp [construct] at success
      | succ depth =>
        cases chosen : choose root depth fuel seed with
        | error message => simp [construct, chosen] at success
        | ok proposal =>
          rcases proposal with ⟨children, next⟩
          by_cases permitted : children ∈ grammar root
          · cases tail : construct grammar choose fuel (push children depth rest) next with
            | error error => simp [construct, chosen, permitted, tail, Except.map] at success
            | ok result =>
              rcases result with ⟨entries, finalSeed⟩
              simp [construct, chosen, permitted, tail, Except.map] at success
              obtain ⟨rfl, rfl⟩ := success
              simpa [check, permitted] using ih _ _ _ _ tail
          · simp [construct, chosen, permitted] at success

/-- Admission itself proves the total production count fits the global quota. -/
theorem check_length (grammar : Grammar) (fuel pending trace)
    (checked : check grammar fuel pending trace = true) : trace.length ≤ fuel := by
  induction fuel generalizing pending trace with
  | zero => cases pending <;> cases trace <;> simp_all [check]
  | succ fuel ih =>
    cases pending with
    | nil => cases trace <;> simp_all [check]
    | cons frame rest =>
      rcases frame with ⟨root, depth⟩
      cases depth with
      | zero => cases trace <;> simp [check] at checked
      | succ depth =>
        cases trace with
        | nil => simp [check] at checked
        | cons entry entries =>
          rcases entry with ⟨node, children⟩
          simp only [check, Bool.and_eq_true] at checked
          exact Nat.succ_le_succ (ih _ _ checked.2)

/-- Successful generation cannot exceed its node quota; depth alone is insufficient. -/
theorem construct_budget (grammar : Grammar) (choose : Choose Seed)
    (fuel pending seed trace final)
    (success : construct grammar choose fuel pending seed = .ok (trace, final)) : trace.length ≤ fuel :=
  check_length grammar fuel pending trace (construct_checked grammar choose fuel pending seed trace final success)

/-- Zero depth refuses a live root even when ample global quota remains. -/
theorem depth_refusal (grammar : Grammar) (choose : Choose Seed) (fuel root pending seed) :
    construct grammar choose (fuel + 1) ((root, 0) :: pending) seed = .error .depth := rfl

/-- An invalid chooser cannot install a production absent from the descriptor. -/
theorem choice_refusal (grammar : Grammar) (choose : Choose Seed) (fuel root depth pending seed children next)
    (chosen : choose root depth fuel seed = .ok (children, next)) (invalid : children ∉ grammar root) :
    construct grammar choose (fuel + 1) ((root, depth + 1) :: pending) seed = .error .choice := by
  simp [construct, chosen, invalid]

/-- Opaque callback errors are not depth exhaustion and cannot trigger fallback. -/
theorem callback_refusal (grammar : Grammar) (choose : Choose Seed) (fuel root depth pending seed message)
    (failed : choose root depth fuel seed = .error message) :
    construct grammar choose (fuel + 1) ((root, depth + 1) :: pending) seed = .error (.callback message) := by
  simp [construct, failed]

/-- Shrinking reuses the established finite candidate engine over independently
checked traces. Accepted witnesses retain both grammar membership and falsity. -/
theorem shrink_checked (grammar : Grammar) (depth quota root) (fails : List Entry → Bool)
    (measure : List Entry → Nat) (fuel best candidates)
    (valid : check grammar quota [(root, depth)] best = true) (falseWitness : fails best = true) :
    let result := (PropertyTesting.shrink (check grammar quota [(root, depth)]) fails measure fuel best candidates).1
    check grammar quota [(root, depth)] result = true ∧ fails result = true ∧ measure result ≤ measure best :=
  PropertyTesting.shrink_preserves _ _ _ _ _ _ valid falseWitness

/-- Reserving later siblings restores the exact pre-call quota. -/
theorem reserve_exact (remaining reserved : Nat) (fits : reserved ≤ remaining) :
    remaining - reserved + reserved = remaining := Nat.sub_add_cancel fits

/-- A child's unused allocation cannot manufacture quota for its siblings. -/
theorem restore_budget (remaining reserved unused : Nat) (fits : reserved ≤ remaining)
    (child : unused ≤ remaining - reserved) : unused + reserved ≤ remaining := by
  calc
    unused + reserved ≤ (remaining - reserved) + reserved := Nat.add_le_add_right child reserved
    _ = remaining := reserve_exact remaining reserved fits

/-- Saturated minimum costs preserve every feasibility comparison at the quota.
Costs beyond the quota need not grow unbounded integers during graph unfolding. -/
theorem saturation_feasible (cost quota : Nat) : min (quota + 1) cost ≤ quota ↔ cost ≤ quota := by
  by_cases fits : cost ≤ quota
  · simp [Nat.min_eq_right (Nat.le_trans fits (Nat.le_succ quota)), fits]
  · have over : quota + 1 ≤ cost := Nat.lt_of_not_ge fits
    simp [Nat.min_eq_left over, fits]

/-- Explicit requests thread the residual global quota, pending DFS and seed
through the existing safe source semantics. No host recursive fixed point is used. -/
def program (grammar : Grammar) (choose : Choose Seed) :
    Prototype.Recursive.Generator (Nat × List Frame × Seed) (Except Failure (List Entry × Seed)) :=
  fun (fuel, pending, seed) =>
    match fuel, pending with
    | _, [] => .value (.ok ([], seed))
    | 0, _ :: _ => .value (.error .nodes)
    | _ + 1, (_, 0) :: _ => .value (.error .depth)
    | fuel + 1, (root, depth + 1) :: pending =>
      match choose root depth fuel seed with
      | .error message => .value (.error (.callback message))
      | .ok (children, next) =>
        if children ∈ grammar root then
          .call (fuel, push children depth pending, next) (fun result =>
            .value (result.map (fun tail => ((root, children) :: tail.1, tail.2))))
        else .value (.error .choice)

/-- One source level per residual quota suffices to close the request program.
Source observation depth remains distinct from the grammar's unfolding depth. -/
theorem program_observation (grammar : Grammar) (choose : Choose Seed) (fuel pending seed) :
    Prototype.Recursive.solve (program grammar choose) (fuel + 1) (fuel, pending, seed) =
      .value (construct grammar choose fuel pending seed) := by
  induction fuel generalizing pending seed with
  | zero => cases pending <;> rfl
  | succ fuel ih =>
    cases pending with
    | nil => rfl
    | cons frame rest =>
      rcases frame with ⟨root, depth⟩
      cases depth with
      | zero => rfl
      | succ depth =>
        cases chosen : choose root depth fuel seed with
        | error message => simp [Prototype.Recursive.solve, program, construct, chosen,
            Prototype.Recursive.Interaction.interpret]
        | ok proposal =>
          rcases proposal with ⟨children, next⟩
          by_cases permitted : children ∈ grammar root
          · have step : program grammar choose (fuel + 1, (root, depth + 1) :: rest, seed) =
                .call (fuel, push children depth rest, next) (fun result =>
                  .value (result.map (fun tail => ((root, children) :: tail.1, tail.2)))) := by
                simp [program, chosen, permitted]
            rw [Prototype.Recursive.solve, step]
            simp only [Prototype.Recursive.Interaction.interpret]
            rw [ih]
            simp [construct, chosen, permitted]
          · simp [Prototype.Recursive.solve, program, construct, chosen, permitted,
              Prototype.Recursive.Interaction.interpret]

/-- Replay is stable under extensionally equal deterministic chooser callbacks.
The host additionally requires the same PRNG implementation and declared sources. -/
theorem replay_choices (grammar : Grammar) (left right : Choose Seed) (fuel pending seed)
    (same : ∀ root depth quota initial, left root depth quota initial = right root depth quota initial) :
    construct grammar left fuel pending seed = construct grammar right fuel pending seed := by
  have equal : left = right := funext fun root => funext fun depth =>
    funext fun quota => funext fun initial => same root depth quota initial
  rw [equal]

/-- Scalar admission and natural weight observation reuse the PBT action scope.
A rejected scalar supplies no derivation; only admitted fresh values can be
measured. Host predicate/measure fidelity and serial termination are premises. -/
def checkLeaf (live : State → Bool)
    (member : Value → State → Except Cause (Bool × State))
    (measure : Value → State → Except Cause (Nat × State)) (value : Value) (state : State) :
    Except (Option Cause) (Option Nat × State) :=
  PropertyTesting.guardedThen live (member value) (fun accepted after =>
    if accepted then
      match measure value after with
      | .error cause => .error cause
      | .ok (weight, final) => .ok (some weight, final)
    else .ok (none, after)) state

/-- An obsolete graph enters neither membership nor measurement. -/
theorem checkLeaf_preflight (live : State → Bool)
    (member : Value → State → Except Cause (Bool × State))
    (measure : Value → State → Except Cause (Nat × State)) (value : Value) (state : State)
    (stale : live state = false) : checkLeaf live member measure value state = .error none := by
  simp [checkLeaf, PropertyTesting.guardedThen, PropertyTesting.guardedGeneration, stale]

/-- A predicate revision cannot reach measurement or the next grammar request. -/
theorem checkLeaf_member_revised (live : State → Bool) (state after : State)
    (value : Value) (accepted : Bool) (measure : Value → State → Except Cause (Nat × State))
    (before : live state = true) (stale : live after = false) :
    checkLeaf live (fun _ _ => .ok (accepted, after)) measure value state = .error none := by
  simp [checkLeaf, PropertyTesting.guardedThen, PropertyTesting.guardedGeneration, before, stale]

/-- Normal membership refusal is not an exception or a falsifying property. -/
theorem checkLeaf_outside (live : State → Bool) (state after : State) (value : Value)
    (measure : Value → State → Except Cause (Nat × State))
    (before : live state = true) (fresh : live after = true) :
    checkLeaf live (fun _ _ => .ok (false, after)) measure value state = .ok (none, after) := by
  simp [checkLeaf, PropertyTesting.guardedThen, PropertyTesting.guardedGeneration, before, fresh]

/-- Predicate exceptions retain their exact cause without invoking measurement. -/
theorem checkLeaf_member_cause (live : State → Bool) (state : State) (value : Value) (cause : Cause)
    (measure : Value → State → Except Cause (Nat × State)) (before : live state = true) :
    checkLeaf live (fun _ _ => .error cause) measure value state = .error (some cause) := by
  simp [checkLeaf, PropertyTesting.guardedThen, PropertyTesting.guardedGeneration, before]

/-- Measurement errors remain the original errors, never alternative selection. -/
theorem checkLeaf_measure_cause (live : State → Bool) (state after : State)
    (value : Value) (cause : Cause) (before : live state = true) (fresh : live after = true) :
    checkLeaf live (fun _ _ => .ok (true, after)) (fun _ _ => .error cause) value state =
      .error (some cause) := by
  simp [checkLeaf, PropertyTesting.guardedThen, PropertyTesting.guardedGeneration, before, fresh]

/-- A revised measure cannot publish a partially observed scalar derivation. -/
theorem checkLeaf_measure_revised (live : State → Bool) (state middle after : State)
    (value : Value) (weight : Nat) (before : live state = true)
    (fresh : live middle = true) (stale : live after = false) :
    checkLeaf (Cause := Cause) live (fun _ _ => .ok (true, middle))
      (fun _ _ => .ok (weight, after)) value state = .error none := by
  simp [checkLeaf, PropertyTesting.guardedThen, PropertyTesting.guardedGeneration, before, fresh, stale]

/-- Fresh scalar admission retains its exact weight and resulting state. -/
theorem checkLeaf_present (live : State → Bool) (state middle after : State)
    (value : Value) (weight : Nat) (before : live state = true)
    (fresh : live middle = true) (current : live after = true) :
    checkLeaf (Cause := Cause) live (fun _ _ => .ok (true, middle))
      (fun _ _ => .ok (weight, after)) value state = .ok (some weight, after) := by
  simp [checkLeaf, PropertyTesting.guardedThen, PropertyTesting.guardedGeneration, before, fresh, current]

/-- Refusal suppresses every later sibling/request continuation of the interpreter. -/
theorem checkLeaf_refused (live : State → Bool)
    (member : Value → State → Except Cause (Bool × State))
    (measure : Value → State → Except Cause (Nat × State)) (value : Value) (state : State)
    (cause : Option Cause) (later : Option Nat × State → Except (Option Cause) Output)
    (refused : checkLeaf live member measure value state = .error cause) :
    (checkLeaf live member measure value state >>= later) = .error cause := by
  rw [refused]; rfl

end LeanPoo.Functional.RecursiveGeneration
