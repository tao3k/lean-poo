import Std

/-! Finite rank-one prototype types. This advances the type-system future work in
Appendices C/D: explicit Self <: Super constraints, structural variance and finite
candidate inference. Host recognizers, effect behavior and mutable slot writes
are not identified with this semantic replacement relation. -/
namespace LeanPoo.Functional.PrototypeTypes

/-- The admitted scalar vocabulary has one proper numeric inclusion. -/
inductive Atom where
  | bool | integer | uint
  deriving Repr, DecidableEq
/-- Finite expressions reuse existing Type/Function/container constructor shapes.
Function lists retain exact input and multiple-output counts. -/
inductive Ty where
  | top | atom (name : Atom) | list (element : Ty) | tuple (fields : List Ty)
  | function (outputs inputs : List Ty)
  | pair (left right : Ty) | map (key value : Ty)
  | sum (tags : List Nat) (payloads : List Ty) | union (branches : List Ty)
  deriving Repr

/-- A pointwise relation checks exact length; zip cannot silently drop arguments. -/
def all₂ (test : Ty → Ty → Bool) : List Ty → List Ty → Bool
  | [], [] => true
  | a :: as, b :: bs => test a b && all₂ test as bs
  | _, _ => false

/-- Exact finite syntax identity is stricter than mutual derivability. It keeps
Map key normalization and ordered Union selection fixed, including nested arrows. -/
def same : Nat → Ty → Ty → Bool
  | 0, _, _ => false
  | fuel + 1, a, b => match a, b with
    | .top, .top => true
    | .atom a, .atom b => decide (a = b)
    | .list a, .list b => same fuel a b
    | .tuple as, .tuple bs | .union as, .union bs => all₂ (same fuel) as bs
    | .pair a b, .pair c d | .map a b, .map c d => same fuel a c && same fuel b d
    | .sum tags as, .sum tags' bs => decide (tags = tags') && all₂ (same fuel) as bs
    | .function outs ins, .function outs' ins' =>
        all₂ (same fuel) outs outs' && all₂ (same fuel) ins ins'
    | _, _ => false

/-- Exact list identity cannot lose, reorder or merge a branch. -/
theorem all₂_equal (test : Ty → Ty → Bool) (sound : ∀ a b, test a b = true → a = b)
    (as bs : List Ty) (accepted : all₂ test as bs = true) : as = bs := by
  induction as generalizing bs with
  | nil => cases bs <;> simp_all [all₂]
  | cons a as ih =>
    cases bs with
    | nil => simp [all₂] at accepted
    | cons b bs =>
      simp only [all₂, Bool.and_eq_true] at accepted
      have both := accepted
      exact congr (congrArg List.cons (sound a b both.1)) (ih bs both.2)

/-- Successful identity checks imply propositional equality, not a sampled match. -/
theorem same_sound (fuel : Nat) (a b : Ty) (accepted : same fuel a b = true) : a = b := by
  induction fuel generalizing a b with
  | zero => simp [same] at accepted
  | succ fuel ih =>
    cases a <;> cases b <;> simp only [same] at accepted
    all_goals try contradiction
    all_goals try rfl
    all_goals first
      | exact congrArg Ty.atom (of_decide_eq_true accepted)
      | exact congrArg Ty.list (ih _ _ accepted)
      | exact congrArg Ty.tuple (all₂_equal _ ih _ _ accepted)
      | exact congrArg Ty.union (all₂_equal _ ih _ _ accepted)
      | simp only [Bool.and_eq_true] at accepted
        have both := accepted
        first
        | exact congr (congrArg Ty.pair (ih _ _ both.1)) (ih _ _ both.2)
        | exact congr (congrArg Ty.map (ih _ _ both.1)) (ih _ _ both.2)
        | exact congr (congrArg Ty.function (all₂_equal _ ih _ _ both.1)) (all₂_equal _ ih _ _ both.2)
        | exact congr (congrArg Ty.sum (of_decide_eq_true both.1)) (all₂_equal _ ih _ _ both.2)

/-- Exact positional lifting of a relation, including empty argument lists. -/
inductive RelList (relation : Ty → Ty → Prop) : List Ty → List Ty → Prop where
  | nil : RelList relation [] []
  | cons : relation a b → RelList relation as bs → RelList relation (a :: as) (b :: bs)

/-- Declarative replacement, independent of prototype ancestry or samples. -/
inductive Subtype : Ty → Ty → Prop where
  | refl (a) : Subtype a a
  | top (a) : Subtype a .top
  | uint : Subtype (.atom .uint) (.atom .integer)
  | list : Subtype a b → Subtype (.list a) (.list b)
  | tuple : RelList Subtype as bs → Subtype (.tuple as) (.tuple bs)
  | pair : Subtype a c → Subtype b d → Subtype (.pair a b) (.pair c d)
  | map : Subtype a b → Subtype (.map key a) (.map key b)
  | sum : RelList Subtype as bs → Subtype (.sum tags as) (.sum tags bs)
  | function : RelList Subtype outs outs' → RelList Subtype ins' ins →
      Subtype (.function outs ins) (.function outs' ins')

/-- Finite derivability checker; exhaustion is separate from a negative result in
Scheme. Fuel here bounds derivation unfolding, not host GC or callback costs. -/
def check : Nat → Ty → Ty → Bool
  | 0, _, _ => false
  | fuel + 1, a, b =>
    match a, b with
    | _, .top => true
    | .atom a, .atom b => decide (a = b) || decide (a = .uint ∧ b = .integer)
    | .list a, .list b => check fuel a b
    | .tuple as, .tuple bs => all₂ (check fuel) as bs
    | .pair a b, .pair c d => check fuel a c && check fuel b d
    | .map k a, .map k' b => same fuel k k' && check fuel a b
    | .sum tags as, .sum tags' bs => decide (tags = tags') && all₂ (check fuel) as bs
    | .union as, .union bs => all₂ (same fuel) as bs
    | .function outs ins, .function outs' ins' =>
        all₂ (check fuel) outs outs' && all₂ (check fuel) ins' ins
    | _, _ => false

/-- Lift a Boolean comparison's soundness through exact positional matching. -/
theorem all₂_sound (test : Ty → Ty → Bool) (sound : ∀ a b, test a b = true → Subtype a b)
    (as bs : List Ty) (accepted : all₂ test as bs = true) : RelList Subtype as bs := by
  induction as generalizing bs with
  | nil => cases bs with
    | nil => exact .nil
    | cons b bs => simp [all₂] at accepted
  | cons a as ih =>
    cases bs with
    | nil => simp [all₂] at accepted
    | cons b bs =>
      have both : test a b = true ∧ all₂ test as bs = true := by simpa only [all₂, Bool.and_eq_true] using accepted
      obtain ⟨head, tail⟩ := both
      exact .cons (sound a b head) (ih bs tail)

/-- Every checked inclusion has a declarative derivation, including higher-order
contravariance and multiple-value arity. No relation is inferred from inheritance. -/
theorem check_sound (fuel : Nat) (a b : Ty) (accepted : check fuel a b = true) : Subtype a b := by
  induction fuel generalizing a b with
  | zero => simp [check] at accepted
  | succ fuel ih =>
    cases a <;> cases b <;> simp only [check] at accepted
    all_goals try { contradiction }
    all_goals try { exact .top _ }
    all_goals try { exact .list (ih _ _ accepted) }
    all_goals try { exact .tuple (all₂_sound _ ih _ _ accepted) }
    case pair.pair a b c d =>
      simp only [Bool.and_eq_true] at accepted
      have both := accepted
      exact .pair (ih _ _ both.1) (ih _ _ both.2)
    case map.map key a key' b =>
      simp only [Bool.and_eq_true] at accepted
      have both := accepted
      have equal := same_sound _ _ _ both.1
      subst key'
      exact .map (ih _ _ both.2)
    case sum.sum tags as tags' bs =>
      simp only [Bool.and_eq_true] at accepted
      have both := accepted
      have equal : tags = tags' := of_decide_eq_true both.1
      subst tags'
      exact .sum (all₂_sound _ ih _ _ both.2)
    case union.union as bs =>
      have equal := all₂_equal _ (same_sound fuel) _ _ accepted
      subst bs
      exact .refl _
    case function.function outs ins outs' ins' =>
      have both : all₂ (check fuel) outs outs' = true ∧ all₂ (check fuel) ins' ins = true := by
        simpa only [Bool.and_eq_true] using accepted
      exact .function (all₂_sound _ ih _ _ both.1) (all₂_sound _ ih _ _ both.2)
    case atom.atom a b =>
      cases a <;> cases b <;> simp_all
      all_goals first | exact .refl _ | exact .uint

/-- Admitted Map replacement cannot alter normalized key syntax. This is an
observational rule; permission to mutate the map requires a separate write law. -/
theorem map_key_invariant (fuel : Nat) (key key' value value' : Ty)
    (accepted : check fuel (.map key value) (.map key' value') = true) : key = key' := by
  cases fuel with
  | zero => simp [check] at accepted
  | succ fuel =>
    have both : same fuel key key' = true ∧ check fuel value value' = true := by
      simpa only [check, Bool.and_eq_true] using accepted
    exact same_sound _ _ _ both.1

/-- Ordered Union replacement fixes every branch, including duplicates and
higher-order payloads. A later permissive branch cannot erase a selected failure. -/
theorem union_branches_invariant (fuel : Nat) (as bs : List Ty)
    (accepted : check fuel (.union as) (.union bs) = true) : as = bs := by
  cases fuel with
  | zero => simp [check] at accepted
  | succ fuel => exact all₂_equal _ (same_sound fuel) _ _ accepted

/-- A Sum's finite tag skeleton is retained exactly; parser admission additionally
requires distinct tags and one payload for each tag before this algebra is built. -/
theorem sum_tags_invariant (fuel : Nat) (tags tags' : List Nat) (as bs : List Ty)
    (accepted : check fuel (.sum tags as) (.sum tags' bs) = true) : tags = tags' := by
  cases fuel with
  | zero => simp [check] at accepted
  | succ fuel =>
    have both : decide (tags = tags') = true ∧ all₂ (check fuel) as bs = true := by
      simpa only [check, Bool.and_eq_true] using accepted
    exact of_decide_eq_true both.1

/-- Semantic replacement is an explicit model premise. A bare Scheme procedure?
recognizer does not satisfy the arrow law; its behavioral interpretation must. -/
structure Interpretation (Value : Type) where
  accepts : Ty → Value → Prop
  top : ∀ a v, accepts a v → accepts .top v
  uint : ∀ v, accepts (.atom .uint) v → accepts (.atom .integer) v
  list : ∀ a b, (∀ v, accepts a v → accepts b v) →
    ∀ v, accepts (.list a) v → accepts (.list b) v
  tuple : ∀ as bs, RelList (fun a b => ∀ v, accepts a v → accepts b v) as bs →
    ∀ v, accepts (.tuple as) v → accepts (.tuple bs) v
  pair : ∀ a b c d, (∀ v, accepts a v → accepts c v) →
    (∀ v, accepts b v → accepts d v) → ∀ v, accepts (.pair a b) v → accepts (.pair c d) v
  map : ∀ key a b, (∀ v, accepts a v → accepts b v) →
    ∀ v, accepts (.map key a) v → accepts (.map key b) v
  sum : ∀ tags as bs, RelList (fun a b => ∀ v, accepts a v → accepts b v) as bs →
    ∀ v, accepts (.sum tags as) v → accepts (.sum tags bs) v
  function : ∀ outs outs' ins ins',
    RelList (fun a b => ∀ v, accepts a v → accepts b v) outs outs' →
    RelList (fun a b => ∀ v, accepts a v → accepts b v) ins' ins →
    ∀ v, accepts (.function outs ins) v → accepts (.function outs' ins') v

/-- Conditional denotational inclusion states exactly what safe replacement means.
The library wrapper still rechecks calls, outputs and exact evidence identities. -/
theorem replacement (model : Interpretation Value) (derivation : Subtype a b) :
    ∀ v, model.accepts a v → model.accepts b v := by
  exact Subtype.rec
    (motive_1 := fun a b _ => ∀ v, model.accepts a v → model.accepts b v)
    (motive_2 := fun as bs _ => RelList (fun a b => ∀ v, model.accepts a v → model.accepts b v) as bs)
    (fun _ _ h => h) model.top model.uint
    (fun _ ih => model.list _ _ ih)
    (fun _ ih => model.tuple _ _ ih)
    (fun _ _ ha hb => model.pair _ _ _ _ ha hb)
    (fun _ ih => model.map _ _ _ ih)
    (fun _ ih => model.sum _ _ _ ih)
    (fun _ _ ho hi => model.function _ _ _ _ ho hi)
    RelList.nil (fun _ _ head tail => RelList.cons head tail) derivation

/-- Rank-one templates bind named finite variables; arbitrary recursive equations
and higher-rank impredicative quantifiers are outside this expression language. -/
inductive Expr where
  | ground (type : Ty) | var (name : Nat)
  | list (element : Expr) | tuple (fields : List Expr)
  | function (outputs inputs : List Expr)
  | pair (left right : Expr) | map (key value : Expr)
  | sum (tags : List Nat) (payloads : List Expr) | union (branches : List Expr)
  deriving Repr

/-- Structural substitution is total in a supplied explicit environment. Admission
separately checks declared names, bounds and available candidate assignments. -/
def substitute (env : Nat → Ty) : Expr → Ty
  | .ground t => t
  | .var name => env name
  | .list e => .list (substitute env e)
  | .tuple es => .tuple (es.map (substitute env))
  | .pair a b => .pair (substitute env a) (substitute env b)
  | .map key value => .map (substitute env key) (substitute env value)
  | .sum tags es => .sum tags (es.map (substitute env))
  | .union es => .union (es.map (substitute env))
  | .function outs ins => .function (outs.map (substitute env)) (ins.map (substitute env))

/-- Bounds and call-site inequalities are checked together for each assignment. -/
def satisfies (fuel : Nat) (constraints : List (Expr × Expr)) (env : Nat → Ty) : Bool :=
  constraints.all fun (a, b) => check fuel (substitute env a) (substitute env b)

/-- A successful assignment proves every substituted constraint, without an
assumption that a field recognizer implies another arbitrary field recognizer. -/
theorem satisfies_sound (fuel constraints env) (accepted : satisfies fuel constraints env = true)
    (bound : (a, b) ∈ constraints) : Subtype (substitute env a) (substitute env b) := by
  exact check_sound _ _ _ ((List.all_eq_true.mp accepted) _ bound)

/-- Classification retains ambiguity. A singleton is accepted only after the
whole supplied finite assignment list was checked; a prefix is never a solution. -/
inductive Inference (Assignment : Type) where
  | none | unique (assignment : Assignment) | ambiguous (assignments : List Assignment)
  deriving Repr, DecidableEq
/-- Infer over an explicit finite universe; Scheme constructs the Cartesian list
lazily under its shared work counter, preserving this order and exact filtering. -/
def infer (valid : Assignment → Bool) (candidates : List Assignment) : Inference Assignment :=
  match candidates.filter valid with
  | [] => .none
  | [one] => .unique one
  | many => .ambiguous many

/-- Unique inference contains an actual admitted candidate, not the first match
of an incomplete or ambiguous search. -/
theorem infer_unique (valid : Assignment → Bool) (candidates : List Assignment)
    (accepted : infer valid candidates = .unique assignment) :
    assignment ∈ candidates ∧ valid assignment = true := by
  unfold infer at accepted
  split at accepted <;> simp_all
  next one matched =>
    have equal : one = assignment := by simpa using accepted
    subst one
    have member : assignment ∈ candidates.filter valid := by simp [matched]
    exact List.mem_filter.mp member

/-- Completed failure is exact within the supplied finite universe. It does not
claim that no instance exists outside that universe or at arbitrary rank. -/
theorem infer_none (valid : Assignment → Bool) (candidates : List Assignment)
    (refused : infer valid candidates = .none) :
    ∀ assignment ∈ candidates, valid assignment = false := by
  have empty : candidates.filter valid = [] := by
    unfold infer at refused
    split at refused <;> simp_all
  intro assignment member
  cases good : valid assignment with
  | false => rfl
  | true =>
    have inFiltered : assignment ∈ candidates.filter valid := List.mem_filter.mpr ⟨member, good⟩
    simp [empty] at inFiltered

/-- Unique bounded inference entails every substituted declaration/query law. -/
theorem inferred_constraints (fuel : Nat) (constraints : List (Expr × Expr)) (candidates : List (Nat → Ty))
    (accepted : infer (satisfies fuel constraints) candidates = .unique env)
    (bound : (a, b) ∈ constraints) : Subtype (substitute env a) (substitute env b) := by
  exact satisfies_sound _ _ _ (infer_unique _ _ accepted).2 bound

/-- Resource failure carries no partial assignment or initialized prototype. -/
inductive Failure where
  | unsupported | malformed | exhausted | bounds
  deriving Repr, DecidableEq
/-- Atomic bounded search refuses before classification when the assignment scan
is incomplete. Individual expression/comparison work is additionally metered by
Scheme; this abstract scan bound is not an exact allocation/performance claim. -/
def inferBounded (budget : Nat) (valid : Assignment → Bool) (candidates : List Assignment) :
    Except Failure (Inference Assignment) :=
  if candidates.length ≤ budget then .ok (infer valid candidates) else .error .exhausted

/-- Exhaustion cannot expose a unique candidate from an already accepted prefix. -/
theorem incomplete_refuses (budget : Nat) (valid : Assignment → Bool) (candidates : List Assignment)
    (incomplete : budget < candidates.length) :
    inferBounded budget valid candidates = .error .exhausted := by
  simp [inferBounded, Nat.not_le.mpr incomplete]

/-- A successful bounded unique result retains semantic candidate validity. -/
theorem bounded_unique (budget : Nat) (valid : Assignment → Bool) (candidates : List Assignment)
    (accepted : inferBounded budget valid candidates = .ok (.unique assignment)) :
    assignment ∈ candidates ∧ valid assignment = true := by
  unfold inferBounded at accepted
  split at accepted
  · exact infer_unique valid candidates (Except.ok.inj accepted)
  · contradiction

/-- Prefix binding fixes the first parameters and renumbers only the residual
variables. This is the semantic environment of capture-free residual syntax. -/
def prefixEnvironment (fixed : List Ty) (tail : Nat → Ty) (name : Nat) : Ty :=
  if present : name < fixed.length then fixed[name] else tail (name - fixed.length)

/-- A later inference assignment cannot overwrite an already bound ground prefix. -/
theorem prefixEnvironment_fixed (fixed : List Ty) (tail : Nat → Ty) (name : Nat)
    (present : name < fixed.length) : prefixEnvironment fixed tail name = fixed[name] := by
  simp [prefixEnvironment, present]

/-- The first unbound variable is exactly the first residual parameter. -/
theorem prefixEnvironment_tail (fixed : List Ty) (tail : Nat → Ty) (name : Nat) :
    prefixEnvironment fixed tail (fixed.length + name) = tail name := by
  have absent : ¬ fixed.length + name < fixed.length := by omega
  simp [prefixEnvironment, absent]

/-- Unique complete residual inference establishes every ORIGINAL substituted
bound/query under the combined environment, not just the unbound suffix alone. -/
theorem inferred_prefix_constraints (fuel budget : Nat) (fixed : List Ty)
    (constraints : List (Expr × Expr)) (candidates : List (Nat → Ty))
    (accepted : inferBounded budget (fun tail => satisfies fuel constraints (prefixEnvironment fixed tail))
      candidates = .ok (.unique tail)) (bound : (a,b) ∈ constraints) :
    Subtype (substitute (prefixEnvironment fixed tail) a) (substitute (prefixEnvironment fixed tail) b) := by
  exact satisfies_sound _ _ _ (bounded_unique _ _ _ accepted).2 bound

/-- Direct mathematical arrow replacement: accepting a broader input and
returning a narrower output suffices, assuming the original behavior is valid. -/
theorem function_replacement (sourceIn targetIn sourceOut targetOut : Value → Prop)
    (input : ∀ v, targetIn v → sourceIn v) (output : ∀ v, sourceOut v → targetOut v)
    (f : Value → Value) (behavior : ∀ v, sourceIn v → sourceOut (f v)) :
    ∀ v, targetIn v → targetOut (f v) := fun _v h => output _ (behavior _ (input _ h))
end LeanPoo.Functional.PrototypeTypes
