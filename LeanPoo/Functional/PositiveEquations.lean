import LeanPoo.Prototype.FiniteClosure
import LeanPoo.Functional.ConstructionCache
import Init.Data.Vector.Lemmas
import Init.Data.Vector.OfFn

/-! Finite positive Boolean component equations, including genuine cycles.
A structurally monotone syntax yields automatic least closure and compiles to
existing generalized lens declarations. This advances future work. -/
namespace LeanPoo.Functional.PositiveEquations

abbrev Bits (n : Nat) := Fin n → Bool

def Below (left right : Bits n) : Prop := ∀ index, left index = true → right index = true

instance bitsDecidable : {n : Nat} → DecidableEq (Bits n)
  | 0,left,right => isTrue (funext fun index => Fin.elim0 index)
  | n+1,left,right =>
    if head : left 0 = right 0 then
      match bitsDecidable (fun index : Fin n => left index.succ) (fun index => right index.succ) with
      | isTrue tail => isTrue (funext (Fin.cases head (fun index => congrFun tail index)))
      | isFalse tail => isFalse (by intro same; exact tail (congrArg (fun state => fun index : Fin n => state index.succ) same))
    else isFalse (by intro same; exact head (congrFun same 0))

def weight : {n : Nat} → Bits n → Nat
  | 0,_ => 0
  | _+1,state => (if state 0 then 1 else 0) + weight (fun index => state index.succ)

theorem weight_bound (state : Bits n) : weight state ≤ n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    have tail := ih (fun index => state index.succ)
    simp only [weight]
    split <;> omega

theorem weight_mono {left right : Bits n} (below : Below left right) : weight left ≤ weight right := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    have tail := ih (left := fun index => left index.succ) (right := fun index => right index.succ)
      (fun index present => below index.succ present)
    have head := below 0
    simp only [weight]
    cases l : left 0 <;> cases r : right 0 <;> simp_all
    omega

theorem weight_eq {left right : Bits n} (below : Below left right) (same : weight left = weight right) : left = right := by
  induction n with
  | zero => exact funext fun index => Fin.elim0 index
  | succ n ih =>
    have tailBelow : Below (fun index : Fin n => left index.succ) (fun index => right index.succ) :=
      fun index present => below index.succ present
    have tailMono := weight_mono tailBelow
    have head : left 0 = right 0 := by
      have implication := below 0
      simp only [weight] at same
      cases l : left 0 <;> cases r : right 0 <;> simp_all
      omega
    have tails : weight (fun index : Fin n => left index.succ) = weight (fun index => right index.succ) := by
      simpa [weight, head] using same
    exact funext (Fin.cases head (fun index => congrFun (ih tailBelow tails) index))

inductive Expr (n : Nat) where
  | literal (value : Bool)
  | read (index : Fin n)
  | both (left right : Expr n)
  | either (left right : Expr n)
  deriving Repr

def Expr.eval (state : Bits n) : Expr n → Bool
  | .literal value => value
  | .read index => state index
  | .both left right => left.eval state && right.eval state
  | .either left right => left.eval state || right.eval state

theorem Expr.monotone (expression : Expr n) {left right : Bits n} (below : Below left right) :
    expression.eval left = true → expression.eval right = true := by
  induction expression with
  | literal value => exact id
  | read index => exact below index
  | both first second ihFirst ihSecond =>
    simp only [eval, Bool.and_eq_true]
    exact fun pair => ⟨ihFirst pair.1,ihSecond pair.2⟩
  | either first second ihFirst ihSecond =>
    simp only [eval, Bool.or_eq_true]
    exact fun choice => choice.elim (fun first => Or.inl (ihFirst first)) (fun second => Or.inr (ihSecond second))

/-- A reusable quorum policy expressed entirely in positive constructors. -/
def Expr.twoOfThree (first second third : Expr n) : Expr n :=
  .either (.both first second) (.either (.both first third) (.both second third))

theorem Expr.twoOfThree_correct (first second third : Expr n) (state : Bits n) :
    (Expr.twoOfThree first second third).eval state =
      decide (2 ≤ (if first.eval state then 1 else 0) + (if second.eval state then 1 else 0) +
        (if third.eval state then 1 else 0)) := by
  simp only [twoOfThree,eval]
  cases first.eval state <;> cases second.eval state <;> cases third.eval state <;> rfl

abbrev Equations (n : Nat) := Fin n → Expr n

/-- The public synchronous equation semantics remains function-valued. -/
def step (equations : Equations n) (state : Bits n) : Bits n := fun index => (equations index).eval state

def system (equations : Equations n) : Prototype.FiniteClosure.System (Bits n) where
  bottom := fun _ => false
  below := Below
  trans first second index present := second index (first index present)
  bottomBelow := by intro state index present; contradiction
  step := step equations
  monotone below index := Expr.monotone _ below
  height := n
  weight
  bounded := weight_bound
  strict := by
    intro left right below different
    have mono := weight_mono below
    have unequal : weight left ≠ weight right := fun same => different (weight_eq below same)
    omega

/-- Read a materialized finite approximation without unfolding prior rounds. -/
private def storedValues (state : Vector Bool n) : Bits n := fun index => state[index.val]

/-- Standard vector tabulation recovers the complete function approximation. -/
private theorem storedValues_ofFn (state : Bits n) : storedValues (Vector.ofFn state) = state := by
  funext index
  simp [storedValues]

/-- Equal readers denote equal stored approximations, including empty vectors. -/
private theorem storedValues_injective : Function.Injective (storedValues (n := n)) := by
  intro left right same
  apply Vector.ext
  intro index bound
  exact congrFun same ⟨index,bound⟩

/-- The existing finite-height solver operates on explicit vectors internally.
Every transition constructs one complete next vector, so repeated reads cannot
rebuild previous synchronous rounds through a function-valued state. -/
private def storedSystem (equations : Equations n) : Prototype.FiniteClosure.System (Vector Bool n) where
  bottom := Vector.replicate n false
  below left right := Below (storedValues left) (storedValues right)
  trans first second index present := second index (first index present)
  bottomBelow := by intro state index present; simp [storedValues] at present
  step state := Vector.ofFn (step equations (storedValues state))
  monotone := by
    intro left right below index present
    simp only [storedValues_ofFn] at present ⊢
    exact Expr.monotone (equations index) below present
  height := n
  weight state := weight (storedValues state)
  bounded state := weight_bound (storedValues state)
  strict := by
    intro left right below different
    have unequal : storedValues left ≠ storedValues right := fun same => different (storedValues_injective same)
    have mono := weight_mono below
    have strict : weight (storedValues left) ≠ weight (storedValues right) := fun same => unequal (weight_eq below same)
    omega

/-- Solve with stored approximations, then return the original certified public
fixed-point interface. The finite unfolding, leastness and height are preserved;
the representation change adds no fuel, acceptance condition or failure case. -/
def close (equations : Equations n) : Prototype.FiniteClosure.Closed (system equations) :=
  let result := Prototype.FiniteClosure.close (storedSystem equations)
  { value := storedValues result.value
    fixed := by
      have fixed := congrArg storedValues result.fixed
      simpa only [storedSystem, system, storedValues_ofFn] using fixed
    least := by
      intro other fixed
      have lifted : (storedSystem equations).step (Vector.ofFn other) = Vector.ofFn other := by
        simp only [storedSystem, storedValues_ofFn]
        exact congrArg Vector.ofFn fixed
      have below := result.least (Vector.ofFn other) lifted
      simpa only [storedSystem, system, storedValues_ofFn] using below
    depth := result.depth
    bound := result.bound
    reached := by
      have related := Prototype.FiniteFix.iterate_relation
        (storedSystem equations).prototype (system equations).prototype
        (fun stored state => storedValues stored = state) () ()
        (storedSystem equations).bottom (system equations).bottom
        (by funext index; simp [storedSystem, system, storedValues])
        (by
          intro stored state same
          simp only [Prototype.FiniteClosure.System.prototype, storedSystem, system, storedValues_ofFn]
          rw [same]) result.depth
      rw [result.reached] at related
      exact related.symm }

/-- Stored closure has exactly the existing reference solver's least solution.
This transports semantic correctness; it does not assert compiler/runtime costs. -/
theorem close_reference (equations : Equations n) :
    (close equations).value = (Prototype.FiniteClosure.close (system equations)).value :=
  Prototype.FiniteClosure.least_unique (system equations)
    (fun first second => weight_eq first (Nat.le_antisymm (weight_mono first) (weight_mono second)))
    (close equations).value (close equations).fixed (close equations).least |>.symm

open GeneralizedGraph

def raw (state : Bits n) : State (Fin n) (fun _ => Bool) := fun index => some (.ok (state index))

/-- Missing recursive facts start false in this finite Boolean construction;
actual source errors remain errors in the compiled graph evaluator. -/
def Expr.compile : (expression : Expr n) → (index : Fin n) → Code (Fin n) (fun _ => Bool) index
  | .literal value,_ => .pure (fun _ => .ok value)
  | .read key,_ => .read key (fun _ value => value.getD (.ok false))
  | .both left right,index => .both (left.compile index) (right.compile index) (fun _ l r => do return (← l) && (← r))
  | .either left right,index => .both (left.compile index) (right.compile index) (fun _ l r => do return (← l) || (← r))

theorem Expr.compile_correct (expression : Expr n) (state : Bits n) (index : Fin n) :
    (expression.compile index).evaluate (provider (raw state)) () = .ok (.ok (expression.eval state)) := by
  induction expression with
  | literal value => rfl
  | read key => rfl
  | both left right ihLeft ihRight => simp [compile, Computation.evaluate, ihLeft, ihRight, eval, bind, Except.bind, pure, Except.pure]
  | either left right ihLeft ihRight => simp [compile, Computation.evaluate, ihLeft, ihRight, eval, bind, Except.bind, pure, Except.pure]

def declaration (equations : Equations n) : Declaration (Fin n) (fun _ => Bool) where
  keys := List.ofFn id
  code index := some ((equations index).compile index)
  base := fun _ => none

theorem resolve (equations : Equations n) (state : Bits n) (index : Fin n) :
    (declaration equations).resolve index (raw state) = some (.ok (step equations state index)) := by
  simp [Declaration.resolve, declaration, Expr.compile_correct, step, Except.bind]

/-- The result is an actual fixed point of the existing generalized lens
protocol. This path does not call the acyclic dependency scheduler. -/
def closed (equations : Equations n) :
    Prototype.Generalized.Closed (declaration equations).protocol (declaration equations).keys (declaration equations).base :=
  ⟨raw (close equations).value,by
    rw [Declaration.step_eq]
    funext index
    rw [resolve]
    exact congrArg (fun value : Bool => some (Except.ok (ε := ComputationError (Fin n)) value)) (congrFun (close equations).fixed index)⟩

/-- Adapt certified least closure to the existing publication cache boundary.
This solver does not invoke the ordinary graph Builder API, so those traces
are empty. Solver depth counts state advances, not individual evaluations. -/
def materialize (equations : Equations n) : ConstructionCache.Cache (declaration equations) :=
  let solution := close equations
  {closed := ⟨raw solution.value,by
      rw [Declaration.step_eq]
      funext index
      rw [resolve]
      exact congrArg (fun value : Bool => some (Except.ok (ε := ComputationError (Fin n)) value)) (congrFun solution.fixed index)⟩
   evaluated := []
   reused := []}

@[simp] theorem materialize_raw (equations : Equations n) :
    (materialize equations).closed.raw = raw (close equations).value := rfl

/-- A published closure carries no arbitrary seed: the least solution starts
from false, so unsupported cycles cannot perpetuate stale facts after revision. -/
theorem least (equations : Equations n) (other : Bits n) (fixed : step equations other = other) :
    Below (close equations).value other := (close equations).least other fixed

theorem least_unique (equations : Equations n) (other : Bits n) (fixed : step equations other = other)
    (otherLeast : ∀ value, step equations value = value → Below other value) : (close equations).value = other := by
  rw [close_reference]
  exact Prototype.FiniteClosure.least_unique (system equations)
    (fun first second => weight_eq first (Nat.le_antisymm (weight_mono first) (weight_mono second))) other fixed otherLeast

theorem updates_bound (equations : Equations n) : (close equations).depth ≤ n := (close equations).bound

/-- Logical equation evaluations for full shared rounds, including the final
stability comparison. Expression-node work, allocation and compiler time are
separate costs; a table read does not evaluate its equation again. -/
def roundEvaluations (equations : Equations n) : Nat := n * ((close equations).depth + 1)

/-- Finite-height closure bounds the shared-round evaluation budget quadratically.
This is an abstract work bound, not a host elapsed-time or allocation theorem. -/
theorem roundEvaluations_bound (equations : Equations n) :
    roundEvaluations equations ≤ n * (n + 1) :=
  Nat.mul_le_mul_left n (Nat.add_le_add_right (updates_bound equations) 1)

end LeanPoo.Functional.PositiveEquations
