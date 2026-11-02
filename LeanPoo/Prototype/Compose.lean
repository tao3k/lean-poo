import LeanPoo.Prototype.FixedPoint

/-!
Typed prototype composition follows the POOF functional model by
François-René Rideau, Alex Knauth, and Nada Amin. Gerbil-POO proto.ss is
an executable reference for the same operations.
Both upstream repositories use Apache-2.0.
-/

namespace LeanPoo.Prototype

universe u v w x

/-- An open-recursive prototype sees the final self, an inherited value,
and produces a possibly different result type. -/
abbrev Proto (Self : Type u) (Parent : Type v) (Result : Type w) :=
  Self → Parent → Result

/-- The prototype that inherits its entire value unchanged. -/
def identity : Proto Self α α := fun _ inherited => inherited

/-- A terminal prototype supplies a value independently of final self and
the inherited input. It can close a chain without a bottom base value. -/
def constant (value : Result) : Proto Self Parent Result :=
  fun _ _ => value

/-- Child takes precedence; both prototypes see the same final self. -/
def compose (child : Proto Self Middle Result)
    (parent : Proto Self Parent Middle) : Proto Self Parent Result :=
  fun self inherited => child self (parent self inherited)

/-- The neutral prototype on the result side of composition. -/
theorem compose_identity_left (prototype : Proto Self Parent Result) :
    compose identity prototype = prototype := by
  funext self inherited
  rfl

/-- The neutral prototype on the inherited-input side. -/
theorem compose_identity_right (prototype : Proto Self Parent Result) :
    compose prototype identity = prototype := by
  funext self inherited
  rfl

/-- POOF's mix associativity, now checked for changing intermediate types. -/
theorem compose_assoc
    (outer : Proto Self B C) (middle : Proto Self A B)
    (inner : Proto Self Parent A) :
    compose (compose outer middle) inner =
      compose outer (compose middle inner) := by
  funext self inherited
  rfl

/-- A type-indexed chain of prototypes; adjacent result and parent types
must match, while the endpoints may differ. -/
inductive Chain (Self : Type u) : Type v → Type v → Type (max u (v + 1)) where
  | nil : Chain Self α α
  | cons : Proto Self Middle Result → Chain Self Parent Middle →
      Chain Self Parent Result

/-- Type-correct concatenation; the middle endpoint must match. -/
def Chain.append : Chain Self Middle Result → Chain Self Parent Middle →
    Chain Self Parent Result
  | .nil, parent => parent
  | .cons child tail, parent => .cons child (tail.append parent)

theorem Chain.nil_append (chain : Chain Self Parent Result) :
    Chain.append .nil chain = chain := rfl

theorem Chain.append_nil (chain : Chain Self Parent Result) :
    chain.append .nil = chain := by
  induction chain with
  | nil => rfl
  | cons _ _ inductionHypothesis =>
      simp only [Chain.append, inductionHypothesis]

theorem Chain.append_assoc
    (outer : Chain Self C D) (middle : Chain Self B C)
    (inner : Chain Self A B) :
    (outer.append middle).append inner =
      outer.append (middle.append inner) := by
  induction outer with
  | nil => rfl
  | cons _ _ inductionHypothesis =>
      simp only [Chain.append, inductionHypothesis]

def Chain.toProto : Chain Self Parent Result → Proto Self Parent Result
  | .nil => identity
  | .cons child tail => compose child tail.toProto

theorem Chain.toProto_append
    (child : Chain Self Middle Result) (parent : Chain Self Parent Middle) :
    (child.append parent).toProto = compose child.toProto parent.toProto := by
  induction child with
  | nil =>
      exact (compose_identity_left parent.toProto).symm
  | cons current tail inductionHypothesis =>
      simp only [Chain.append, Chain.toProto, inductionHypothesis, compose_assoc]

def Chain.ofList (prototypes : List (Proto Self α α)) : Chain Self α α :=
  prototypes.foldr Chain.cons Chain.nil

/-- Compose a homogeneous precedence list through the same typed chain. -/
def composeAll (prototypes : List (Proto Self α α)) : Proto Self α α :=
  (Chain.ofList prototypes).toProto

/-- The empty prototype list contributes no change to the inherited value. -/
theorem composeAll_nil : composeAll ([] : List (Proto Self α α)) = identity := rfl

/-- Head and suffix share the same final self, with the suffix evaluated first. -/
theorem composeAll_cons (head : Proto Self α α) (tail) :
    composeAll (head :: tail) = compose head (composeAll tail) := rfl

/-- A finite model of standard reduce-right's nonempty reduction. None denotes
an empty list; a singleton is retained without an identity composition wrapper.
This models the host operation, rather than certifying its implementation. -/
def reducePrototypes (prototypes : List (Proto Self α α)) : Option (Proto Self α α) :=
  prototypes.foldr (fun head tail => some (tail.elim head (compose head))) none

/-- Empty reduction has no supplied prototype. -/
theorem reducePrototypes_nil : reducePrototypes ([] : List (Proto Self α α)) = none := rfl

/-- The right reduction assembles a suffix before composing its head. -/
theorem reducePrototypes_cons (head : Proto Self α α) (tail) :
    reducePrototypes (head :: tail) =
      some ((reducePrototypes tail).elim head (compose head)) := rfl

/-- Apply the existing identity only when the standard reduction was empty. -/
def composeReduced (prototypes : List (Proto Self α α)) : Proto Self α α :=
  (reducePrototypes prototypes).getD identity

/-- The nonempty right reduction preserves a singleton extension directly. -/
theorem composeReduced_singleton (head : Proto Self α α) : composeReduced [head] = head := rfl

/-- Nonempty reduction has the same composition equation as the typed chain. -/
theorem composeReduced_cons (head : Proto Self α α) (tail) :
    composeReduced (head :: tail) = compose head (composeReduced tail) := by
  unfold composeReduced
  rw [reducePrototypes_cons]
  cases reducePrototypes tail <;> simp [compose_identity_right]

/-- Standard right reduction and the existing prototype interpreter agree on
every finite typed list, including its empty and singleton cases. -/
theorem composeReduced_eq (prototypes : List (Proto Self α α)) :
    composeReduced prototypes = composeAll prototypes := by
  induction prototypes with
  | nil => rfl
  | cons head tail ih => rw [composeReduced_cons, ih, composeAll_cons]

/-- Independently assembled batches compose in their original precedence order. -/
theorem composeReduced_append (front back : List (Proto Self α α)) :
    composeReduced (front ++ back) = compose (composeReduced front) (composeReduced back) := by
  induction front with
  | nil => simp [composeReduced, reducePrototypes, compose_identity_left]
  | cons head tail ih => simp only [List.cons_append, composeReduced_cons, ih, compose_assoc]

/-- A previously captured head composes with the suffix selected for this call.
The suffix list is supplied explicitly: host cell mutation and capture timing are
regression obligations, not consequences of this pure finite-list theorem. -/
theorem compose_captured_suffix (head : Proto Self α α) (currentSuffix) :
    compose head (composeReduced currentSuffix) = composeAll (head :: currentSuffix) := by
  rw [composeReduced_eq, composeAll_cons]

/-- Every layer sees the same final self; the inherited result flows inward out. -/
theorem composeReduced_apply_cons (head : Proto Self α α) (tail) (self : Self) (base : α) :
    composeReduced (head :: tail) self base = head self (composeReduced tail self base) := by
  rw [composeReduced_cons]
  rfl

/-- A function instance with a runtime representation distinct from a bare
function. The anchor prevents Lean from erasing the wrapper and eta-expanding
prototype construction into every call. -/
structure FixedFunction (Input Output : Type) where
  run : Input → Output
  runtimeAnchor : Nat := 0

def FixedFunction.ofFun (run : Input → Output) : FixedFunction Input Output :=
  { run }

instance : CoeFun (FixedFunction Input Output) (fun _ => Input → Output) where
  coe := FixedFunction.run

/-- Tie the paper's shared function fixed point. The prototype is applied
once to a recursive reference; every call then uses that one result. General
open recursion may diverge, so this executable knot is explicitly unsafe. -/
unsafe def instantiate {Input Output Parent : Type}
    (prototype : Proto (FixedFunction Input Output) Parent
      (FixedFunction Input Output))
    (base : Parent) : FixedFunction Input Output :=
  (sharedFix fun self =>
    prototype (FixedFunction.ofFun fun input => self.get input) base).get

/-- Instantiate an ordered homogeneous prototype composition in one step. -/
unsafe def instantiateAll {Input Output : Type}
    (prototypes : List (Proto (FixedFunction Input Output)
      (FixedFunction Input Output) (FixedFunction Input Output)))
    (base : FixedFunction Input Output) : FixedFunction Input Output :=
  instantiate (composeAll prototypes) base

/-- Lean notation for the existing composition operation; no second evaluator. -/
scoped infixr:65 " ⊕ " => compose

end LeanPoo.Prototype
