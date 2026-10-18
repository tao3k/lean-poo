import LeanPoo.Functional.PrototypeTypes
import LeanPoo.Functional.VariantValidation

/-! Bounded prototype type future work: the same UInt/Integer service signature,
Self <: Super bounds and higher-order negative positions as the Gerbil fixture. -/
namespace Examples.PrototypeTypes
open LeanPoo.Functional.PrototypeTypes

/-- Numeric service instances return a narrower value than their accepted input. -/
def service : Ty := .function [.atom .uint] [.atom .integer]
/-- Clients require only Integer outputs and supply UInt inputs. -/
def client : Ty := .function [.atom .integer] [.atom .uint]
example : check 8 service client = true := by decide
example : Subtype service client := check_sound 8 _ _ (by decide)
example : check 8 client service = false := by decide
/-- Nested higher-order/container observations preserve both directions. -/
example : check 12 (.list (.tuple [.atom .uint, service]))
    (.list (.tuple [.atom .integer, client])) = true := by decide
/-- Multiple return values cannot silently disappear through prefix matching. -/
example : check 8 (.function [.atom .uint, .atom .uint] [])
    (.function [.atom .integer] []) = false := by decide

/-- Explicit variables 0/1 correspond to Self/Super prototype parameters. -/
def signature : Expr := .function [.var 0] [.var 1]
/-- The appendix Proto A B is itself higher order when A/B are Functions. -/
def prototypeSignature : Expr := .function [.var 0] [.var 0, .var 1]
example : substitute (fun name => if name = 0 then service else client) prototypeSignature =
    .function [service] [service, client] := by simp [substitute, prototypeSignature]

/-- Bidirectional test constraints force UInt for both variables in this universe.
The negative Function argument occurrence supplies Self <: UInt. -/
def constraints : List (Expr × Expr) :=
  [(.var 0, .var 1), (.var 1, .var 0), (.ground (.atom .uint), .var 0),
   (.function [] [.ground (.atom .uint)], .function [] [.var 0])]
/-- Candidate assignments enumerate a caller-supplied finite universe in order. -/
def environment (self super : Ty) : Nat → Ty := fun name => if name = 0 then self else super
/-- Four explicit possibilities mirror two scalar choices for each parameter. -/
def candidates : List (Nat → Ty) :=
  [environment (.atom .uint) (.atom .uint), environment (.atom .uint) (.atom .integer),
   environment (.atom .integer) (.atom .uint), environment (.atom .integer) (.atom .integer)]
example : infer (satisfies 8 constraints) candidates =
    .unique (environment (.atom .uint) (.atom .uint)) := by
  simp [infer, satisfies, candidates, constraints, substitute, check, all₂, environment]
/-- Any admitted finite assignment proves each original bound after substitution. -/
example (env : Nat → Ty) (accepted : satisfies 8 constraints env = true) :
    Subtype (env 0) (env 1) :=
  by simpa only [substitute] using
    satisfies_sound (a := .var 0) (b := .var 1) 8 constraints env accepted (by simp [constraints])
/-- Partial enumeration cannot publish the first accepted UInt instance. -/
example : inferBounded 3 (satisfies 8 constraints) candidates = .error .exhausted := by
  apply incomplete_refuses
  decide
/-- With only Self <: Super the same universe has multiple valid specializations. -/
example : (match infer (satisfies 8 [(.var 0, .var 1)]) candidates with
    | .ambiguous _ => true | _ => false) = true := by
  simp [infer, satisfies, candidates, substitute, check, environment]
/-- The behavioral replacement premise handles real Int functions separately from
procedure recognition. Negative source inputs are permitted, results nonnegative. -/
example (f : Int → Int) (valid : ∀ n, 0 ≤ f n) :
    ∀ n : Int, 0 ≤ n → True :=
  function_replacement (fun _ : Int => True) (fun n => 0 ≤ n)
    (fun n => 0 ≤ n) (fun _ => True) (fun _ _ => trivial) (fun _ _ => trivial)
    f (fun n _ => valid n)
/-- Canonical Map keys and literal Sum tag IDs correspond to the Gerbil routing
fixture after Key-prefix specialization and syntax admission. -/
def routingMap : Expr := .map (.ground (.atom .uint))
  (.sum [0, 1] [.function [.var 0] [.var 1], .var 0])
/-- The exact declared result keeps Union order unchanged across substitution. -/
def routingOutput : Expr := .pair routingMap (.union [.ground service, .ground (.atom .bool)])
/-- One declared generic uses the same argument and result constructors. -/
def routing : Expr := .function [routingOutput] [routingMap]
/-- EXACT Gerbil obligations: original Self <: Super, actual Map <: formal Map,
and formal Pair <: expected Pair. No reverse/extra equality constraints are added. -/
def routingConstraints : List (Expr × Expr) :=
  [(.var 0, .var 1),
   (.ground (substitute (environment (.atom .uint) (.atom .integer)) routingMap), routingMap),
   (routingOutput, .ground (substitute (environment (.atom .uint) (.atom .integer)) routingOutput))]
example : infer (satisfies 8 routingConstraints) candidates =
    .unique (environment (.atom .uint) (.atom .integer)) := by
  have uu : satisfies 8 routingConstraints (environment (.atom .uint) (.atom .uint)) = false := by
    simp only [satisfies, routingConstraints, List.all_cons, List.all_nil, routingMap, routingOutput, substitute, List.map_cons, List.map_nil, environment, service]
    decide
  have ui : satisfies 8 routingConstraints (environment (.atom .uint) (.atom .integer)) = true := by
    simp only [satisfies, routingConstraints, List.all_cons, List.all_nil, routingMap, routingOutput, substitute, List.map_cons, List.map_nil, environment, service]
    decide
  have iu : satisfies 8 routingConstraints (environment (.atom .integer) (.atom .uint)) = false := by
    simp only [satisfies, routingConstraints, List.all_cons, List.all_nil, routingMap, routingOutput, substitute, List.map_cons, List.map_nil, environment, service]
    decide
  have ii : satisfies 8 routingConstraints (environment (.atom .integer) (.atom .integer)) = false := by
    simp only [satisfies, routingConstraints, List.all_cons, List.all_nil, routingMap, routingOutput, substitute, List.map_cons, List.map_nil, environment, service]
    decide
  simp only [infer, candidates, List.filter_cons, uu, ui, iu, ii, Bool.false_eq_true,
    ↓reduceIte, List.filter_nil, Bool.false_eq_true]
/-- Every new constructor participates in the existing universal inferred-bound
proof; the same assignment must satisfy both original and observed constraints. -/
example (env : Nat → Ty) (accepted : infer (satisfies 8 routingConstraints) candidates = .unique env)
    (member : (a, b) ∈ routingConstraints) : Subtype (substitute env a) (substitute env b) :=
  inferred_constraints 8 routingConstraints candidates accepted member
example : check 12 (.pair (.atom .uint) service) (.pair (.atom .integer) client) = true := by decide
example : check 12 (.map (.atom .uint) service) (.map (.atom .uint) client) = true := by decide
example : check 12 (.map (.atom .uint) service) (.map (.atom .integer) client) = false := by decide
example : check 12 (.sum [0, 1] [service, .atom .uint])
    (.sum [0, 1] [client, .atom .integer]) = true := by decide
example : check 12 (.sum [0, 1] [service, .atom .uint])
    (.sum [1, 0] [client, .atom .integer]) = false := by decide
example : check 12 (.union [service, client]) (.union [client, service]) = false := by decide
example : check 12 (.union [service, service]) (.union [service]) = false := by decide
example : check 12 (.union [service, client]) (.union [service, client]) = true := by decide
/-- The existing validator's collision theorem composes independently with type
inference: no successful inferred key identity can bypass runtime collision checks. -/
example (key : Nat → Except String Nat) (value : Nat → Except String Nat)
    (entries checked : List (Nat × Nat))
    (normalized : LeanPoo.Functional.Validation.traverse
      (LeanPoo.Functional.VariantValidation.pair key value) entries = .ok checked)
    (collision : LeanPoo.Functional.VariantValidation.distinctKeys (· == ·) checked = false) :
    LeanPoo.Functional.VariantValidation.map key value (· == ·) "collision" entries = .error "collision" :=
  LeanPoo.Functional.VariantValidation.map_collision _ _ _ _ _ _ normalized collision
#print axioms same_sound
#print axioms map_key_invariant
#print axioms union_branches_invariant
#print axioms sum_tags_invariant
#print axioms inferred_constraints
end Examples.PrototypeTypes
