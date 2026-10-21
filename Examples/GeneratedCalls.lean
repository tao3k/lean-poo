import LeanPoo.Functional.FunctionSignature
import LeanPoo.Functional.PrototypeTypeDescriptors
import LeanPoo.Functional.PropertyTesting

/-! Finite service controls for required/optional keys, ordered overloads,
reproducible trials and strict-domain shrinking. These are model examples;
Gerbil's native dispatcher and source-stamp behavior have separate runtime tests. -/
namespace Examples.GeneratedCalls
open LeanPoo.Functional.FunctionSignature LeanPoo.Functional.PropertyTesting

/-- A callback service accepts one base value, one optional slot and required scale. -/
def service : Signature String :=
  { required := 1, optional := 1, keywords := ["scale", "offset"], requiredKeywords := ["scale"] }

example : accepts service { positional := [3], keywords := [("scale", 2)] } = true := by decide
example : accepts service { positional := [3, 4], keywords := [("scale", 2), ("offset", 1)] } = true := by decide
example : accepts service { positional := [3], keywords := [] } = false := by decide
example : accepts service { positional := [3], keywords := [("scale", 2), ("scale", 3)] } = false := by decide
example : accepts service { positional := [3], keywords := [("unknown", 2)] } = false := by decide
example : accepts service { positional := [3, 4, 5], keywords := [("scale", 2)] } = false := by decide

/-- The later branch overlaps in arity but cannot override an earlier shape match. -/
def later : Signature String := { service with optional := 0, rest := true }
example : select [service, later] { positional := [3], keywords := [("scale", 2)] } = some service := by decide
example : select [service, later] { positional := [3, 4, 5], keywords := [("scale", 2)] } = some later := by decide

/-- A witnessed nonzero counterexample shrinks, refusing invalid and equal candidates. -/
def valid (n : Int) := decide (0 ≤ n)
/-- This deliberately false specification supplies a boundary counterexample at three. -/
def fails (n : Int) := decide (3 ≤ n)
example : shrink valid fails Int.natAbs 8 12 [-1, 12, 6, 2, 3, 0] = (3, 6) := by decide
example : shrink valid fails Int.natAbs 2 12 [-1, 12, 6, 3] = (12, 2) := by decide
example : locallyMinimal valid fails Int.natAbs 3 [0, 1, 2, -1] = true := by decide
example : admit (4 : Nat) 5 (3 : Int) = none := by decide

/-- A deterministic draw is only a model of stable generator state, not a claim
about the distribution or cross-version identity of the host pseudo-random source. -/
def draw (seed : Nat) (size : Nat) : Nat × Nat := (seed % (size + 1), seed + 17)
example : samples draw 4 3 8 = [3, 2, 1, 0] := by decide
example : samples draw 4 3 8 = samples draw 4 3 8 := rfl
/-- Explicit false is a payload, not an absent binding or omitted default. -/
def keywordBindings : List (String × Bool) := [("label", false), ("approved", true)]
example : decodeKeywords (encodeKeywords keywordBindings) = some keywordBindings := by decide
example : (encodeKeywords keywordBindings).length = 4 := by decide
example : decodeKeywords (Value := Bool) [.inl "dangling"] = none := rfl
#print axioms encodeKeywords_flatMap
#print axioms encodeKeywords_append
#print axioms encodeKeywords_length
#print axioms decode_encodeKeywords
#print axioms decodeKeywords_dangling

open LeanPoo.Functional.PrototypeTypes
/-- Empty mandatory products have no call values; nil/sentinels still do. -/
example : emptyCallRow 4 [.pair (.integerEnum []) (.function [.atom .uint] [.atom .uint])] = true := rfl
example : emptyCallRow 4 [.list (.integerEnum []), .maybe (.integerEnum []), .tuple []] = false := rfl
/-- The first dead clause shadows the later live clause; it is not removed. -/
example : selectedCallCheck 4 (fun (clause : Nat) => if clause = 0 then [.integerEnum []] else [.atom .uint])
    (fun _ => false) ([0, 1].find? (fun _ => true)) = true := rfl
example : selectedCallCheck 4 (fun (clause : Nat) => if clause = 0 then [.integerEnum []] else [.atom .uint])
    (fun _ => false) ([1, 0].find? (fun _ => true)) = false := rfl
/-- The zero/two-input service retains its live coverage obligations around a
reserved impossible one-input cell. The candidate controls the second live cell. -/
def retiringRows (candidate : Nat) : List (List Ty × Bool) :=
  [([], true), ([.pair (.integerEnum []) (.function [.atom .uint] [.atom .uint])], false),
    ([.atom .uint, .atom .uint], decide (candidate ≠ 1))]
/-- One original complete declaration solver selects/builds the entire service. -/
example : LeanPoo.Functional.DeclarativeMetadata.inferDeclared 2
    (fun candidate => callRowsCheck 4 (retiringRows candidate)) [0, 1]
    (fun candidate => (Except.ok ("handlers", candidate) : Except String (String × Nat))) =
      .ok (.unique 0, some ("handlers", 0)) := rfl
/-- Distinct complete accepted candidates remain ambiguous and build nothing. -/
example : LeanPoo.Functional.DeclarativeMetadata.inferDeclared 2
    (fun candidate => callRowsCheck 4 (retiringRows candidate)) [0, 2]
    (fun _ => (Except.error "builder must not run" : Except String Nat)) =
      .ok (.ambiguous [0, 2], none) := rfl
#print axioms emptyCallRow_refuses
#print axioms selectedCallCheck_live
#print axioms emptyCallRow_invoke_refused
#print axioms inferCallRows_sound
end Examples.GeneratedCalls
