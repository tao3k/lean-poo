import LeanPoo.Functional.SupportedComponents
import LeanPoo.Prototype.ComponentClosure

/-! Reusable finite-vector reference execution for component examples. Only final
successful source residuals certify values; bounded search may always refuse. -/
namespace LeanPoo.Functional.ComponentExecution
open GeneralizedGraph StrongComponents Prototype Prototype.Generalized
variable {n : Nat} {Value : Type}
/-- A candidate vector supplies actual successful predecessor outcomes. -/
def state (read : Fin n → Value) : State (Fin n) (fun _ => Value) := fun key => some (.ok (read key))
/-- Totalize errors only during candidate search; final residual validation below
cannot accept a default in place of an actual successful source result. -/
def observe (spec : Declaration (Fin n) (fun _ => Value)) (fallback : Fin n → Value)
    (key : Fin n) (read : Fin n → Value) : Value :=
  match spec.resolve key (state read) with
  | some (.ok value) => value
  | _ => fallback key
/-- Every active source resolver must return exactly the final candidate value. -/
def resolved [DecidableEq Value] (spec : Declaration (Fin n) (fun _ => Value)) (raw : Vector Value n) : Bool :=
  spec.keys.all fun key => match spec.resolve key (state raw.get) with
    | some (.ok value) => decide (value = raw.get key)
    | _ => false
/-- Accepted residuals exclude missing providers and errors for every active key. -/
theorem resolved_correct [DecidableEq Value] (spec : Declaration (Fin n) (fun _ => Value)) (raw : Vector Value n)
    (accepted : resolved spec raw = true) (key : Fin n) (member : key ∈ spec.keys) :
    spec.resolve key (state raw.get) = some (.ok (raw.get key)) := by
  have checked := List.all_eq_true.mp accepted key member
  cases found : spec.resolve key (state raw.get) with
  | none => simp [found] at checked
  | some outcome =>
    cases outcome with
    | error message => simp [found] at checked
    | ok value =>
      simp only [found, decide_eq_true_eq] at checked
      simp only [checked]
/-- Successful reference execution carries every ACTUAL active source equation. -/
structure Closed (spec : Declaration (Fin n) (fun _ => Value)) where
  raw : Vector Value n
  equations : ∀ key ∈ spec.keys, spec.resolve key (state raw.get) = some (.ok (raw.get key))
/-- Persistent vector focuses reuse the original generalized lens compiler. -/
def focus (key : Fin n) : MonoLens (Vector Value n) Value :=
  MonoLens.ofGetSet (fun raw => raw.get key) (fun value raw => raw.set key.val value key.isLt)
/-- All three focus laws hold for every value type and vector, independently of runs. -/
theorem focus_laws (key : Fin n) :
    LensLaws (fun raw : Vector Value n => raw.get key) (fun value raw => raw.set key.val value key.isLt) := by
  constructor
  · intro raw; simp [Vector.get]
  · intro raw value
    change (raw.set key.val value key.isLt)[key.val] = value
    exact Vector.getElem_set_self key.isLt
  · intro raw first second; simp
/-- Actual source programs read same cooked self inside each group and closed
predecessors outside it; there is no detached arithmetic equation family. -/
def parts (spec : Declaration (Fin n) (fun _ => Value)) (seed external : Vector Value n) :=
  componentParts focus (observe spec seed.get) (fun key (raw : Vector Value n) => raw.get key) external.get
/-- Execute whole discovered groups in supplied source order. These fixtures use
dependency-first representative order; this reference checker does not prove an
arbitrary order complete. Support equality and final real residuals fail closed. -/
def build [DecidableEq Value] (spec : Declaration (Fin n) (fun _ => Value))
    (graph : Supported (fun key dep => decide (dep ∈ spec.reads key)))
    (seed : Vector Value n) (budget : Nat) : Except String (Closed spec) := do
  unless graph.keys == spec.keys do throw "component support mismatch"
  let mut raw := seed
  let mut done : List (Fin n) := []
  for key in graph.keys do
    if key ∉ done then
      let members := graph.members key
      let group ← FeedbackCache.closeGroup (parts spec seed raw) id seed members seed budget
      raw := members.foldl (fun current node => current.set node.val (group.result.closed.raw.get node) node.isLt) raw
      done := done ++ members
  if valid : resolved spec raw = true then
    return ⟨raw,fun key member => resolved_correct spec raw valid key member⟩
  else throw "actual component resolver residual failed"
end LeanPoo.Functional.ComponentExecution
