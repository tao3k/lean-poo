import LeanPoo.Functional.Validation

/-! Host predicate delegation composed with checked wrappers and typed observations.
This model assumes the host guard law; Scheme tests exercise the actual using macro.
-/
namespace Examples.ContractChecks
open LeanPoo.Functional.Validation

/-- User errors and the local host family can coexist without broad exception translation. -/
inductive Failure where
  | legacy | hostContract | exhausted | body
  deriving DecidableEq, Repr

/-- A small service contains a raw method before recursive normalization. -/
structure Raw where
  method : Int → Int
  allowed : Bool

/-- Normalization retains a guarded method, which consumers must use. -/
structure Checked where
  method : Int → Except Failure Int

/-- A host shape predicate accepts the supplied service; policy is checked later. -/
def shape (_ : Raw) : Except Failure Bool := .ok true

/-- Representative wrapping rejects invalid arguments without executing the raw method. -/
def normalize (raw : Raw) : Except Failure Checked :=
  if raw.allowed then .ok ⟨fun n => if n < 0 then .error .legacy else .ok (raw.method n)⟩
  else .error .legacy

/-- An observer returns both its result and updated host state, without losing either. -/
def observe (argument : Int) (count : Nat) (checked : Checked) : Except Failure (Int × Nat) :=
  (checked.method argument).map (fun result => (result, count + 1))

example : checkThen shape Failure.legacy normalize (observe 4 0) ⟨(· + 3), true⟩ = .ok (7, 1) := rfl
example : checkThen shape Failure.legacy normalize (observe (-1) 0) ⟨(· + 3), true⟩ = .error .legacy := rfl
example : checkThen shape Failure.legacy normalize (observe 4 0) ⟨(· + 3), false⟩ = .error .legacy := rfl

/-- Predicate host errors pass through even though local guard failures are translated. -/
example : checkArgument (fun (_ : Nat) => Except.error Failure.hostContract) Failure.legacy 4 =
    .error .hostContract := rfl

/-- A recursive exhaustion refusal is preserved by normalization, not relabeled. -/
example : checkThen (fun (_ : Nat) => .ok true) Failure.legacy
    (fun _ => Except.error Failure.exhausted) (fun (n : Nat) => .ok (n + 1)) 4 =
    .error .exhausted := rfl

/-- A consumer's host contract error remains original, including after successful wrapping. -/
example : checkThen shape Failure.legacy normalize (fun _ => Except.error Failure.hostContract : Checked → Except Failure Nat)
    ⟨(· + 3), true⟩ = .error .hostContract := rfl
end Examples.ContractChecks
