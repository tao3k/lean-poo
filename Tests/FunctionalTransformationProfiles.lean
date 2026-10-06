import LeanPoo.Functional.TransformationProfiles
import LeanPoo.Functional.TransformationResources
open LeanPoo.Functional.Transformation

def yesProblem : DecisionProblem where
  Input := Nat
  Valid := fun _ => True
  Yes := fun n => n = 0
example (n : Nat) : yesProblem.Yes n ↔ yesProblem.Yes
    (((CertifiedDecisionReduction.identity yesProblem).compose
      (CertifiedDecisionReduction.identity yesProblem)).forward n) := Iff.rfl

-- Unknown partial transport cannot acquire a successful transport witness.
def partialProblem : Problem where
  Input := Nat
  Result := fun _ => Nat
  Valid := fun _ => True
  Correct := fun n r => n = r
def unavailable : CertifiedPartialTransformation partialProblem partialProblem := ⟨fun _ => none⟩
example (n : Nat) : (unavailable.compose unavailable).forward n = none := rfl

-- The intermediate size affects the second resource charge.
#guard ((ResourceContract.mk ⟨2, 3⟩ ⟨1, 2⟩).compose
  (ResourceContract.mk ⟨3, 1⟩ ⟨4, 5⟩)).cost.apply 7 == 82
#guard ((ResourceContract.mk ⟨2, 3⟩ ⟨1, 2⟩).compose
  (ResourceContract.mk ⟨3, 1⟩ ⟨4, 5⟩)).size.apply 7 == 52

-- State changes revoke authorization for the next actual effect.
def once : EffectSystem.{0, 0} where
  State := Bool
  Effect := Unit
  Authorized := fun state _ => state = true
  Transition := fun _ _ after => after = false
example : AuthorizedTrace once true [()] false :=
  AuthorizedTrace.step (S := once) rfl rfl (AuthorizedTrace.nil (S := once) false)
theorem trace_head_authorized {S : EffectSystem} {a b : S.State}
    {e : S.Effect} {rest : List S.Effect}
    (trace : AuthorizedTrace S a (e :: rest) b) : S.Authorized a e := by
  cases trace with
  | step authorized _ _ => exact authorized
example : ¬ AuthorizedTrace once false [()] false := by
  intro trace
  have denied : false = true := trace_head_authorized trace
  cases denied
#print axioms decision_compose_equivalent
#print axioms optimization_compose_optimal
#print axioms resource_compose_assoc
#print axioms authorized_trace_append

#check measured_composition_bound
#check effectful_composition_sound
#print axioms measured_composition_bound
#print axioms effectful_composition_sound
