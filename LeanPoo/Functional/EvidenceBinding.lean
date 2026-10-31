import LeanPoo.Functional.DeclarativeMetadata

/-! Bind an existing invocation to explicit reference identities. Equality must
interpret reference identity for the adapter in use; no authentication is proved.
The projection is total here; Scheme projection exceptions are tested separately. -/
namespace LeanPoo.Functional.DeclarativeMetadata

/-- Transport the original formula into a larger atom space without collisions. -/
def Formula.relabel (rename : Atom → Other) : Formula Atom → Formula Other
  | .truth => .truth
  | .atom key => .atom (rename key)
  | .both left right => .both (left.relabel rename) (right.relabel rename)
  | .either left right => .either (left.relabel rename) (right.relabel rename)
  | .implies left right => .implies (left.relabel rename) (right.relabel rename)
  | .deny body => .deny (body.relabel rename)

/-- Relabeling preserves all connectives, including implication and negation. -/
theorem Formula.holds_relabel (formula : Formula Atom) (rename : Atom → Other) (meaning : Other → Prop) :
    (formula.relabel rename).Holds meaning ↔ formula.Holds (fun key => meaning (rename key)) := by
  induction formula <;> simp_all [Formula.relabel, Formula.Holds]

/-- Add one fresh atom to an existing invocation. Reference carriers and a pure
projection are supplied by the consumer; input/output policies remain effective. -/
def Contract.bindEvidence [DecidableEq Args] [DecidableEq Descriptor] [DecidableEq Context]
    (template : Contract Atom Args Result) (subject : Args) (descriptor : Descriptor) (context : Context)
    (view : Result → Args × Descriptor × Context) : Contract (Option Atom) Args Result where
  input := template.input
  output := template.output
  meaning key request result := match key with
    | some atom => template.meaning atom request result
    | none => request = subject ∧ view result = (subject,descriptor,context)
  decide key request result := match key with
    | some atom => template.decide atom request result
    | none => inferInstance
  rule := .both (template.rule.relabel some) (.atom none)

/-- Binding keeps the actual input policy, not merely its public label. -/
theorem Contract.bindEvidence_input [DecidableEq Args] [DecidableEq Descriptor] [DecidableEq Context]
    (template : Contract Atom Args Result) (subject : Args) (descriptor : Descriptor) (context : Context) (view) :
    (template.bindEvidence subject descriptor context view).input = template.input := rfl

/-- Binding keeps the actual output policy, including its existing rejection. -/
theorem Contract.bindEvidence_output [DecidableEq Args] [DecidableEq Descriptor] [DecidableEq Context]
    (template : Contract Atom Args Result) (subject : Args) (descriptor : Descriptor) (context : Context) (view) :
    (template.bindEvidence subject descriptor context view).output = template.output := rfl

/-- Neither the original rule nor any of the three reference associations can
be bypassed by the new binding. A matching record alone is not authorization. -/
theorem Contract.bindEvidence_logic_iff [DecidableEq Args] [DecidableEq Descriptor] [DecidableEq Context]
    (template : Contract Atom Args Result) (subject : Args) (descriptor : Descriptor) (context : Context)
    (view : Result → Args × Descriptor × Context) (request : Args) (result : Result) :
    (template.bindEvidence subject descriptor context view).rule.Holds
        (fun key => (template.bindEvidence subject descriptor context view).meaning key request result) ↔
      template.rule.Holds (fun key => template.meaning key request result) ∧
        request = subject ∧ view result = (subject,descriptor,context) := by
  simp [Contract.bindEvidence, Formula.Holds, Formula.holds_relabel]

/-- An accepted invocation contains original policy evidence plus exact binding. -/
theorem Contract.bindEvidence_accepted [DecidableEq Args] [DecidableEq Descriptor] [DecidableEq Context]
    (template : Contract Atom Args Result) (subject : Args) (descriptor : Descriptor) (context : Context)
    (view : Result → Args × Descriptor × Context)
    (execute : Args → Except Error (Result × State)) (request : Args)
    (receipt : Invocation (template.bindEvidence subject descriptor context view) execute request) :
    template.rule.Holds (fun key => template.meaning key request receipt.result) ∧
      request = subject ∧ view receipt.result = (subject,descriptor,context) :=
  (template.bindEvidence_logic_iff subject descriptor context view request receipt.result).mp receipt.logic

/-- With admitted input/output and a returned candidate, a mismatched binding
refuses in the logic phase and exposes exactly the old state. No effect rollback
or progress/freshness property of external services is implied. -/
theorem Contract.bindEvidence_publish_mismatch [DecidableEq Args] [DecidableEq Descriptor] [DecidableEq Context]
    (template : Contract Atom Args Result) (subject : Args) (descriptor : Descriptor) (context : Context)
    (view : Result → Args × Descriptor × Context) (old : State)
    (execute : Args → Except Error (Result × State)) (request : Args) (result : Result) (next : State)
    (input : template.input.holds request) (called : execute request = .ok (result,next))
    (output : template.output.holds result)
    (mismatch : ¬ (request = subject ∧ view result = (subject,descriptor,context))) :
    (template.bindEvidence subject descriptor context view).publish old execute request = (.error .logic,old) := by
  let bound := template.bindEvidence subject descriptor context view
  have invalid : ¬ bound.rule.Holds (fun key => bound.meaning key request result) := by
    intro valid
    exact mismatch ((template.bindEvidence_logic_iff subject descriptor context view request result).mp valid).2
  have refused := bound.invoke_logic execute request result next input called output invalid
  apply bound.publish_refuses old execute request .logic
  simp [Contract.wrap, refused, Except.map]
/-- The fused known-atom conjunction executes the original decision once and
only reaches the fresh evidence decision after true. Host Boolean admission
and exception-to-phase mapping remain the existing checked wrapper's job. -/
def Formula.conjoinAtom (previous : Except Error Bool) (evidence : Unit → Except Error Bool) : Except Error Bool :=
  previous.bind fun accepted => if accepted then evidence () else .ok false
/-- Original false short-circuits projection and exact-reference checks. -/
theorem Formula.conjoinAtom_false (evidence : Unit → Except Error Bool) :
    Formula.conjoinAtom (.ok false) evidence = .ok false := rfl
/-- An original decision exception is retained before evidence is evaluated. -/
theorem Formula.conjoinAtom_error (error : Error) (evidence : Unit → Except Error Bool) :
    Formula.conjoinAtom (.error error) evidence = .error error := rfl
/-- Successful original approval delegates the exact evidence result or error. -/
theorem Formula.conjoinAtom_true (evidence : Unit → Except Error Bool) :
    Formula.conjoinAtom (.ok true) evidence = evidence () := rfl
/-- Fusing an atom and conjunction preserves the existing declarative formula;
this eliminates construction nodes, not logical checks or binding freshness. -/
theorem Formula.conjoinAtom_holds (formula : Formula Atom) (key : Atom) (meaning : Atom → Prop)
    [DecidablePred meaning] :
    Formula.conjoinAtom (Error := Unit) (.ok (decide (formula.Holds meaning)))
      (fun _ => .ok (decide (meaning key))) =
        .ok (decide ((Formula.both formula (.atom key)).Holds meaning)) := by
  by_cases previous : formula.Holds meaning <;> by_cases next : meaning key <;>
    simp [Formula.conjoinAtom, Formula.Holds, previous, next, Except.bind]

end LeanPoo.Functional.DeclarativeMetadata
