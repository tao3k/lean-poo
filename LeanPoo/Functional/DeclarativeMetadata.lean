import LeanPoo.Functional.GenericFamily
import LeanPoo.Functional.Validation

/-! Finite method declarations and decidable refinement/logic metadata.
Elaboration uses existing dispatch edits; invocation uses the supplied existing
call operation. This advances generalized-prototype future work. -/
namespace LeanPoo.Functional.DeclarativeMetadata

/-- Qualifiers remain in the actual typed Method body (including existing
standard/qualified/simple contributions), rather than a second descriptive tag. -/
inductive Declaration (Args Method : Type) where
  | replace (name : String) (path : List Object.Specializer) (body : Method)
  | contribute (name : String) (path : List Object.Specializer) (body : Method)
  | guarded (name : String) (path : List Object.Specializer) (guard : Args → Bool) (body : Method)
  | remove (name : String) (path : List Object.Specializer)

def Declaration.name : Declaration Args Method → String
  | .replace name _ _ | .contribute name _ _ | .guarded name _ _ _ | .remove name _ => name

def Declaration.compile : Declaration Args Method → DispatchExtension.Edit Args Method
  | .replace _ path body => .register path body
  | .contribute _ path body => .contribute path body
  | .guarded _ path guard body => .registerWhen path guard body
  | .remove _ path => .erase path

/-- An adapter preserves existing method builders exactly while attaching names. -/
def Declaration.ofEdit (name : String) : DispatchExtension.Edit Args Method → Declaration Args Method
  | .register path body => .replace name path body
  | .contribute path body => .contribute name path body
  | .registerWhen path guard body => .guarded name path guard body
  | .erase path => .remove name path

@[simp] theorem Declaration.compile_ofEdit (name : String) (edit : DispatchExtension.Edit Args Method) :
    (Declaration.ofEdit name edit).compile = edit := by cases edit <;> rfl

/-- Existing registration, contribution order, guards, erasure and arity failures
are the semantics of a declaration batch, including empty and failing batches. -/
def install (seed : Object.Multimethod Args Method Result) (declarations : List (Declaration Args Method)) :=
  DispatchExtension.patch seed (declarations.map Declaration.compile)

theorem install_append (seed : Object.Multimethod Args Method Result)
    (front back : List (Declaration Args Method)) :
    install seed (front ++ back) = (install seed front).bind (fun next => install next back) := by
  simp only [install, List.map_append]
  induction front generalizing seed with
  | nil => rfl
  | cons declaration rest ih =>
    simp only [List.map_cons, List.cons_append, DispatchExtension.patch]
    cases declaration.compile.apply seed <;> simp_all [bind, Except.bind]

/-- The generic family keeps its existing seeds, cache laws and negative watches;
only the declarative source of its edits changes. -/
def family (base : GenericFamily.Model G Policy Cooked Args Method Result)
    (declarations : (key : G) → Policy → Cooked → List (Declaration (Args key) (Method key))) :
    GenericFamily.Model G Policy Cooked Args Method Result :=
  {base with methods := fun key policy cooked => (declarations key policy cooked).map Declaration.compile}

/-- Naming an existing batch is a migration adapter, with exact semantic parity. -/
def named (label : String) (edits : List (DispatchExtension.Edit Args Method)) :
    List (Declaration Args Method) :=
  edits.mapIdx fun index edit => Declaration.ofEdit (label ++ ":" ++ toString index) edit

theorem compile_named (label : String) (edits : List (DispatchExtension.Edit Args Method)) :
    (named label edits).map Declaration.compile = edits := by
  apply List.ext_getElem
  · simp [named]
  · intro index left right
    simp [named]

inductive Formula (Atom : Type) where
  | truth
  | atom (key : Atom)
  | both (left right : Formula Atom)
  | either (left right : Formula Atom)
  | implies (premise conclusion : Formula Atom)
  | deny (body : Formula Atom)
  deriving Repr

def Formula.Holds (meaning : Atom → Prop) : Formula Atom → Prop
  | .truth => True
  | .atom key => meaning key
  | .both left right => left.Holds meaning ∧ right.Holds meaning
  | .either left right => left.Holds meaning ∨ right.Holds meaning
  | .implies premise conclusion => premise.Holds meaning → conclusion.Holds meaning
  | .deny body => ¬ body.Holds meaning

instance Formula.decidable (meaning : Atom → Prop) [DecidablePred meaning] :
    (formula : Formula Atom) → Decidable (formula.Holds meaning)
  | .truth => inferInstanceAs (Decidable True)
  | .atom key => inferInstanceAs (Decidable (meaning key))
  | .both left right =>
    letI := left.decidable meaning
    letI := right.decidable meaning
    inferInstanceAs (Decidable (_ ∧ _))
  | .either left right =>
    letI := left.decidable meaning
    letI := right.decidable meaning
    inferInstanceAs (Decidable (_ ∨ _))
  | .implies premise conclusion =>
    letI := premise.decidable meaning
    letI := conclusion.decidable meaning
    inferInstanceAs (Decidable (_ → _))
  | .deny body =>
    letI := body.decidable meaning
    inferInstanceAs (Decidable (¬ _))

structure Evidence (meaning : Atom → Prop) (formula : Formula Atom) : Type where
  valid : formula.Holds meaning

/-- A decidable formula is also an exact-candidate StagedPublication admission
callback when its atom environment is computed from that candidate. -/
def Formula.check (formula : Formula Atom) (meaning : Atom → Prop) [DecidablePred meaning] :
    Except Unit (Evidence meaning formula) :=
  if valid : formula.Holds meaning then .ok ⟨valid⟩ else .error ()

theorem Formula.check_ok_iff (formula : Formula Atom) (meaning : Atom → Prop) [DecidablePred meaning] :
    (∃ evidence, formula.check meaning = .ok evidence) ↔ formula.Holds meaning := by
  constructor
  · rintro ⟨evidence, _⟩; exact evidence.valid
  · intro valid; exact ⟨⟨valid⟩, by simp [check, valid]⟩

structure Predicate (Value : Type) where
  name : String
  holds : Value → Prop
  decide : DecidablePred holds

/-- The input/output carriers are actual Lean types. Runtime metadata refines
those types; logical atoms may relate arguments and results dependently. -/
structure Contract (Atom Args Result : Type) where
  input : Predicate Args
  output : Predicate Result
  meaning : Atom → Args → Result → Prop
  decide : ∀ atom args result, Decidable (meaning atom args result)
  rule : Formula Atom

/-- Specialize dependent meaning while sharing invariant native predicate/formula
structure. This models deriving a contract prototype through its meaning slot. -/
def Contract.withMeaning (template : Contract Atom Args Result)
    (meaning : Atom → Args → Result → Prop)
    (decision : ∀ atom args result, Decidable (meaning atom args result)) : Contract Atom Args Result :=
  { template with meaning := meaning, decide := decision }

theorem Contract.withMeaning_input (template : Contract Atom Args Result) (meaning decision) :
    (template.withMeaning meaning decision).input = template.input := rfl

theorem Contract.withMeaning_output (template : Contract Atom Args Result) (meaning decision) :
    (template.withMeaning meaning decision).output = template.output := rfl

theorem Contract.withMeaning_rule (template : Contract Atom Args Result) (meaning decision) :
    (template.withMeaning meaning decision).rule = template.rule := rfl

theorem Contract.withMeaning_self (template : Contract Atom Args Result) :
    template.withMeaning template.meaning template.decide = template := by cases template; rfl

/-- Reusable invariant callbacks carry their exact source predicates and formula.
The equality witnesses are the semantic premise discharged by native identity
stamps under immutable descriptors. They certify neither pointer identity nor GC. -/
structure Contract.Checks (source : Contract Atom Args Result) where
  input : Predicate Args
  output : Predicate Result
  rule : Formula Atom
  sameInput : input = source.input
  sameOutput : output = source.output
  sameRule : rule = source.rule

/-- Capture only invariant metadata; executors, results and dependent meaning
are deliberately absent so a later service snapshot cannot reuse stale state. -/
def Contract.checks (source : Contract Atom Args Result) : source.Checks :=
  ⟨source.input, source.output, source.rule, rfl, rfl, rfl⟩

/-- Rebind current dependent meaning to certified shared invariant checks.
Changed source metadata requires new witnesses (or fresh compilation natively). -/
def Contract.Checks.specialize {source : Contract Atom Args Result} (checks : source.Checks)
    (meaning : Atom → Args → Result → Prop)
    (decision : ∀ atom args result, Decidable (meaning atom args result)) : Contract Atom Args Result :=
  ⟨checks.input, checks.output, meaning, decision, checks.rule⟩

/-- Shared checks reconstruct exactly ordinary withMeaning specialization.
Consequently all existing input/source/output/logic refusal and exact-state laws
apply unchanged; no semantic result is memoized by this optimization. -/
theorem Contract.Checks.specialize_eq {source : Contract Atom Args Result} (checks : source.Checks)
    (meaning : Atom → Args → Result → Prop)
    (decision : ∀ atom args result, Decidable (meaning atom args result)) :
    checks.specialize meaning decision = source.withMeaning meaning decision := by
  rcases checks with ⟨input, output, rule, hi, ho, hr⟩
  subst input; subst output; subst rule
  rfl

inductive Failure (Error : Type) where
  | input (name : String)
  | source (error : Error)
  | output (name : String)
  | logic
  deriving Repr, BEq

structure Invocation (contract : Contract Atom Args Result)
    (execute : Args → Except Error (Result × State)) (args : Args) where
  result : Result
  state : State
  called : execute args = .ok (result,state)
  input : contract.input.holds args
  output : contract.output.holds result
  logic : contract.rule.Holds (fun atom => contract.meaning atom args result)

/-- No intermediate state escapes a rejected output or rule. Source errors are
preserved, including a result which itself is an Except value. -/
def Contract.invoke (contract : Contract Atom Args Result)
    (execute : Args → Except Error (Result × State)) (args : Args) :
    Except (Failure Error) (Invocation contract execute args) :=
  letI := contract.input.decide
  letI := contract.output.decide
  if input : contract.input.holds args then
    match called : execute args with
    | .error error => .error (.source error)
    | .ok (result,state) =>
      if output : contract.output.holds result then
        letI : DecidablePred (fun atom => contract.meaning atom args result) := fun atom => contract.decide atom args result
        if logic : contract.rule.Holds (fun atom => contract.meaning atom args result) then
          .ok ⟨result,state,called,input,output,logic⟩
        else .error .logic
      else .error (.output contract.output.name)
  else .error (.input contract.input.name)

/-- Completeness includes exact returned state, not merely an allowed result. -/
theorem Contract.invoke_accepts (contract : Contract Atom Args Result)
    (execute : Args → Except Error (Result × State)) (args : Args) (result : Result) (state : State)
    (input : contract.input.holds args) (called : execute args = .ok (result,state))
    (output : contract.output.holds result)
    (logic : contract.rule.Holds (fun atom => contract.meaning atom args result)) :
    ∃ receipt, contract.invoke execute args = .ok receipt ∧ receipt.result = result ∧ receipt.state = state := by
  unfold Contract.invoke
  simp only [dite_eq_left input]
  split
  · rename_i error failed
    rw [called] at failed
    contradiction
  · rename_i actual next found
    have same := Except.ok.inj (found.symm.trans called)
    cases same
    simp [output, logic]

theorem Contract.invoke_source (contract : Contract Atom Args Result)
    (execute : Args → Except Error (Result × State)) (args : Args) (error : Error)
    (input : contract.input.holds args) (called : execute args = .error error) :
    contract.invoke execute args = .error (.source error) := by
  unfold Contract.invoke
  simp only [dite_eq_left input]
  split
  · rename_i actual failed
    have same := Except.error.inj (failed.symm.trans called)
    cases same
    rfl
  · rename_i result state found
    rw [called] at found
    contradiction

/-- Input refusal precedes execution and therefore every source outcome. -/
theorem Contract.invoke_input (contract : Contract Atom Args Result)
    (execute : Args → Except Error (Result × State)) (args : Args)
    (invalid : ¬ contract.input.holds args) :
    contract.invoke execute args = .error (.input contract.input.name) := by
  simp [Contract.invoke, invalid]

/-- A rejected output retains neither the result nor its tentative state. -/
theorem Contract.invoke_output (contract : Contract Atom Args Result)
    (execute : Args → Except Error (Result × State)) (args : Args) (result : Result) (state : State)
    (input : contract.input.holds args) (called : execute args = .ok (result,state))
    (invalid : ¬ contract.output.holds result) :
    contract.invoke execute args = .error (.output contract.output.name) := by
  unfold Contract.invoke
  simp only [dite_eq_left input]
  split
  · rename_i error failed
    rw [called] at failed
    contradiction
  · rename_i actual next found
    have same := Except.ok.inj (found.symm.trans called)
    cases same
    simp [invalid]

theorem Contract.invoke_logic (contract : Contract Atom Args Result)
    (execute : Args → Except Error (Result × State)) (args : Args) (result : Result) (state : State)
    (input : contract.input.holds args) (called : execute args = .ok (result,state))
    (output : contract.output.holds result)
    (invalid : ¬ contract.rule.Holds (fun atom => contract.meaning atom args result)) :
    contract.invoke execute args = .error .logic := by
  unfold Contract.invoke
  simp only [dite_eq_left input]
  split
  · rename_i error failed
    rw [called] at failed
    contradiction
  · rename_i actual next found
    have same := Except.ok.inj (found.symm.trans called)
    cases same
    simp [output, invalid]

/-- A bound contract is an ordinary invocation transformer. Wrappers can be
composed without introducing another result carrier or state protocol. -/
def Contract.wrap (contract : Contract Atom Args Result)
    (execute : Args → Except Error (Result × State)) :
    Args → Except (Failure Error) (Result × State) :=
  fun args => (contract.invoke execute args).map fun receipt => (receipt.result, receipt.state)

/-- The publication adapter exposes no tentative state on any rejection. -/
def Contract.publish (contract : Contract Atom Args Result) (old : State)
    (execute : Args → Except Error (Result × State)) (args : Args) :
    Except (Failure Error) Result × State :=
  match contract.wrap execute args with
  | .ok (result, next) => (.ok result, next)
  | .error failure => (.error failure, old)

theorem Contract.wrap_accepts (contract : Contract Atom Args Result)
    (execute : Args → Except Error (Result × State)) (args : Args) (result : Result) (state : State)
    (input : contract.input.holds args) (called : execute args = .ok (result,state))
    (output : contract.output.holds result)
    (logic : contract.rule.Holds (fun atom => contract.meaning atom args result)) :
    contract.wrap execute args = .ok (result,state) := by
  obtain ⟨receipt, accepted, sameResult, sameState⟩ :=
    contract.invoke_accepts execute args result state input called output logic
  simp [Contract.wrap, accepted, sameResult, sameState, Except.map]

theorem Contract.publish_refuses (contract : Contract Atom Args Result) (old : State)
    (execute : Args → Except Error (Result × State)) (args : Args) (failure : Failure Error)
    (rejected : contract.wrap execute args = .error failure) :
    contract.publish old execute args = (.error failure, old) := by
  simp [Contract.publish, rejected]

/-- Nested wrappers preserve the first inner refusal as an outer source failure;
outer output and logic checks cannot relabel an already rejected invocation. -/
theorem Contract.wrap_source (contract : Contract Atom Args Result)
    (execute : Args → Except Error (Result × State)) (args : Args) (error : Error)
    (input : contract.input.holds args) (called : execute args = .error error) :
    contract.wrap execute args = .error (.source error) := by
  simp [Contract.wrap, contract.invoke_source execute args error input called, Except.map]

end LeanPoo.Functional.DeclarativeMetadata
