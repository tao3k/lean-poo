import LeanPoo.Functional.Assembly

/-! Analyze finite pure capability computations, including composed helpers and
both conditional branches. Provider-wide callbacks retain an explicit unknown
footprint. No reflection assumption about arbitrary Lean functions is made. -/
namespace LeanPoo.Functional

universe u v w

inductive ComputationError (Key : Type v) where
  | missing (key : Key)
  | introduced (key : Key)
  | source (message : String)
  deriving Repr, BEq, DecidableEq

/-- Data reads need exact selected factories. Availability observations need
only presence equality. Inferred requirements/absences govern admission; both
branches contribute conservatively. Order and duplicates are retained. -/
structure DependencyFootprint (Key : Type v) where
  values : List Key := []
  presences : List Key := []
  required : List Key := []
  forbidden : List Key := []
  unknown : Bool := false
  deriving Repr

def DependencyFootprint.merge (left right : DependencyFootprint Key) : DependencyFootprint Key :=
  ⟨left.values ++ right.values, left.presences ++ right.presences,
    left.required ++ right.required, left.forbidden ++ right.forbidden,
    left.unknown || right.unknown⟩

/-- Typed computations whose provider access is inspectable. Pure callbacks
receive only the context and explicit child values; provider-wide access uses
`opaque`, which cannot silently acquire a known footprint. -/
inductive Computation (Context : Type u) (Key : Type v) (Value : Context → Key → Type w) :
    (Result : Context → Type w) → Type (max u v (w+1)) where
  | pure (value : Factory Context Result) : Computation Context Key Value Result
  | failure (message : String) : Computation Context Key Value Result
  | read (key : Key) (observe : ∀ c, Option (Value c key) → Result c) :
      Computation Context Key Value Result
  | need (key : Key) (observe : ∀ c, Value c key → Result c) :
      Computation Context Key Value Result
  | inspect (key : Key) (observe : ∀ c, Bool → Result c) :
      Computation Context Key Value Result
  | deny (key : Key) (value : Factory Context Result) : Computation Context Key Value Result
  | map (child : Computation Context Key Value Input)
      (transform : ∀ c, Input c → Result c) : Computation Context Key Value Result
  /-- Inspect only the child's value/context; refusals are source errors. -/
  | validate (child : Computation Context Key Value Input)
      (check : ∀ c, Input c → Except String (Result c)) : Computation Context Key Value Result
  | both (left : Computation Context Key Value Left) (right : Computation Context Key Value Right)
      (combine : ∀ c, Left c → Right c → Result c) : Computation Context Key Value Result
  | choose (guard : Computation Context Key Value Input) (condition : ∀ c, Input c → Bool)
      (yes no : Computation Context Key Value Result) : Computation Context Key Value Result
  | opaque (execute : Provider Context Key Value → ∀ c, Except (ComputationError Key) (Result c)) :
      Computation Context Key Value Result

variable {Context : Type u} {Key : Type v} {Value : Context → Key → Type w}
variable {Result : Context → Type w}

def Computation.analyze : {Result : Context → Type w} →
    Computation Context Key Value Result → DependencyFootprint Key
  | _, .pure _ | _, .failure _ => {}
  | _, .read key _ => {values := [key]}
  | _, .need key _ => {values := [key], required := [key]}
  | _, .inspect key _ => {presences := [key]}
  | _, .deny key _ => {presences := [key], forbidden := [key]}
  | _, .map child _ => child.analyze
  | _, .validate child _ => child.analyze
  | _, .both left right _ => left.analyze.merge right.analyze
  | _, .choose guard _ yes no => (guard.analyze.merge yes.analyze).merge no.analyze
  | _, .opaque _ => {unknown := true}

/-- Execute only the selected conditional branch. Presence checks never invoke
factory bodies; optional/required value reads invoke the selected factory at the
exact context. Local composition is structurally terminating. -/
def Computation.evaluate : {Result : Context → Type w} →
    Computation Context Key Value Result → Provider Context Key Value →
    (context : Context) → Except (ComputationError Key) (Result context)
  | _, .pure value, _, context => .ok (value context)
  | _, .failure message, _, _ => .error (.source message)
  | _, .read key observe, provider, context => .ok (observe context (apply provider context key))
  | _, .need key observe, provider, context => match provider key with
    | none => .error (.missing key)
    | some factory => .ok (observe context (factory context))
  | _, .inspect key observe, provider, context => .ok (observe context (provider key).isSome)
  | _, .deny key value, provider, context => if (provider key).isSome then .error (.introduced key) else .ok (value context)
  | _, .map child transform, provider, context => (child.evaluate provider context).map (transform context)
  | _, .validate child check, provider, context => (child.evaluate provider context).bind fun value =>
    match check context value with
    | .error message => .error (.source message)
    | .ok result => .ok result
  | _, .both left right combine, provider, context => do
    let l ← left.evaluate provider context
    let r ← right.evaluate provider context
    return combine context l r
  | _, .choose guard condition yes no, provider, context => do
    let value ← guard.evaluate provider context
    if condition context value then yes.evaluate provider context else no.evaluate provider context
  | _, .opaque execute, provider, context => execute provider context

/-- Inferred dependencies cover every provider observation of known syntax,
including nested helpers and every possible branch, at every context. No output
equality or decidable factory equality is assumed. -/
theorem Computation.evaluate_congr (code : Computation Context Key Value Result)
    (left right : Provider Context Key Value)
    (known : code.analyze.unknown = false)
    (values : ∀ key ∈ code.analyze.values, left key = right key)
    (presences : ∀ key ∈ code.analyze.presences, (left key).isSome = (right key).isSome)
    (context : Context) : code.evaluate left context = code.evaluate right context := by
  induction code with
  | pure value => rfl
  | failure message => rfl
  | read key observe =>
    simp only [Computation.evaluate, apply, values key (by simp [analyze])]
  | need key observe => simp only [evaluate, values key (by simp [analyze])]
  | inspect key observe => simp only [evaluate, presences key (by simp [analyze])]
  | deny key value => simp only [evaluate, presences key (by simp [analyze])]
  | map child transform ih => exact congrArg (fun result => result.map (transform context)) (ih known values presences)
  | validate child check ih => simp only [evaluate, ih known values presences]
  | both l r combine il ir =>
    have k : l.analyze.unknown = false ∧ r.analyze.unknown = false := by
      simpa [analyze, DependencyFootprint.merge, Bool.or_eq_false_iff] using known
    have kl := k.1
    have kr := k.2
    have el := il kl (fun key member => values key (by simp [analyze, DependencyFootprint.merge, member]))
      (fun key member => presences key (by simp [analyze, DependencyFootprint.merge, member]))
    have er := ir kr (fun key member => values key (by simp [analyze, DependencyFootprint.merge, member]))
      (fun key member => presences key (by simp [analyze, DependencyFootprint.merge, member]))
    simp only [evaluate, el, er]
  | choose guard condition yes no ig iy ino =>
    have k : guard.analyze.unknown = false ∧ yes.analyze.unknown = false ∧ no.analyze.unknown = false := by
      simpa [analyze, DependencyFootprint.merge, Bool.or_eq_false_iff, and_assoc] using known
    have eg := ig k.1 (fun key member => values key (by simp [analyze, DependencyFootprint.merge, member]))
      (fun key member => presences key (by simp [analyze, DependencyFootprint.merge, member]))
    have ey := iy k.2.1 (fun key member => values key (by simp [analyze, DependencyFootprint.merge, member]))
      (fun key member => presences key (by simp [analyze, DependencyFootprint.merge, member]))
    have en := ino k.2.2 (fun key member => values key (by simp [analyze, DependencyFootprint.merge, member]))
      (fun key member => presences key (by simp [analyze, DependencyFootprint.merge, member]))
    simp only [evaluate, eg, ey, en]
  | «opaque» execute => simp [analyze] at known

/-- Source errors are permitted; satisfied inferred guards exclude capability
errors from known syntax. Opaque callbacks retain their separate admission. -/
def CapabilitySafe : Except (ComputationError Key) α → Prop
  | .error (.missing _) | .error (.introduced _) => False
  | _ => True

private theorem capabilitySafe_map (first : Except (ComputationError Key) α)
    (safe : CapabilitySafe first) (transform : α → β) : CapabilitySafe (first.map transform) := by
  cases first with
  | ok value => trivial
  | error error => cases error <;> exact safe

private theorem capabilitySafe_bind (first : Except (ComputationError Key) α)
    (safe : CapabilitySafe first) (next : α → Except (ComputationError Key) β)
    (follows : ∀ value, CapabilitySafe (next value)) : CapabilitySafe (first.bind next) := by
  cases first with
  | ok value => exact follows value
  | error error => cases error <;> exact safe

theorem Computation.evaluate_capabilitySafe (code : Computation Context Key Value Result)
    (provider : Provider Context Key Value) (known : code.analyze.unknown = false)
    (available : ∀ key ∈ code.analyze.required, (provider key).isSome = true)
    (absent : ∀ key ∈ code.analyze.forbidden, provider key = none) (context : Context) :
    CapabilitySafe (code.evaluate provider context) := by
  induction code with
  | pure value => trivial
  | failure message => trivial
  | read key observe => trivial
  | need key observe =>
    have present := available key (by simp [analyze])
    cases found : provider key <;> simp [evaluate, found, CapabilitySafe] at present ⊢
  | inspect key observe => trivial
  | deny key value => simp [evaluate, absent key (by simp [analyze]), CapabilitySafe]
  | map child transform ih => exact capabilitySafe_map _ (ih known available absent) _
  | validate child check ih =>
    apply capabilitySafe_bind _ (ih known available absent) _
    intro value
    cases check context value <;> trivial
  | both l r combine il ir =>
    have k : l.analyze.unknown = false ∧ r.analyze.unknown = false := by
      simpa [analyze, DependencyFootprint.merge, Bool.or_eq_false_iff] using known
    have sl := il k.1 (fun key member => available key (by simp [analyze, DependencyFootprint.merge, member]))
      (fun key member => absent key (by simp [analyze, DependencyFootprint.merge, member]))
    have sr := ir k.2 (fun key member => available key (by simp [analyze, DependencyFootprint.merge, member]))
      (fun key member => absent key (by simp [analyze, DependencyFootprint.merge, member]))
    exact capabilitySafe_bind _ sl _ (fun _ => capabilitySafe_bind _ sr _ (fun _ => True.intro))
  | choose guard condition yes no ig iy ino =>
    have k : guard.analyze.unknown = false ∧ yes.analyze.unknown = false ∧ no.analyze.unknown = false := by
      simpa [analyze, DependencyFootprint.merge, Bool.or_eq_false_iff, and_assoc] using known
    have sg := ig k.1 (fun key member => available key (by simp [analyze, DependencyFootprint.merge, member]))
      (fun key member => absent key (by simp [analyze, DependencyFootprint.merge, member]))
    have sy := iy k.2.1 (fun key member => available key (by simp [analyze, DependencyFootprint.merge, member]))
      (fun key member => absent key (by simp [analyze, DependencyFootprint.merge, member]))
    have sn := ino k.2.2 (fun key member => available key (by simp [analyze, DependencyFootprint.merge, member]))
      (fun key member => absent key (by simp [analyze, DependencyFootprint.merge, member]))
    apply capabilitySafe_bind _ sg _
    intro value
    cases condition context value <;> assumption
  | «opaque» execute => simp [analyze] at known

end LeanPoo.Functional
