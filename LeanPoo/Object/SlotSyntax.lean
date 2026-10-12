import LeanPoo.Object.Resolve
import LeanPoo.Prototype.FixedPoint

/-! Topology-independent object composition. Both C3 and C4 orders use
the same declaration, delayed inherited method and final-self semantics. -/
namespace LeanPoo.Object

universe u v

/-- A precedence order together with its actual object declarations. -/
structure SlotSyntax (Key : Type u) (Value : Key → Type v) where
  declaration : String → Option (Declaration Key Value)
  precedence : List String

def SlotSyntax.defaultAt (program : SlotSyntax Key Value) (key : Key)
    (name : String) (inherited : Option (Value key)) : Option (Value key) :=
  match program.declaration name with
  | none => inherited
  | some declaration => (declaration.default key).orElse (fun _ => inherited)

def SlotSyntax.layer (program : SlotSyntax Key Value) (key : Key)
    (name : String) : Prototype.Method (Self Key Value) (Option (Value key)) :=
  match program.declaration name with
  | none => Prototype.Method.identity
  | some declaration => match declaration.slot key with
    | none => Prototype.Method.identity
    | some spec => spec.toMethod

/-- Paper `mix` in precedence order; every layer receives the same final self. -/
def SlotSyntax.methods (program : SlotSyntax Key Value) (key : Key) :
    Prototype.Method (Self Key Value) (Option (Value key)) :=
  program.precedence.foldr (fun name inherited =>
    Prototype.Method.compose (program.layer key name) inherited) Prototype.Method.identity

def SlotSyntax.resolve (program : SlotSyntax Key Value) (key : Key)
    (self : Self Key Value) : Option (Value key) :=
  program.methods key self (fun _ => program.precedence.foldr (program.defaultAt key) none)

/-- Parent-first assembly, corresponding to the paper's reversed C3 sequence. -/
def SlotSyntax.resolveForward (program : SlotSyntax Key Value) (key : Key)
    (self : Self Key Value) : Option (Value key) :=
  let defaults := program.precedence.reverse.foldl
    (fun inherited name => program.defaultAt key name inherited) none
  let methods := program.precedence.reverse.foldl
    (fun inherited name => Prototype.Method.compose (program.layer key name) inherited)
    Prototype.Method.identity
  methods self (fun _ => defaults)

/-- The parent-first source construction and precedence-ordered composition
agree for every key and final self, including missing slots. -/
theorem SlotSyntax.resolveForward_eq (program : SlotSyntax Key Value)
    (key : Key) (self : Self Key Value) :
    program.resolveForward key self = program.resolve key self := by
  simp only [SlotSyntax.resolveForward, SlotSyntax.resolve, SlotSyntax.methods,
    List.foldl_reverse]

def Plan.slotSyntax (plan : Plan Key Value) : SlotSyntax Key Value :=
  ⟨plan.schema.declaration, plan.precedence⟩

/-- The existing C4 object resolver is the same slot program. -/
theorem Plan.slotSyntax_resolve (plan : Plan Key Value) (key : Key)
    (self : Self Key Value) : plan.slotSyntax.resolve key self = plan.resolve key self := by
  rw [plan.resolve_eq_compileSlot, plan.compileSlot_apply]
  have methods (order : List String) :
      order.foldr (fun name inherited =>
        Prototype.Method.compose (plan.slotSyntax.layer key name) inherited)
        Prototype.Method.identity =
      order.foldr (plan.schema.methodStep key) Prototype.Method.identity := by
    induction order with
    | nil => rfl
    | cons name rest ih =>
      simp only [List.foldr_cons]
      rw [ih]
      simp only [SlotSyntax.layer, Plan.slotSyntax, Schema.methodStep]
      cases declared : plan.schema.declaration name with
      | none => simp [Prototype.Method.compose_identity_left]
      | some declaration =>
        cases slot : declaration.slot key with
        | none => simp [slot, Prototype.Method.compose_identity_left]
        | some spec => simp [slot]
  have defaults : plan.slotSyntax.defaultAt key = plan.schema.defaultStep key := by
    funext name inherited
    simp only [SlotSyntax.defaultAt, Plan.slotSyntax, Schema.defaultStep]
    cases declared : plan.schema.declaration name with
    | none => rfl
    | some declaration => cases value : declaration.default key <;> simp [value]
  unfold SlotSyntax.resolve SlotSyntax.methods
  rw [methods, defaults]
  rfl

/-- A certified fixed-point instance can use either topology policy. -/
structure SlotSyntax.Instance (program : SlotSyntax Key Value) where
  state : Self Key Value
  agrees : ∀ key, program.resolve key state = state key

def SlotSyntax.Instance.ref {program : SlotSyntax Key Value}
    (instanceValue : program.Instance) (key : Key) : Except (LookupError Key) (Value key) :=
  match instanceValue.state key with
  | none => .error (.noApplicableMethod key)
  | some value => .ok value

/-- One shared delayed self, using the existing runtime fixed-point constructor. -/
unsafe def SlotSyntax.instantiate {Key : Type} {Value : Key → Type}
    (program : SlotSyntax Key Value) : Thunk (Self Key Value) :=
  Prototype.sharedFix fun self key => program.resolve key (fun queried => self.get queried)

end LeanPoo.Object
