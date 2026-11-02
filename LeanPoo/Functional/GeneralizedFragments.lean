import LeanPoo.Functional.GeneralizedGraph

/-! Inspectable inherited fragments for the generalized-prototype future work.
Existing Computation combinators compile ordered super wrappers into the existing
automatic graph closure. No second evaluator or fixed-point rule is introduced. -/
namespace LeanPoo.Functional.GeneralizedFragments
open GeneralizedGraph

abbrev Modifier (Key : Type) (Value : Key → Type) (key : Key) :=
  Computation Unit Key (fun _ dep => Outcome Key Value dep)
    (fun _ => Outcome Key Value key → Outcome Key Value key)
abbrev Guard (Key : Type) (Value : Key → Type) :=
  Computation Unit Key (fun _ dep => Outcome Key Value dep) (fun _ => Bool)

/-- Replace ignores inherited code. Extend explicitly evaluates a modifier and
then super. Conditional replacement observes final self and may select super. -/
inductive Fragment (Key : Type) (Value : Key → Type) (key : Key) where
  | replace (code : Code Key Value key)
  | extend (modifier : Modifier Key Value key)
  | conditional (guard : Guard Key Value) (code : Code Key Value key)

inductive Kind where
  | replace
  | extend
  | conditional
  deriving Repr, BEq, DecidableEq

def Fragment.kind : Fragment Key Value key → Kind
  | .replace _ => .replace
  | .extend _ => .extend
  | .conditional _ _ => .conditional

variable {Key : Type} {Value : Key → Type}

def compile (key : Key) (base : Option (Outcome Key Value key)) :
    List (Fragment Key Value key) → Code Key Value key
  | [] => .pure fun _ => base.getD (.error (.missing key))
  | .replace code :: _ => code
  | .extend modifier :: rest => .both modifier (compile key base rest) fun _ transform inherited => transform inherited
  | .conditional guard code :: rest => .choose guard (fun _ value => value) code (compile key base rest)

/-- No declaration preserves true slot absence; a wrapper without a base gets
an explicit missing-super outcome that the typed modifier may handle. -/
def node (key : Key) (base : Option (Outcome Key Value key)) (fragments : List (Fragment Key Value key)) :
    Option (Code Key Value key) := if fragments.isEmpty then none else some (compile key base fragments)

abbrev Binding (Key : Type) (Value : Key → Type) := (key : Key) × Fragment Key Value key

variable [DecidableEq Key]

def select (key : Key) (bindings : List (Binding Key Value)) : List (Fragment Key Value key) :=
  bindings.filterMap fun ⟨other,body⟩ => if same : other = key then some (same ▸ body) else none

def declaration (keys : List Key) (base : State Key Value) (bindings : List (Binding Key Value)) :
    GeneralizedGraph.Declaration Key Value :=
  ⟨keys,fun key => node key (base key) (select key bindings),base⟩

theorem select_append (key : Key) (front back : List (Binding Key Value)) :
    select key (front ++ back) = select key front ++ select key back := by
  simp [select, List.filterMap_append]

omit [DecidableEq Key]

/-- Override pruning is semantic and static: dead parents cannot introduce an
unknown footprint, a dependency edge, a missing capability or a source failure. -/
theorem replace_prunes (key : Key) (base : Option (Outcome Key Value key))
    (code : Code Key Value key) (parents : List (Fragment Key Value key)) :
    compile key base (.replace code :: parents) = code := rfl

theorem extend_metadata (key : Key) (base : Option (Outcome Key Value key))
    (modifier : Modifier Key Value key) (parents : List (Fragment Key Value key)) :
    (compile key base (.extend modifier :: parents)).analyze =
      modifier.analyze.merge (compile key base parents).analyze := rfl

/-- Failed modifier evaluation refuses before inherited evaluation. -/
theorem extend_modifier_error (key : Key) (base : Option (Outcome Key Value key))
    (modifier : Modifier Key Value key) (parents : List (Fragment Key Value key))
    (provider : Provider Unit Key (fun _ dep => Outcome Key Value dep))
    (error : ComputationError Key) (failed : modifier.evaluate provider () = .error error) :
    (compile key base (.extend modifier :: parents)).evaluate provider () = .error error := by
  simp [compile, Computation.evaluate, failed, bind, Except.bind]

/-- Successful wrappers retain both evaluation and component failures exactly. -/
theorem extend_evaluate (key : Key) (base : Option (Outcome Key Value key))
    (modifier : Modifier Key Value key) (parents : List (Fragment Key Value key))
    (provider : Provider Unit Key (fun _ dep => Outcome Key Value dep)) :
    (compile key base (.extend modifier :: parents)).evaluate provider () =
      (modifier.evaluate provider ()).bind (fun transform =>
        ((compile key base parents).evaluate provider ()).map transform) := by
  rfl

/-- Interpret one inherited fragment through the existing generalized lens.
The outer evaluation error is retained until the complete slot is installed. -/
def compiler (key : Key) : Prototype.Generalized.Compiler
    (Except (ComputationError Key) (Outcome Key Value key)) (State Key Value) (Fragment Key Value key) :=
  Prototype.lensGen id (fun value _ => value) fun fragment self inherited =>
    let provider := GeneralizedGraph.provider self.get
    match fragment with
    | .replace code => code.evaluate provider ()
    | .extend modifier => (modifier.evaluate provider ()).bind fun transform => inherited.get.map transform
    | .conditional guard code => (guard.evaluate provider ()).bind fun choose =>
      if choose then code.evaluate provider () else inherited.get

/-- Compilation into analyzed computations agrees with actual delayed
inheritance for every final self, base, error and ordered fragment list. -/
theorem compile_inheritance (key : Key) (base : Option (Outcome Key Value key))
    (fragments : List (Fragment Key Value key)) (self : State Key Value) :
    (compile key base fragments).evaluate (GeneralizedGraph.provider self) () =
      Prototype.DelayedProto.composeAll (fragments.map (compiler key))
        (Thunk.mk fun _ => self) (Thunk.mk fun _ => .ok (base.getD (.error (.missing key)))) := by
  induction fragments with
  | nil => rfl
  | cons fragment rest ih =>
    cases fragment with
    | replace code => rfl
    | extend modifier =>
      change (modifier.evaluate _ ()).bind (fun transform =>
        ((compile key base rest).evaluate _ ()).map transform) = _
      rw [ih]
      rfl
    | conditional guard code =>
      change (guard.evaluate _ ()).bind (fun choose =>
        if choose then code.evaluate _ () else (compile key base rest).evaluate _ ()) = _
      rw [ih]
      rfl

end LeanPoo.Functional.GeneralizedFragments
