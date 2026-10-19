import LeanPoo.Functional.PrototypeTypes
import LeanPoo.Functional.PrototypeTypeDescriptors
import LeanPoo.Functional.VariantValidation
import LeanPoo.Functional.MethodDeclarations

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
  -- Reduce four ground judgments before filtering function-valued assignments.
  have unsigned : satisfies 8 constraints (environment (.atom .uint) (.atom .uint)) = true := by
    simp [satisfies, constraints, substitute, check, emptySource, emptyCheck, emptyTarget, all₂, environment]
  have mixedLeft : satisfies 8 constraints (environment (.atom .uint) (.atom .integer)) = false := by
    simp [satisfies, constraints, substitute, check, emptySource, emptyCheck, emptyTarget, all₂, environment]
  have mixedRight : satisfies 8 constraints (environment (.atom .integer) (.atom .uint)) = false := by
    simp [satisfies, constraints, substitute, check, emptySource, emptyCheck, emptyTarget, all₂, environment]
  have signed : satisfies 8 constraints (environment (.atom .integer) (.atom .integer)) = false := by
    simp [satisfies, constraints, substitute, check, emptySource, emptyCheck, emptyTarget, all₂, environment]
  simp [infer, candidates, unsigned, mixedLeft, mixedRight, signed]
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
/-- Label is prefix-bound Symbol; the finite residual candidates are the same
heterogeneous Bool/Symbol/String alternatives used by the Gerbil text service. -/
def textEnvironment (value : Atom) : Nat → Ty :=
  prefixEnvironment [.atom .symbol] (fun _ => .atom value)
/-- Original supplied-input and expected-result constraints share the nested
callback's negative Label position and positive Value position. -/
def textConstraints : List (Expr × Expr) :=
  [(.ground (.atom .symbol), .var 0), (.var 1, .ground (.atom .string)),
   (.function [.var 1] [.var 0], .ground (.function [.atom .string] [.atom .symbol]))]
/-- Public parameters are the existing positional Template, with no new binder. -/
def textParameters : LeanPoo.Functional.Parameters.Template String Ty :=
  ⟨["Label", "Value"], fun _ => none⟩
/-- Prefix and residual specialization must both finish before declaration work.
The returned pair records the actual bound fields; host effects are not modeled. -/
def buildText (value : Atom) : Except String (Ty × Ty) := do
  let staged ← (LeanPoo.Functional.Parameters.checkedSpecialize ".parameters" textParameters
    [.atom .symbol]).mapError (fun _ => "prefix")
  (LeanPoo.Functional.DeclarativeMetadata.specializeDeclared ".parameters" staged [.atom value]
    (fun bound => (do
      if !bound.remaining.isEmpty then throw "residual parameters"
      let some label := bound.fields "Label" | throw "missing Label"
      let some result := bound.fields "Value" | throw "missing Value"
      pure (label, result) : Except String (Ty × Ty)))).mapError (fun _ => "declaration")
/-- The original complete finite inference driver is the only route to buildText. -/
def inferredText := LeanPoo.Functional.DeclarativeMetadata.inferDeclared 3
  (fun value => satisfies 8 textConstraints (textEnvironment value))
  [.bool, .symbol, .string] buildText
#guard match inferredText with
  | .ok (.unique .string, some (.atom .symbol, .atom .string)) => true
  | _ => false
/-- Publication retains all original substituted constraints and the complete
positional builder result. This does not certify the host macro expander. -/
theorem inferredText_sound (value artifact)
    (published : inferredText = .ok (.unique value, some artifact)) :
    (∀ a b, (a, b) ∈ textConstraints →
      Subtype (substitute (textEnvironment value) a) (substitute (textEnvironment value) b)) ∧
    buildText value = .ok artifact := by
  obtain ⟨_, valid, built⟩ := LeanPoo.Functional.DeclarativeMetadata.inferDeclared_unique
    3 (fun value => satisfies 8 textConstraints (textEnvironment value))
    [Atom.bool, Atom.symbol, Atom.string] buildText published
  exact ⟨fun a b member => satisfies_sound 8 textConstraints (textEnvironment value) valid member, built⟩
/-- An incomplete finite universe still refuses, even when a text candidate might
otherwise be unique. No accepted prefix can authorize the declaration builder. -/
example : LeanPoo.Functional.DeclarativeMetadata.inferDeclared 2
    (fun value => satisfies 8 textConstraints (textEnvironment value))
    [.bool, .symbol, .string] buildText = .error (.inl .exhausted) := by
  apply LeanPoo.Functional.DeclarativeMetadata.inferDeclared_exhausted
  decide
#print axioms atom_inclusion
#print axioms text_distinct
#print axioms inferredText_sound
/-- The range fixture binds Self to the result interval before inferring Super. -/
def smallRange : Ty := .integerRange ⟨some 0, some 10⟩
/-- Supplied inputs and the declared upper bound agree on this inclusive domain. -/
def largeRange : Ty := .integerRange ⟨some 0, some 100⟩
/-- The same residual assignment drives ordinary arguments and callback inputs. -/
def rangeEnvironment (super : Ty) : Nat → Ty := prefixEnvironment [smallRange] (fun _ => super)
/-- Declared Self <: Super <: [0,100] and complete supplied/result constraints
jointly select the actual interval rather than Integer or UInt. -/
def rangeConstraints : List (Expr × Expr) :=
  [(.var 0, .var 1), (.var 1, .ground largeRange), (.ground largeRange, .var 1),
   (.var 0, .ground smallRange),
   (.function [.var 0] [.var 1], .ground (.function [smallRange] [largeRange]))]
/-- Metadata uses the original Self/Super positional binder. -/
def signatureParameters : LeanPoo.Functional.Parameters.Template String Ty :=
  ⟨["Self", "Super"], fun _ => none⟩
/-- One complete signature builder handles numeric and Boolean prefixes; no
artifact is returned until both prefix and residual bindings finish. -/
def buildSignature (self super : Ty) : Except String (Ty × Ty) := do
  let staged ← (LeanPoo.Functional.Parameters.checkedSpecialize ".parameters" signatureParameters
    [self]).mapError (fun _ => "prefix")
  (LeanPoo.Functional.DeclarativeMetadata.specializeDeclared ".parameters" staged [super]
    (fun bound => (do
      if !bound.remaining.isEmpty then throw "residual parameters"
      let some self := bound.fields "Self" | throw "missing Self"
      let some super := bound.fields "Super" | throw "missing Super"
      pure (self, super) : Except String (Ty × Ty)))).mapError (fun _ => "declaration")
/-- Canonical metadata is projected before these three distinct Type candidates
enter the original complete declaration driver; aliases are not new candidates. -/
def inferredRange := LeanPoo.Functional.DeclarativeMetadata.inferDeclared 3
  (fun super => satisfies 12 rangeConstraints (rangeEnvironment super))
  [.atom .integer, .atom .uint, largeRange] (buildSignature smallRange)
#guard match inferredRange with
  | .ok (.unique (.integerRange ⟨some 0, some 100⟩), some
      (.integerRange ⟨some 0, some 10⟩, .integerRange ⟨some 0, some 100⟩)) => true
  | _ => false
#guard check 8 (.integerRange ⟨some 3, some 1⟩) (.atom .uint)
#guard !check 8 smallRange (.integerRange ⟨some 3, some 1⟩)
#guard !check 8 (.map smallRange (.atom .uint)) (.map largeRange (.atom .integer))
/-- Literal range metadata is not a position for Type-variable substitution. -/
example (env : Nat → Ty) (bounds : IntegerRange) :
    substitute env (.ground (.integerRange bounds)) = .integerRange bounds := by simp [substitute]
/-- Successful publication retains every original/call constraint and the exact
complete builder result; its range derivations preserve all integer observations. -/
theorem inferredRange_sound (super artifact)
    (published : inferredRange = .ok (.unique super, some artifact)) :
    (∀ a b, (a, b) ∈ rangeConstraints →
      Subtype (substitute (rangeEnvironment super) a) (substitute (rangeEnvironment super) b)) ∧
      (buildSignature smallRange) super = .ok artifact := by
  obtain ⟨_, valid, built⟩ := LeanPoo.Functional.DeclarativeMetadata.inferDeclared_unique 3
    (fun super => satisfies 12 rangeConstraints (rangeEnvironment super))
    [.atom .integer, .atom .uint, largeRange] (buildSignature smallRange) published
  exact ⟨fun a b member => satisfies_sound 12 rangeConstraints (rangeEnvironment super) valid member, built⟩
#print axioms IntegerRange.replacement
#print axioms IntegerRange.empty_refuses
#print axioms inferredRange_sound
/-- The finite target keeps its literal order and duplicates; range inclusion
uses integer membership, without changing candidate descriptor identity. -/
def rangeAlphabet : Ty := .integerEnum [10, 0, 9, 1, 8, 2, 7, 3, 6, 4, 5, 5]
/-- The prefix, observations and finite alphabet jointly determine Super. -/
def enumConstraints : List (Expr × Expr) :=
  [(.var 0, .var 1), (.var 1, .ground rangeAlphabet), (.ground smallRange, .var 1),
   (.function [.var 0] [.var 1], .ground (.function [smallRange] [smallRange]))]
/-- The original bounded driver and complete builder publish the range candidate,
not the finite alphabet descriptor that was used to constrain it. -/
def inferredEnum := LeanPoo.Functional.DeclarativeMetadata.inferDeclared 3
  (fun super => satisfies 12 enumConstraints (rangeEnvironment super))
  [.atom .integer, .atom .uint, smallRange] (buildSignature smallRange)
#guard match inferredEnum with
  | .ok (.unique (.integerRange ⟨some 0, some 10⟩), some
      (.integerRange ⟨some 0, some 10⟩, .integerRange ⟨some 0, some 10⟩)) => true
  | _ => false
#guard !check 8 smallRange (.integerEnum [0, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10])
#guard check 8 (.integerRange ⟨some 1, some 0⟩) (.integerEnum [])
#guard !check 8 (.integerRange ⟨none, some 0⟩) (.integerEnum [-1, 0])
#guard !check 8 (.map smallRange (.atom .uint)) (.map rangeAlphabet (.atom .uint))
/-- Successful finite-alphabet publication retains all substituted constraints
and the exact complete builder result; runtime interpretation remains explicit. -/
theorem inferredEnum_sound (super artifact)
    (published : inferredEnum = .ok (.unique super, some artifact)) :
    (∀ a b, (a, b) ∈ enumConstraints →
      Subtype (substitute (rangeEnvironment super) a) (substitute (rangeEnvironment super) b)) ∧
      (buildSignature smallRange) super = .ok artifact := by
  obtain ⟨_, valid, built⟩ := LeanPoo.Functional.DeclarativeMetadata.inferDeclared_unique 3
    (fun super => satisfies 12 enumConstraints (rangeEnvironment super))
    [.atom .integer, .atom .uint, smallRange] (buildSignature smallRange) published
  exact ⟨fun a b member => satisfies_sound 12 enumConstraints (rangeEnvironment super) valid member, built⟩
#print axioms IntegerRange.coverFrom_sound
#print axioms IntegerRange.coverFrom_complete
#print axioms IntegerRange.coveredBy_sound
#print axioms inferredEnum_sound
/-- Joint coverage retains the original nested order, including the middle Enum
that bridges otherwise disjoint low/high intervals. -/
def unionBound : Ty := .union [.integerRange ⟨some 7, some 10⟩,
  .union [.integerEnum [5, 6], .integerRange ⟨some 0, some 4⟩]]
/-- Prefix observations and this multi-branch bound constrain the same Super. -/
def unionConstraints : List (Expr × Expr) :=
  [(.var 0, .var 1), (.var 1, .ground unionBound), (.ground smallRange, .var 1),
   (.function [.var 0] [.var 1], .ground (.function [smallRange] [smallRange]))]
/-- Reuse the original complete declaration driver and positional builder. -/
def inferredUnion := LeanPoo.Functional.DeclarativeMetadata.inferDeclared 3
  (fun super => satisfies 12 unionConstraints (rangeEnvironment super))
  [.atom .integer, .atom .uint, smallRange] (buildSignature smallRange)
#guard match inferredUnion with
  | .ok (.unique (.integerRange ⟨some 0, some 10⟩), some
      (.integerRange ⟨some 0, some 10⟩, .integerRange ⟨some 0, some 10⟩)) => true
  | _ => false
#guard check 12 smallRange unionBound
#guard check 12 (.integerEnum [0, 5, 10]) unionBound
#guard !check 12 smallRange (.union [.integerRange ⟨some 0, some 4⟩, .integerRange ⟨some 6, some 10⟩])
#guard !check 12 smallRange (.union [smallRange, .function [.atom .uint] [.atom .uint]])
#guard !check 12 (.integerEnum []) (.union [smallRange, .function [.atom .uint] [.atom .uint]])
#guard !check 12 (.map smallRange (.atom .uint)) (.map unionBound (.atom .uint))
#guard !check 12 unionBound (.union [.union [.integerEnum [5, 6], .integerRange ⟨some 0, some 4⟩],
  .integerRange ⟨some 7, some 10⟩])
/-- Joint coverage authorizes every original/call constraint and the exact fully
bound artifact; it grants no permission to reorder branches or serialize values. -/
theorem inferredUnion_sound (super artifact)
    (published : inferredUnion = .ok (.unique super, some artifact)) :
    (∀ a b, (a, b) ∈ unionConstraints →
      Subtype (substitute (rangeEnvironment super) a) (substitute (rangeEnvironment super) b)) ∧
      (buildSignature smallRange) super = .ok artifact := by
  obtain ⟨_, valid, built⟩ := LeanPoo.Functional.DeclarativeMetadata.inferDeclared_unique 3
    (fun super => satisfies 12 unionConstraints (rangeEnvironment super))
    [.atom .integer, .atom .uint, smallRange] (buildSignature smallRange) published
  exact ⟨fun a b member => satisfies_sound 12 unionConstraints (rangeEnvironment super) valid member, built⟩
/-- An ordered infinite-tail cover retains the finite bridge and nested order. -/
def unboundedUnion : Ty := .union [.integerRange ⟨some 1, none⟩,
  .union [.integerEnum [0], .integerRange ⟨none, some (-1)⟩]]
/-- Inputs must admit every exact integer; Self and callback results stay bounded. -/
def unboundedConstraints : List (Expr × Expr) :=
  [(.var 0, .var 1), (.var 1, .ground unboundedUnion),
   (.ground (.integerRange IntegerRange.all), .var 1),
   (.function [.var 0] [.var 1], .ground (.function [smallRange] [.integerRange IntegerRange.all]))]
/-- The same complete specialization/declaration builder consumes the unique Type. -/
def inferredUnbounded := LeanPoo.Functional.DeclarativeMetadata.inferDeclared 3
  (fun super => satisfies 12 unboundedConstraints (rangeEnvironment super))
  [.atom .uint, .integerRange IntegerRange.unsigned, .integerRange IntegerRange.all] (buildSignature smallRange)
#guard match inferredUnbounded with
  | .ok (.unique (.integerRange ⟨none, none⟩), some
      (.integerRange ⟨some 0, some 10⟩, .integerRange ⟨none, none⟩)) => true
  | _ => false
#guard check 12 (.integerRange IntegerRange.all) unboundedUnion
#guard check 12 (.integerRange ⟨some (-2), none⟩)
  (.union [.integerEnum [-2, -1], .integerRange IntegerRange.unsigned])
#guard check 12 (.integerRange ⟨none, some 2⟩)
  (.union [.integerRange ⟨none, some 0⟩, .integerEnum [2, 1]])
#guard !check 12 (.integerRange IntegerRange.all)
  (.union [.integerRange ⟨none, some (-1)⟩, .integerRange ⟨some 1, none⟩])
#guard !check 12 (.integerRange IntegerRange.all)
  (.union [.integerRange ⟨none, some 0⟩, .integerEnum [1, 2]])
#guard !check 12 (.integerRange IntegerRange.all)
  (.union [unboundedUnion, .function [.atom .uint] [.atom .uint]])
#guard !check 0 (.integerRange IntegerRange.all) unboundedUnion
/-- Every exact integer is covered, without a sampled boundary or finite cutoff. -/
theorem unboundedUnion_accepts (value : Int) : integerAccepts 12 unboundedUnion value = true := by
  obtain ⟨_, _, covered⟩ := rangeUnionCheck_sound 12 IntegerRange.all
    [.integerRange ⟨some 1, none⟩, .union [.integerEnum [0], .integerRange ⟨none, some (-1)⟩]] (by decide)
  exact covered value (by simp [IntegerRange.Contains, IntegerRange.all])
/-- The complete declaration preserves all constraints and the exact artifact;
this is type replacement, not a proof of host keyword parsing or GC behavior. -/
theorem inferredUnbounded_sound (super artifact)
    (published : inferredUnbounded = .ok (.unique super, some artifact)) :
    (∀ a b, (a, b) ∈ unboundedConstraints →
      Subtype (substitute (rangeEnvironment super) a) (substitute (rangeEnvironment super) b)) ∧
      (buildSignature smallRange) super = .ok artifact := by
  obtain ⟨_, valid, built⟩ := LeanPoo.Functional.DeclarativeMetadata.inferDeclared_unique 3
    (fun super => satisfies 12 unboundedConstraints (rangeEnvironment super))
    [.atom .uint, .integerRange IntegerRange.unsigned, .integerRange IntegerRange.all] (buildSignature smallRange) published
  exact ⟨fun a b member => satisfies_sound 12 unboundedConstraints (rangeEnvironment super) valid member, built⟩
/-- UInt's ordered cover separates zero from the infinite strictly positive tail. -/
def unsignedUnion : Ty := .union [.integerRange ⟨some 1, none⟩, .integerEnum [0]]
/-- Ordinary observations and callback variance constrain the same atomic input
parameter; the finite Self result and complete specialization builder are shared. -/
def numericUnionConstraints (source target : Ty) : List (Expr × Expr) :=
  [(.var 0, .var 1), (.var 1, .ground target), (.ground source, .var 1),
   (.function [.var 0] [.var 1], .ground (.function [smallRange] [source]))]
/-- The existing declaration driver chooses the actual atomic descriptor; no
range alias is manufactured as an additional candidate or substituted result. -/
def inferredNumericUnion (source target : Ty) := LeanPoo.Functional.DeclarativeMetadata.inferDeclared 2
  (fun super => satisfies 12 (numericUnionConstraints source target) (rangeEnvironment super))
  [.atom .integer, .atom .uint] (buildSignature smallRange)
#guard match inferredNumericUnion (.atom .integer) unboundedUnion with
  | .ok (.unique (.atom .integer), some (.integerRange ⟨some 0, some 10⟩, .atom .integer)) => true
  | _ => false
#guard match inferredNumericUnion (.atom .uint) unsignedUnion with
  | .ok (.unique (.atom .uint), some (.integerRange ⟨some 0, some 10⟩, .atom .uint)) => true
  | _ => false
#guard check 12 (.atom .integer) unboundedUnion
#guard check 12 (.atom .uint) unsignedUnion
#guard !check 12 (.atom .integer) unsignedUnion
#guard !check 12 (.atom .uint) (.union [.integerRange ⟨some 1, none⟩])
#guard !check 12 (.atom .integer) (.union [.integerEnum [-1, 0, 1]])
#guard !check 12 (.atom .uint) (.union [unsignedUnion, .function [.atom .uint] [.atom .uint]])
#guard !check 12 (.map (.atom .uint) smallRange) (.map unsignedUnion smallRange)
#guard check 12 (.pair (.atom .integer) (.map (.atom .uint) (.atom .uint)))
  (.pair unboundedUnion (.map (.atom .uint) unsignedUnion))
#guard check 12 (.function [.atom .uint] [unboundedUnion])
  (.function [unsignedUnion] [.atom .integer])
/-- All integers and nonnegative integers use the same universal coverage theorem. -/
theorem atomicUnion_accepts (value : Int) :
    integerAccepts 12 unboundedUnion value = true ∧
      (0 ≤ value → integerAccepts 12 unsignedUnion value = true) := by
  constructor
  · exact numericUnion_sound (.atom .integer) IntegerRange.all 12 _ rfl (by decide) value rfl
  · intro nonnegative
    exact numericUnion_sound (.atom .uint) IntegerRange.unsigned 12 _ rfl (by decide) value
      (by simpa [integerAccepts] using nonnegative)
/-- The same complete builder retains every inferred constraint and exact atomic
Type. Rich host calling syntax remains covered by separate Scheme controls. -/
theorem inferredNumericUnion_sound (source target super artifact)
    (published : inferredNumericUnion source target = .ok (.unique super, some artifact)) :
    (∀ a b, (a, b) ∈ numericUnionConstraints source target →
      Subtype (substitute (rangeEnvironment super) a) (substitute (rangeEnvironment super) b)) ∧
      (buildSignature smallRange) super = .ok artifact := by
  obtain ⟨_, valid, built⟩ := LeanPoo.Functional.DeclarativeMetadata.inferDeclared_unique 2
    (fun super => satisfies 12 (numericUnionConstraints source target) (rangeEnvironment super))
    [.atom .integer, .atom .uint] (buildSignature smallRange) published
  exact ⟨fun a b member => satisfies_sound 12 _ (rangeEnvironment super) valid member, built⟩
/-- Exactly true and Enum false jointly cover Bool, preserving nested order
and the deliberately duplicated true branch in the runtime service. -/
def booleanUnion : Ty := .union [.booleanEnum [true], .union [.booleanEnum [false], .booleanEnum [true]]]
/-- The Boolean prefix and callback result remain fixed while Super is inferred. -/
def booleanEnvironment (super : Ty) : Nat → Ty := prefixEnvironment [.atom .bool] (fun _ => super)
/-- The complete call and declared upper bound constrain the same Super parameter. -/
def booleanConstraints : List (Expr × Expr) :=
  [(.var 0, .var 1), (.var 1, .ground booleanUnion), (.ground (.atom .bool), .var 1),
   (.function [.var 0] [.var 1], .ground (.function [.atom .bool] [.atom .bool]))]
/-- Reuse the original complete declaration driver and the shared signature binder. -/
def inferredBoolean := LeanPoo.Functional.DeclarativeMetadata.inferDeclared 3
  (fun super => satisfies 12 booleanConstraints (booleanEnvironment super))
  [.atom .integer, .atom .uint, .atom .bool] (buildSignature (.atom .bool))
#guard match inferredBoolean with
  | .ok (.unique (.atom .bool), some (.atom .bool, .atom .bool)) => true
  | _ => false
#guard check 12 (.atom .bool) booleanUnion
#guard check 12 (.atom .bool) (.booleanEnum [false, true, false])
#guard !check 12 (.atom .bool) (.union [.booleanEnum [true]])
#guard !check 12 (.atom .bool) (.union [.booleanEnum [false, false]])
#guard !check 12 (.atom .bool) (.union [.atom .integer, .atom .uint])
#guard !check 12 (.atom .bool) (.union [booleanUnion, .function [.atom .bool] [.atom .bool]])
#guard !check 12 (.map (.atom .bool) (.atom .uint)) (.map booleanUnion (.atom .uint))
#guard check 12 (.pair (.atom .bool) (.map (.atom .uint) (.atom .bool)))
  (.pair booleanUnion (.map (.atom .uint) booleanUnion))
#guard check 12 (.function [.atom .bool] [booleanUnion])
  (.function [booleanUnion] [.atom .bool])
#guard !check 12 booleanUnion (.union [.union [.booleanEnum [false], .booleanEnum [true]], .booleanEnum [true]])
/-- Both inhabitants are covered exhaustively; false cannot disappear as absence. -/
theorem booleanUnion_accepts : ∀ value : Bool, booleanAccepts 12 booleanUnion value = true :=
  booleanCheck_total 12 booleanUnion (by decide)
/-- Complete Boolean specialization retains every constraint and the exact Bool
artifact. Host keyword parsing and user callback behavior remain explicit bounds. -/
theorem inferredBoolean_sound (super artifact)
    (published : inferredBoolean = .ok (.unique super, some artifact)) :
    (∀ a b, (a, b) ∈ booleanConstraints →
      Subtype (substitute (booleanEnvironment super) a) (substitute (booleanEnvironment super) b)) ∧
      buildSignature (.atom .bool) super = .ok artifact := by
  obtain ⟨_, valid, built⟩ := LeanPoo.Functional.DeclarativeMetadata.inferDeclared_unique 3
    (fun super => satisfies 12 booleanConstraints (booleanEnvironment super))
    [.atom .integer, .atom .uint, .atom .bool] (buildSignature (.atom .bool)) published
  exact ⟨fun a b member => satisfies_sound 12 _ (booleanEnvironment super) valid member, built⟩
/-- Finite Symbol/Keyword alternatives precede the complete intrinsic family;
extra Bool coverage does not identify different source families. -/
def scalarBound (family : Atom) : Ty := .union [.scalarEnum .symbol [1], .scalarEnum .keyword [2],
  .union [.atom family, .atom .bool]]
/-- The same prefix binder handles String, Symbol and Keyword without conversion. -/
def scalarEnvironment (family super : Ty) : Nat → Ty := prefixEnvironment [family] (fun _ => super)
/-- Supplied inputs, callback variance and declared bounds constrain one parameter. -/
def scalarConstraints (family : Atom) : List (Expr × Expr) :=
  [(.var 0, .var 1), (.var 1, .ground (scalarBound family)), (.ground (.atom family), .var 1),
   (.function [.var 0] [.var 1], .ground (.function [.atom family] [.atom family]))]
/-- Complete declaration inference uses the existing signature builder for all
three intrinsic families; candidate identity and order remain descriptor data. -/
def inferredScalar (family : Atom) := LeanPoo.Functional.DeclarativeMetadata.inferDeclared 3
  (fun super => satisfies 12 (scalarConstraints family) (scalarEnvironment (.atom family) super))
  [.atom .string, .atom .symbol, .atom .keyword] (buildSignature (.atom family))
#guard match inferredScalar .string with
  | .ok (.unique (.atom .string), some (.atom .string, .atom .string)) => true | _ => false
#guard match inferredScalar .symbol with
  | .ok (.unique (.atom .symbol), some (.atom .symbol, .atom .symbol)) => true | _ => false
#guard match inferredScalar .keyword with
  | .ok (.unique (.atom .keyword), some (.atom .keyword, .atom .keyword)) => true | _ => false
#guard check 12 (.atom .keyword) (scalarBound .keyword)
#guard !check 12 (.atom .symbol) (.union [.atom .keyword])
#guard !check 12 (.atom .string) (.union [.scalarEnum .symbol [0, 1], .scalarEnum .keyword [2]])
#guard !check 12 (.atom .keyword) (.union [.scalarEnum .keyword [0, 1, 2]])
#guard !check 12 (.atom .symbol) (.union [.atom .symbol, .function [.atom .symbol] [.atom .symbol]])
#guard !check 12 (.map (.atom .keyword) (.atom .bool)) (.map (scalarBound .keyword) (.atom .bool))
#guard check 12 (.function [.atom .symbol] [scalarBound .keyword])
  (.function [scalarBound .symbol] [.atom .keyword])
/-- Every member of a classified family reaches an original branch; literal IDs
are abstract labels, not a proof of host parsing or String/Symbol conversion. -/
theorem scalarBound_accepts (family : Atom) (classified : infiniteScalar family = true) :
    ∀ value, scalarAccepts 12 family (scalarBound family) value = true := by
  intro value
  cases family <;> simp only [infiniteScalar] at classified
  all_goals try contradiction
  all_goals exact scalarWhole_sound _ _ _ _ (by decide)
/-- No finite list of literal labels covers an infinite source; the cutoff gives
an explicit missing member instead of a sampled negative observation. -/
theorem finiteScalar_missing (family : Atom) (values : List Nat) :
    scalarAccepts 12 family (.union [.scalarEnum family values])
      (scalarCutoff 12 (.union [.scalarEnum family values]) + 1) = false := by
  rw [scalarFresh _ _ _ _ (by omega)]
  rfl
/-- Publication retains every call/declaration constraint and complete artifact.
Host keyword transport is checked independently by Scheme's released decoder. -/
theorem inferredScalar_sound (family super artifact)
    (published : inferredScalar family = .ok (.unique super, some artifact)) :
    (∀ a b, (a, b) ∈ scalarConstraints family →
      Subtype (substitute (scalarEnvironment (.atom family) super) a)
        (substitute (scalarEnvironment (.atom family) super) b)) ∧
      buildSignature (.atom family) super = .ok artifact := by
  obtain ⟨_, valid, built⟩ := LeanPoo.Functional.DeclarativeMetadata.inferDeclared_unique 3
    (fun super => satisfies 12 (scalarConstraints family) (scalarEnvironment (.atom family) super))
    [.atom .string, .atom .symbol, .atom .keyword] (buildSignature (.atom family)) published
  exact ⟨fun a b member => satisfies_sound 12 _ _ valid member, built⟩
/-- The disabled capability keeps its impossible mandatory input descriptor.
The two Sum payloads mirror the Scheme callback fixture after literal tag IDs. -/
def deadCallbackInput : Ty := .pair
  (.sum [0, 1] [.tuple [.integerEnum []], .union [.integerEnum []]]) (.atom .uint)
/-- Prefix binding fixes the ordinary service value independently of the callback. -/
def emptyEnvironment (dead : Ty) : Nat → Ty := prefixEnvironment [.atom .uint] (fun _ => dead)
/-- A declared bound rejects inhabited integer candidates without widening to top. -/
def emptyConstraints : List (Expr × Expr) := [(.var 1, .ground (.atom .string))]
/-- The existing all-or-error declaration builder receives the original candidate. -/
def inferredEmpty := LeanPoo.Functional.DeclarativeMetadata.inferDeclared 2
  (fun dead => satisfies 12 emptyConstraints (emptyEnvironment dead))
  [.atom .uint, deadCallbackInput] (buildSignature (.atom .uint))
#guard emptyCheck 12 deadCallbackInput
#guard check 12 deadCallbackInput (.atom .string)
#guard check 12 (.function [.atom .uint] [.atom .string])
  (.function [.atom .integer] [deadCallbackInput])
#guard !emptyCheck 12 (.list (.integerEnum []))
#guard !emptyCheck 12 (.map (.atom .uint) (.integerEnum []))
#guard !emptyCheck 12 (.maybe (.integerEnum []))
#guard !emptyCheck 12 (.orFalse (.integerEnum []))
#guard !check 12 (.union []) (.union [.atom .uint])
#guard !check 12 (.sum [0] [.integerEnum []]) (.sum [1] [.integerEnum []])
#guard match inferredEmpty with
  | .ok (.unique dead, some (_, bound)) => emptyCheck 12 dead && same 12 bound dead
  | _ => false
/-- No observation can reach a disabled callback under the required host shape
laws; this does not prove that a Scheme procedure terminates if called directly. -/
theorem deadCallback_refuses (accepts : Ty → Value → Prop) (laws : EmptyLaws accepts) :
    ∀ value, ¬ accepts deadCallbackInput value :=
  (emptyCheck_sound 12 deadCallbackInput (by decide)).refuses laws
/-- Unique inference preserves every bound and exact artifact through the same
completed declaration protocol used by inhabited service signatures. -/
theorem inferredEmpty_sound (dead artifact)
    (published : inferredEmpty = .ok (.unique dead, some artifact)) :
    (∀ a b, (a, b) ∈ emptyConstraints →
      Subtype (substitute (emptyEnvironment dead) a) (substitute (emptyEnvironment dead) b)) ∧
      buildSignature (.atom .uint) dead = .ok artifact := by
  obtain ⟨_, valid, built⟩ := LeanPoo.Functional.DeclarativeMetadata.inferDeclared_unique 2
    (fun dead => satisfies 12 emptyConstraints (emptyEnvironment dead))
    [.atom .uint, deadCallbackInput] (buildSignature (.atom .uint)) published
  exact ⟨fun a b member => satisfies_sound 12 _ _ valid member, built⟩
/-- Each service keeps a literal prefix and complete original descriptor artifact.
These mirror Null/Unit, signed-input/unsigned-output and byte-buffer publication. -/
def descriptorServices :=
  [(Intrinsic.null, Intrinsic.null, [Intrinsic.unit, .null]),
   (Intrinsic.unit, Intrinsic.unit, [Intrinsic.null, .unit]),
   (Intrinsic.signed 9, Intrinsic.unsigned 8, [Intrinsic.unsigned 8, .unsigned 9]),
   (Intrinsic.bytes none, Intrinsic.bytes (some 32), [Intrinsic.bytes (some 16), .bytes (some 32)])]
#guard descriptorServices.all fun (input, expected, candidates) =>
  match inferIntrinsic input expected candidates with
  | .ok (.unique output, some (boundInput, boundOutput)) =>
      decide (boundInput = input) && decide (boundOutput = output) && intrinsicCheck output expected
  | _ => false
#guard intrinsicCheck (.unsigned 0) (.unsigned 1)
#guard intrinsicCheck (.unsigned 8) (.signed 9)
#guard !intrinsicCheck (.signed 8) (.unsigned 8)
#guard !intrinsicCheck (.bytes (some 0)) .null
#guard !intrinsicCheck (.bytes (some 1)) (.unsigned 8)
#guard intrinsicCheck .bytes32 (.bytes none)
#guard intrinsicCheck .uint256 (.unsigned 256)
#guard intrinsicCheck .jsInt (.signed 54)
#guard !(Intrinsic.signed 0).admitted
#guard !(Intrinsic.unsigned 4097).admitted
#guard !(Intrinsic.bytes (some 65537)).admitted
/-- The two excluded signed endpoints are concrete counterexamples, including
negative overflow. Acceptance uses exact integer order, not bit truncation. -/
example : (Intrinsic.signed 8).Accepts (.integer (-128)) ∧
    ¬ (Intrinsic.signed 8).Accepts (.integer (-129)) ∧
    ¬ (Intrinsic.signed 8).Accepts (.integer 128) := by
  simp [Intrinsic.Accepts, IntrinsicValue.observation, Intrinsic.carrier,
    Intrinsic.range, IntegerRange.forSigned, IntegerRange.Contains]
/-- Runtime aliases can share interval meaning without losing artifact identity. -/
example : Intrinsic.uint256 ≠ Intrinsic.unsigned 256 ∧
    intrinsicCheck .uint256 (.unsigned 256) = true := by decide
#print axioms intrinsicCheck_sound
#print axioms intrinsicCheck_carrier
#print axioms intrinsicCheck_admitted
#print axioms numericView_exact
#print axioms metadataUnits_bounded
#print axioms inferIntrinsic_sound
#print axioms emptyCheck_sound
#print axioms EmptyType.refuses
#print axioms requiredField_refuses
#print axioms deadCallback_refuses
#print axioms inferredEmpty_sound
#print axioms scalarWhole_iff
#print axioms scalarCheck_sound
#print axioms scalarCheck_complete
#print axioms scalarUnion_validate
#print axioms finiteScalar_missing
#print axioms inferredScalar_sound
#print axioms booleanUnion_validate
#print axioms booleanCheck_sound
#print axioms booleanCheck_total
#print axioms booleanUnion_accepts
#print axioms inferredBoolean_sound
#print axioms numericBounds_contains
#print axioms numericUnion_sound
#print axioms atomicUnion_accepts
#print axioms inferredNumericUnion_sound
#print axioms unboundedUnion_accepts
#print axioms inferredUnbounded_sound
#print axioms LeanPoo.Functional.VariantValidation.coversInterval_sound
#print axioms LeanPoo.Functional.VariantValidation.union_identity
#print axioms LeanPoo.Functional.VariantValidation.union_finite_identity
#print axioms numericPieces_sound
#print axioms rangeUnionCheck_sound
#print axioms enumUnionCheck_sound
#print axioms inferredUnion_sound
end Examples.PrototypeTypes
