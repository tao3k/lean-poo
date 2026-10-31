import LeanPoo.Functional.PrototypeTypeCoverage

/-! Checked replacement, structural variance and finite prototype inference.
This advances the type-protocol future work, with explicit semantic premises. -/
namespace LeanPoo.Functional.PrototypeTypes

/-- A pointwise relation checks exact length; zip cannot silently drop arguments. -/
def all₂ (test : Ty → Ty → Bool) : List Ty → List Ty → Bool
  | [], [] => true
  | a :: as, b :: bs => test a b && all₂ test as bs
  | _, _ => false

/-- Exact finite syntax identity is stricter than mutual derivability. It keeps
Map key normalization and ordered Union selection fixed, including nested arrows. -/
def same : Nat → Ty → Ty → Bool
  | 0, _, _ => false
  | fuel + 1, a, b => match a, b with
    | .top, .top => true
    | .atom a, .atom b => decide (a = b)
    | .integerRange a, .integerRange b => decide (a = b)
    | .integerEnum a, .integerEnum b | .booleanEnum a, .booleanEnum b => decide (a = b)
    | .scalarEnum name as, .scalarEnum name' bs => decide (name = name') && decide (as = bs)
    | .list a, .list b | .maybe a, .maybe b | .orFalse a, .orFalse b => same fuel a b
    | .tuple as, .tuple bs | .union as, .union bs => all₂ (same fuel) as bs
    | .pair a b, .pair c d | .map a b, .map c d => same fuel a c && same fuel b d
    | .sum tags as, .sum tags' bs => decide (tags = tags') && all₂ (same fuel) as bs
    | .function outs ins, .function outs' ins' =>
        all₂ (same fuel) outs outs' && all₂ (same fuel) ins ins'
    | _, _ => false

/-- Exact list identity cannot lose, reorder or merge a branch. -/
theorem all₂_equal (test : Ty → Ty → Bool) (sound : ∀ a b, test a b = true → a = b)
    (as bs : List Ty) (accepted : all₂ test as bs = true) : as = bs := by
  induction as generalizing bs with
  | nil => cases bs <;> simp_all [all₂]
  | cons a as ih =>
    cases bs with
    | nil => simp [all₂] at accepted
    | cons b bs =>
      simp only [all₂, Bool.and_eq_true] at accepted
      have both := accepted
      exact congr (congrArg List.cons (sound a b both.1)) (ih bs both.2)

/-- Successful identity checks imply propositional equality, not a sampled match. -/
theorem same_sound (fuel : Nat) (a b : Ty) (accepted : same fuel a b = true) : a = b := by
  induction fuel generalizing a b with
  | zero => simp [same] at accepted
  | succ fuel ih =>
    cases a <;> cases b <;> simp only [same] at accepted
    all_goals try contradiction
    all_goals try rfl
    all_goals first
      | exact congrArg Ty.atom (of_decide_eq_true accepted)
      | exact congrArg Ty.integerRange (of_decide_eq_true accepted)
      | exact congrArg Ty.integerEnum (of_decide_eq_true accepted)
      | exact congrArg Ty.booleanEnum (of_decide_eq_true accepted)
      | simp only [Bool.and_eq_true] at accepted
        exact congr (congrArg Ty.scalarEnum (of_decide_eq_true accepted.1)) (of_decide_eq_true accepted.2)
      | exact congrArg Ty.list (ih _ _ accepted)
      | exact congrArg Ty.maybe (ih _ _ accepted)
      | exact congrArg Ty.orFalse (ih _ _ accepted)
      | exact congrArg Ty.tuple (all₂_equal _ ih _ _ accepted)
      | exact congrArg Ty.union (all₂_equal _ ih _ _ accepted)
      | simp only [Bool.and_eq_true] at accepted
        have both := accepted
        first
        | exact congr (congrArg Ty.pair (ih _ _ both.1)) (ih _ _ both.2)
        | exact congr (congrArg Ty.map (ih _ _ both.1)) (ih _ _ both.2)
        | exact congr (congrArg Ty.function (all₂_equal _ ih _ _ both.1)) (all₂_equal _ ih _ _ both.2)
        | exact congr (congrArg Ty.sum (of_decide_eq_true both.1)) (all₂_equal _ ih _ _ both.2)

/-- Exact positional lifting of a relation, including empty argument lists. -/
inductive RelList (relation : Ty → Ty → Prop) : List Ty → List Ty → Prop where
  | nil : RelList relation [] []
  | cons : relation a b → RelList relation as bs → RelList relation (a :: as) (b :: bs)

/-- Declarative replacement, independent of prototype ancestry or samples. -/
inductive Subtype : Ty → Ty → Prop where
  | empty : emptySource fuel a = true → Subtype a b
  | refl (a) : Subtype a a
  | top (a) : Subtype a .top
  | uint : Subtype (.atom .uint) (.atom .integer)
  | numeric : numericBounds a = some source → numericBounds b = some target →
      source.includes target = true → Subtype a b
  | rangeEnum : range.coveredBy values = true → Subtype (.integerRange range) (.integerEnum values)
  | numericUnion : numericBounds source = some range → rangeUnionCheck fuel range branches = true →
      Subtype source (.union branches)
  | scalarUnion : scalarCheck fuel family (.union branches) = true →
      Subtype (.atom family) (.union branches)
  | boolean : booleanValues source = some values → booleanCheck fuel values target = true →
      Subtype source target
  | enumUnion : enumUnionCheck fuel values branches = true → Subtype (.integerEnum values) (.union branches)
  | sourceUnion : (∀ branch ∈ branches, Subtype branch target) → Subtype (.union branches) target
  | list : Subtype a b → Subtype (.list a) (.list b)
  | maybe : Subtype a b → Subtype (.maybe a) (.maybe b)
  | orFalse : Subtype a b → Subtype (.orFalse a) (.orFalse b)
  | tuple : RelList Subtype as bs → Subtype (.tuple as) (.tuple bs)
  | pair : Subtype a c → Subtype b d → Subtype (.pair a b) (.pair c d)
  | map : Subtype a b → Subtype (.map key a) (.map key b)
  | emptyMap : emptyCheck fuel key = true ∨ emptyCheck fuel value = true →
      Subtype (.map key value) (.map key' value')
  | sum : RelList Subtype as bs → Subtype (.sum tags as) (.sum tags bs)
  | function : RelList Subtype outs outs' → RelList Subtype ins' ins →
      Subtype (.function outs ins) (.function outs' ins')

/-- Finite derivability checker; exhaustion is separate from a negative result in
Scheme. Fuel here bounds derivation unfolding, not host GC or callback costs. -/
def check : Nat → Ty → Ty → Bool
  | 0, _, _ => false
  | fuel + 1, a, b =>
    (match a, b with
    | _, .top => true
    | .atom a, .atom b => decide (a = b) || decide (a = .uint ∧ b = .integer)
    | .integerRange source, .integerRange target => source.includes target
    | .integerRange source, .integerEnum values => source.coveredBy values
    | .integerEnum values, .integerEnum target => decide (values = target)
    | .scalarEnum family values, .scalarEnum family' target =>
        decide (family = family') && decide (values = target)
    | .integerRange source, .union branches => rangeUnionCheck fuel source branches
    | .atom .bool, .union branches => booleanCheck fuel [false, true] (.union branches)
    | .atom source, .union branches =>
        if infiniteScalar source then scalarCheck fuel source (.union branches)
        else match numericBounds (.atom source) with
          | some range => rangeUnionCheck fuel range branches
          | none => false
    | .atom .bool, .booleanEnum values => booleanCheck fuel [false, true] (.booleanEnum values)
    | .booleanEnum values, .atom .bool => booleanCheck fuel values (.atom .bool)
    | .booleanEnum values, .booleanEnum target => booleanCheck fuel values (.booleanEnum target)
    | .booleanEnum values, .union branches => booleanCheck fuel values (.union branches)
    | .integerEnum values, .union branches => enumUnionCheck fuel values branches
    | .integerRange source, .atom .integer => source.includes IntegerRange.all
    | .integerRange source, .atom .uint => source.includes IntegerRange.unsigned
    | .atom .integer, .integerRange target => IntegerRange.all.includes target
    | .atom .uint, .integerRange target => IntegerRange.unsigned.includes target
    | .list a, .list b | .maybe a, .maybe b | .orFalse a, .orFalse b => check fuel a b
    | .tuple as, .tuple bs => all₂ (check fuel) as bs
    | .pair a b, .pair c d => check fuel a c && check fuel b d
    | .map k a, .map k' b => (same fuel k k' && check fuel a b) || emptyCheck fuel k || emptyCheck fuel a
    | .sum tags as, .sum tags' bs => decide (tags = tags') && all₂ (check fuel) as bs
    | .union as, .union bs => all₂ (same fuel) as bs
    | .union branches, target => branches.all (fun branch => check fuel branch target)
    | .function outs ins, .function outs' ins' =>
        all₂ (check fuel) outs outs' && all₂ (check fuel) ins' ins
    | _, _ => false) || (emptySource (fuel + 1) a && emptyTarget (fuel + 1) b)

/-- Callable alternatives cover one arrow exactly when every original branch
passes the same bounded arrow judgment. Empty alternatives are vacuous, not a
procedure witness; zero fuel still refuses. Ordered Union targets stay separate. -/
theorem check_union_function (fuel : Nat) (branches outputs inputs : List Ty) :
    check (fuel + 1) (.union branches) (.function outputs inputs) =
      branches.all (fun branch => check fuel branch (.function outputs inputs)) := by
  simp only [check, emptySource, Bool.false_and, Bool.or_false]

/-- Lift a Boolean comparison's soundness through exact positional matching. -/
theorem all₂_sound (test : Ty → Ty → Bool) (sound : ∀ a b, test a b = true → Subtype a b)
    (as bs : List Ty) (accepted : all₂ test as bs = true) : RelList Subtype as bs := by
  induction as generalizing bs with
  | nil => cases bs with
    | nil => exact .nil
    | cons b bs => simp [all₂] at accepted
  | cons a as ih =>
    cases bs with
    | nil => simp [all₂] at accepted
    | cons b bs =>
      have both : test a b = true ∧ all₂ test as bs = true := by simpa only [all₂, Bool.and_eq_true] using accepted
      obtain ⟨head, tail⟩ := both
      exact .cons (sound a b head) (ih bs tail)

/-- Every checked inclusion has a declarative derivation, including higher-order
contravariance and multiple-value arity. No relation is inferred from inheritance. -/
theorem check_sound (fuel : Nat) (a b : Ty) (accepted : check fuel a b = true) : Subtype a b := by
  induction fuel generalizing a b with
  | zero => simp [check] at accepted
  | succ fuel ih =>
    simp only [check, Bool.or_eq_true] at accepted
    rcases accepted with accepted | empty
    · cases a <;> cases b <;> try simp only at accepted
      all_goals try { contradiction }
      all_goals try { exact .top _ }
      all_goals try { exact .list (ih _ _ accepted) }
      all_goals try { exact .maybe (ih _ _ accepted) }
      all_goals try { exact .orFalse (ih _ _ accepted) }
      all_goals try { exact .tuple (all₂_sound _ ih _ _ accepted) }
      all_goals try {
        apply Subtype.sourceUnion
        intro branch member
        exact ih _ _ (List.all_eq_true.mp accepted branch member) }
      case integerRange.integerRange source target => exact .numeric rfl rfl accepted
      case integerRange.integerEnum source values => exact .rangeEnum accepted
      case integerEnum.integerEnum values target =>
        have equal := of_decide_eq_true accepted
        subst target
        exact .refl _
      case scalarEnum.scalarEnum family values family' target =>
        simp only [Bool.and_eq_true] at accepted
        have names : family = family' := of_decide_eq_true accepted.1
        have values : values = target := of_decide_eq_true accepted.2
        subst family'; subst target
        exact .refl _
      case integerRange.union source branches => exact .numericUnion rfl accepted
      case atom.union source branches =>
        cases source <;> first | contradiction | exact .boolean rfl accepted | exact .numericUnion rfl accepted | exact .scalarUnion accepted
      case atom.booleanEnum source values =>
        cases source <;> first | contradiction | exact .boolean rfl accepted
      case booleanEnum.atom values target =>
        cases target <;> first | contradiction | exact .boolean rfl accepted
      case booleanEnum.booleanEnum values target => exact .boolean rfl accepted
      case booleanEnum.union values branches => exact .boolean rfl accepted
      case integerEnum.union values branches => exact .enumUnion accepted
      case integerRange.atom source target =>
        cases target
        all_goals first | contradiction | exact .numeric rfl rfl accepted
      case atom.integerRange source target =>
        cases source
        all_goals first | contradiction | exact .numeric rfl rfl accepted
      case pair.pair a b c d =>
        simp only [Bool.and_eq_true] at accepted
        have both := accepted
        exact .pair (ih _ _ both.1) (ih _ _ both.2)
      case map.map key a key' b =>
        simp only [Bool.or_eq_true, Bool.and_eq_true] at accepted
        rcases accepted with covered | emptyValue
        · rcases covered with ordinary | emptyKey
          · obtain ⟨keys, values⟩ := ordinary
            have equal := same_sound _ _ _ keys
            subst key'
            exact .map (ih _ _ values)
          · exact .emptyMap (Or.inl emptyKey)
        · exact .emptyMap (Or.inr emptyValue)
      case sum.sum tags as tags' bs =>
        simp only [Bool.and_eq_true] at accepted
        have both := accepted
        have equal : tags = tags' := of_decide_eq_true both.1
        subst tags'
        exact .sum (all₂_sound _ ih _ _ both.2)
      case union.union as bs =>
        have equal := all₂_equal _ (same_sound fuel) _ _ accepted
        subst bs
        exact .refl _
      case function.function outs ins outs' ins' =>
        have both : all₂ (check fuel) outs outs' = true ∧ all₂ (check fuel) ins' ins = true := by
          simpa only [Bool.and_eq_true] using accepted
        exact .function (all₂_sound _ ih _ _ both.1) (all₂_sound _ ih _ _ both.2)
      case atom.atom a b =>
        cases a <;> cases b <;> simp_all
        all_goals first | exact .refl _ | exact .uint
    · simp only [Bool.and_eq_true] at empty
      exact .empty empty.1

/-- Closed scalar derivations admit only identical families or UInt <: Integer.
String/Symbol conversion APIs cannot silently become a replacement permission. -/
theorem atom_inclusion (fuel : Nat) (source target : Atom)
    (accepted : check fuel (.atom source) (.atom target) = true) :
    source = target ∨ (source = .uint ∧ target = .integer) := by
  cases fuel with
  | zero => simp [check] at accepted
  | succ fuel =>
    simp only [check, emptySource, emptyCheck, Bool.false_and, Bool.or_false, Bool.or_eq_true] at accepted
    rcases accepted with same | numeric
    · exact .inl (of_decide_eq_true same)
    · exact .inr (of_decide_eq_true numeric)

/-- Runtime text/symbol conversion does not identify the source and target Types. -/
theorem text_distinct (fuel : Nat) :
    check fuel (.atom .string) (.atom .symbol) = false ∧
      check fuel (.atom .symbol) (.atom .string) = false := by
  cases fuel <;> simp [check, emptySource, emptyCheck]

/-- A changed Map key requires positive evidence that no source entry can exist.
The source Map itself is inhabited by the empty table, never an empty Type. -/
theorem map_key_or_empty (fuel : Nat) (key key' value value' : Ty)
    (accepted : check fuel (.map key value) (.map key' value') = true) :
    key = key' ∨ EmptyType key ∨ EmptyType value := by
  cases fuel with
  | zero => simp [check] at accepted
  | succ fuel =>
    have branches : (same fuel key key' && check fuel value value') = true ∨
        emptyCheck fuel key = true ∨ emptyCheck fuel value = true := by
      simpa [check, emptySource, emptyCheck, or_assoc] using accepted
    rcases branches with ordinary | emptyKey | emptyValue
    · have both : same fuel key key' = true ∧ check fuel value value' = true := by
        simpa only [Bool.and_eq_true] using ordinary
      exact Or.inl (same_sound _ _ _ both.1)
    · exact Or.inr (Or.inl (emptyCheck_sound _ _ emptyKey))
    · exact Or.inr (Or.inr (emptyCheck_sound _ _ emptyValue))

/-- Possible source entries retain key identity. Readable replacement grants no
permission to mutate either the source or target table. -/
theorem map_key_invariant (fuel : Nat) (key key' value value' : Ty)
    (keyLive : ¬ EmptyType key) (valueLive : ¬ EmptyType value)
    (accepted : check fuel (.map key value) (.map key' value') = true) : key = key' := by
  rcases map_key_or_empty fuel key key' value value' accepted with equal | emptyKey | emptyValue
  · exact equal
  · exact False.elim (keyLive emptyKey)
  · exact False.elim (valueLive emptyValue)

/-- Ordered Union replacement fixes every branch, including duplicates and
higher-order payloads. A later permissive branch cannot erase a selected failure. -/
theorem union_branches_invariant (fuel : Nat) (as bs : List Ty)
    (accepted : check fuel (.union as) (.union bs) = true) : as = bs := by
  cases fuel with
  | zero => simp [check] at accepted
  | succ fuel => exact all₂_equal _ (same_sound fuel) _ _ (by simpa only [check, emptySource, Bool.false_and, Bool.or_false] using accepted)

/-- A Sum's finite tag skeleton is retained exactly; parser admission additionally
requires distinct tags and one payload for each tag before this algebra is built. -/
theorem sum_tags_invariant (fuel : Nat) (tags tags' : List Nat) (as bs : List Ty)
    (accepted : check fuel (.sum tags as) (.sum tags' bs) = true) : tags = tags' := by
  cases fuel with
  | zero => simp [check] at accepted
  | succ fuel =>
    have both : decide (tags = tags') = true ∧ all₂ (check fuel) as bs = true := by
      simpa only [check, emptySource, emptyCheck, Bool.false_and, Bool.or_false, Bool.and_eq_true] using accepted
    exact of_decide_eq_true both.1

/-- Semantic replacement is an explicit model premise. A bare Scheme procedure?
recognizer does not satisfy the arrow law; its behavioral interpretation must. -/
structure Interpretation (Value : Type) where
  accepts : Ty → Value → Prop
  emptyLaws : EmptyLaws accepts
  top : ∀ a v, accepts a v → accepts .top v
  uint : ∀ v, accepts (.atom .uint) v → accepts (.atom .integer) v
  numeric : ∀ a b source target, numericBounds a = some source → numericBounds b = some target →
    (∀ value, source.Contains value → target.Contains value) → ∀ v, accepts a v → accepts b v
  rangeEnum : ∀ range values, (∀ value, range.Contains value → value ∈ values) →
    ∀ v, accepts (.integerRange range) v → accepts (.integerEnum values) v
  rangeUnion : ∀ source branches fuel pieces,
    numericPieces fuel (.union branches) = some pieces →
    (∀ value, source.Contains value → integerAccepts fuel (.union branches) value = true) →
    ∀ v, accepts (.integerRange source) v → accepts (.union branches) v
  scalarUnion : ∀ family branches fuel pieces, infiniteScalar family = true →
    numericPieces fuel (.union branches) = some pieces →
    (∀ value, scalarAccepts fuel family (.union branches) value = true) →
    ∀ v, accepts (.atom family) v → accepts (.union branches) v
  boolean : ∀ source values target fuel pieces, booleanValues source = some values →
    numericPieces fuel target = some pieces →
    (∀ value ∈ values, booleanAccepts fuel target value = true) →
    ∀ v, accepts source v → accepts target v
  enumUnion : ∀ values branches fuel pieces,
    numericPieces fuel (.union branches) = some pieces →
    (∀ value ∈ values, integerAccepts fuel (.union branches) value = true) →
    ∀ v, accepts (.integerEnum values) v → accepts (.union branches) v
  list : ∀ a b, (∀ v, accepts a v → accepts b v) →
    ∀ v, accepts (.list a) v → accepts (.list b) v
  maybe : ∀ a b, (∀ v, accepts a v → accepts b v) →
    ∀ v, accepts (.maybe a) v → accepts (.maybe b) v
  orFalse : ∀ a b, (∀ v, accepts a v → accepts b v) →
    ∀ v, accepts (.orFalse a) v → accepts (.orFalse b) v
  tuple : ∀ as bs, RelList (fun a b => ∀ v, accepts a v → accepts b v) as bs →
    ∀ v, accepts (.tuple as) v → accepts (.tuple bs) v
  pair : ∀ a b c d, (∀ v, accepts a v → accepts c v) →
    (∀ v, accepts b v → accepts d v) → ∀ v, accepts (.pair a b) v → accepts (.pair c d) v
  map : ∀ key a b, (∀ v, accepts a v → accepts b v) →
    ∀ v, accepts (.map key a) v → accepts (.map key b) v
  emptyMap : ∀ key value key' value',
    ((∀ item, ¬ accepts key item) ∨ (∀ item, ¬ accepts value item)) →
    ∀ table, accepts (.map key value) table → accepts (.map key' value') table
  sum : ∀ tags as bs, RelList (fun a b => ∀ v, accepts a v → accepts b v) as bs →
    ∀ v, accepts (.sum tags as) v → accepts (.sum tags bs) v
  function : ∀ outs outs' ins ins',
    RelList (fun a b => ∀ v, accepts a v → accepts b v) outs outs' →
    RelList (fun a b => ∀ v, accepts a v → accepts b v) ins' ins →
    ∀ v, accepts (.function outs ins) v → accepts (.function outs' ins') v

/-- Conditional denotational inclusion states exactly what safe replacement means.
The library wrapper still rechecks calls, outputs and exact evidence identities. -/
theorem replacement (model : Interpretation Value) (derivation : Subtype a b) :
    ∀ v, model.accepts a v → model.accepts b v := by
  exact Subtype.rec
    (motive_1 := fun a b _ => ∀ v, model.accepts a v → model.accepts b v)
    (motive_2 := fun as bs _ => RelList (fun a b => ∀ v, model.accepts a v → model.accepts b v) as bs)
    (fun empty _ valid => False.elim ((emptySource_sound _ _ empty).refuses model.emptyLaws _ valid))
    (fun _ _ h => h) model.top model.uint
    (fun left right included => model.numeric _ _ _ _ left right (IntegerRange.replacement _ _ included))
    (fun covered => model.rangeEnum _ _ (IntegerRange.coveredBy_sound _ _ covered))
    (fun bounds accepted => by
      obtain ⟨pieces, projected, covered⟩ := rangeUnionCheck_sound _ _ _ accepted
      intro value valid
      apply model.rangeUnion _ _ _ pieces projected covered value
      exact model.numeric _ _ _ _ bounds rfl (fun _ inside => inside) value valid)
    (fun accepted => by
      obtain ⟨familyKind, pieces, projected, covered⟩ := scalarCheck_sound _ _ _ accepted
      exact model.scalarUnion _ _ _ pieces familyKind projected covered)
    (fun view accepted => by
      obtain ⟨pieces, projected, covered⟩ := booleanCheck_sound _ _ _ accepted
      exact model.boolean _ _ _ _ pieces view projected covered)
    (fun accepted => by
      obtain ⟨pieces, projected, covered⟩ := enumUnionCheck_sound _ _ _ accepted
      exact model.enumUnion _ _ _ pieces projected covered)
    (fun _ ih value valid => by
      obtain ⟨branch, member, admitted⟩ := model.emptyLaws.union _ value valid
      exact ih branch member value admitted)
    (fun _ ih => model.list _ _ ih)
    (fun _ ih => model.maybe _ _ ih)
    (fun _ ih => model.orFalse _ _ ih)
    (fun _ ih => model.tuple _ _ ih)
    (fun _ _ ha hb => model.pair _ _ _ _ ha hb)
    (fun _ ih => model.map _ _ _ ih)
    (fun witness => model.emptyMap _ _ _ _ (witness.elim
      (fun empty => Or.inl ((emptyCheck_sound _ _ empty).refuses model.emptyLaws))
      (fun empty => Or.inr ((emptyCheck_sound _ _ empty).refuses model.emptyLaws))))
    (fun _ ih => model.sum _ _ _ ih)
    (fun _ _ ho hi => model.function _ _ _ _ ho hi)
    RelList.nil (fun _ _ head tail => RelList.cons head tail) derivation

/-- Rank-one templates bind named finite variables; arbitrary recursive equations
and higher-rank impredicative quantifiers are outside this expression language. -/
inductive Expr where
  | ground (type : Ty) | var (name : Nat)
  | list (element : Expr) | tuple (fields : List Expr)
  | maybe (element : Expr) | orFalse (element : Expr)
  | function (outputs inputs : List Expr)
  | pair (left right : Expr) | map (key value : Expr)
  | sum (tags : List Nat) (payloads : List Expr) | union (branches : List Expr)
  deriving Repr

/-- Structural substitution is total in a supplied explicit environment. Admission
separately checks declared names, bounds and available candidate assignments. -/
def substitute (env : Nat → Ty) : Expr → Ty
  | .ground t => t
  | .var name => env name
  | .list e => .list (substitute env e)
  | .maybe e => .maybe (substitute env e)
  | .orFalse e => .orFalse (substitute env e)
  | .tuple es => .tuple (es.map (substitute env))
  | .pair a b => .pair (substitute env a) (substitute env b)
  | .map key value => .map (substitute env key) (substitute env value)
  | .sum tags es => .sum tags (es.map (substitute env))
  | .union es => .union (es.map (substitute env))
  | .function outs ins => .function (outs.map (substitute env)) (ins.map (substitute env))

/-- Partial syntax substitution retains the original constructor/branch/field
positions. Ground leaves are immutable; only explicit variable positions change.
Rich named rows, Function options and Mu binders have separate host syntax laws. -/
def substituteExpr (env : Nat → Expr) : Expr → Expr
  | .ground t => .ground t
  | .var name => env name
  | .list e => .list (substituteExpr env e)
  | .maybe e => .maybe (substituteExpr env e)
  | .orFalse e => .orFalse (substituteExpr env e)
  | .tuple es => .tuple (es.map (substituteExpr env))
  | .pair a b => .pair (substituteExpr env a) (substituteExpr env b)
  | .map key value => .map (substituteExpr env key) (substituteExpr env value)
  | .sum tags es => .sum tags (es.map (substituteExpr env))
  | .union es => .union (es.map (substituteExpr env))
  | .function outs ins => .function (outs.map (substituteExpr env)) (ins.map (substituteExpr env))

/-- One compositional law covers every supported structural expression and every
nested child list. Staged substitution cannot alter tag or alternative order. -/
theorem substitute_substituteExpr (env : Nat → Expr) (tail : Nat → Ty) (expression : Expr) :
    substitute tail (substituteExpr env expression) =
      substitute (fun name => substitute tail (env name)) expression := by
  apply Expr.rec
    (motive_1 := fun e => substitute tail (substituteExpr env e) = substitute (fun n => substitute tail (env n)) e)
    (motive_2 := fun es => (es.map (substituteExpr env)).map (substitute tail) =
      es.map (substitute (fun n => substitute tail (env n)))) <;>
    intros <;> simp_all [substituteExpr, substitute]

/-- An identity syntax transformation preserves the complete expression tree,
including repeated branches and literal Sum tags. -/
theorem substituteExpr_identity (expression : Expr) : substituteExpr Expr.var expression = expression := by
  apply Expr.rec (motive_1 := fun e => substituteExpr Expr.var e = e)
    (motive_2 := fun es => es.map (substituteExpr Expr.var) = es) <;>
    intros <;> simp_all [substituteExpr]

/-- Bounds and call-site inequalities are checked together for each assignment. -/
def satisfies (fuel : Nat) (constraints : List (Expr × Expr)) (env : Nat → Ty) : Bool :=
  constraints.all fun (a, b) => check fuel (substitute env a) (substitute env b)

/-- A successful assignment proves every substituted constraint, without an
assumption that a field recognizer implies another arbitrary field recognizer. -/
theorem satisfies_sound (fuel constraints env) (accepted : satisfies fuel constraints env = true)
    (bound : (a, b) ∈ constraints) : Subtype (substitute env a) (substitute env b) := by
  exact check_sound _ _ _ ((List.all_eq_true.mp accepted) _ bound)

/-- Classification retains ambiguity. A singleton is accepted only after the
whole supplied finite assignment list was checked; a prefix is never a solution. -/
inductive Inference (Assignment : Type) where
  | none | unique (assignment : Assignment) | ambiguous (assignments : List Assignment)
  deriving Repr, DecidableEq
/-- Infer over an explicit finite universe; Scheme constructs the Cartesian list
lazily under its shared work counter, preserving this order and exact filtering. -/
def infer (valid : Assignment → Bool) (candidates : List Assignment) : Inference Assignment :=
  match candidates.filter valid with
  | [] => .none
  | [one] => .unique one
  | many => .ambiguous many

/-- Unique inference contains an actual admitted candidate, not the first match
of an incomplete or ambiguous search. -/
theorem infer_unique (valid : Assignment → Bool) (candidates : List Assignment)
    (accepted : infer valid candidates = .unique assignment) :
    assignment ∈ candidates ∧ valid assignment = true := by
  unfold infer at accepted
  split at accepted <;> simp_all
  next one matched =>
    have equal : one = assignment := by simpa using accepted
    subst one
    have member : assignment ∈ candidates.filter valid := by simp [matched]
    exact List.mem_filter.mp member

/-- Completed failure is exact within the supplied finite universe. It does not
claim that no instance exists outside that universe or at arbitrary rank. -/
theorem infer_none (valid : Assignment → Bool) (candidates : List Assignment)
    (refused : infer valid candidates = .none) :
    ∀ assignment ∈ candidates, valid assignment = false := by
  have empty : candidates.filter valid = [] := by
    unfold infer at refused
    split at refused <;> simp_all
  intro assignment member
  cases good : valid assignment with
  | false => rfl
  | true =>
    have inFiltered : assignment ∈ candidates.filter valid := List.mem_filter.mpr ⟨member, good⟩
    simp [empty] at inFiltered

/-- Unique bounded inference entails every substituted declaration/query law. -/
theorem inferred_constraints (fuel : Nat) (constraints : List (Expr × Expr)) (candidates : List (Nat → Ty))
    (accepted : infer (satisfies fuel constraints) candidates = .unique env)
    (bound : (a, b) ∈ constraints) : Subtype (substitute env a) (substitute env b) := by
  exact satisfies_sound _ _ _ (infer_unique _ _ accepted).2 bound

/-- Resource failure carries no partial assignment or initialized prototype. -/
inductive Failure where
  | unsupported | malformed | exhausted | bounds
  deriving Repr, DecidableEq
/-- Atomic bounded search refuses before classification when the assignment scan
is incomplete. Individual expression/comparison work is additionally metered by
Scheme; this abstract scan bound is not an exact allocation/performance claim. -/
def inferBounded (budget : Nat) (valid : Assignment → Bool) (candidates : List Assignment) :
    Except Failure (Inference Assignment) :=
  if candidates.length ≤ budget then .ok (infer valid candidates) else .error .exhausted

/-- Exhaustion cannot expose a unique candidate from an already accepted prefix. -/
theorem incomplete_refuses (budget : Nat) (valid : Assignment → Bool) (candidates : List Assignment)
    (incomplete : budget < candidates.length) :
    inferBounded budget valid candidates = .error .exhausted := by
  simp [inferBounded, Nat.not_le.mpr incomplete]

/-- A successful bounded unique result retains semantic candidate validity. -/
theorem bounded_unique (budget : Nat) (valid : Assignment → Bool) (candidates : List Assignment)
    (accepted : inferBounded budget valid candidates = .ok (.unique assignment)) :
    assignment ∈ candidates ∧ valid assignment = true := by
  unfold inferBounded at accepted
  split at accepted
  · exact infer_unique valid candidates (Except.ok.inj accepted)
  · contradiction

/-- Candidate-dependent projection retains the layout/signature evidence beside
its original assignment. Bounds/kind mismatch rejects only that candidate; other
failures abort the whole search. Fuel is shared across the complete scan and no
accepted prefix is returned on exhaustion. Expression-level work is separately
metered by Scheme, so this scan bound is not a runtime cost certificate. -/
def collectCandidates (derive : Assignment → Except Failure Evidence)
    (valid : Assignment → Evidence → Bool) : Nat → List Assignment →
    Except Failure (List (Assignment × Evidence))
  | _, [] => .ok []
  | 0, _ :: _ => .error .exhausted
  | fuel + 1, candidate :: rest =>
    match derive candidate with
    | .error .bounds => collectCandidates derive valid fuel rest
    | .error cause => .error cause
    | .ok evidence =>
      match collectCandidates derive valid fuel rest with
      | .error cause => .error cause
      | .ok accepted => .ok (if valid candidate evidence then (candidate, evidence) :: accepted else accepted)

/-- Every retained layout belongs to its own candidate, and that same candidate
satisfies all bounds and call inequalities derived from the layout. Sibling
queries from different alternatives cannot be merged into a synthetic solution. -/
theorem collectCandidates_sound (derive : Assignment → Except Failure Evidence)
    (valid : Assignment → Evidence → Bool) (fuel candidates accepted)
    (completed : collectCandidates derive valid fuel candidates = .ok accepted)
    (entry : Assignment × Evidence) (member : entry ∈ accepted) :
    entry.1 ∈ candidates ∧ derive entry.1 = .ok entry.2 ∧ valid entry.1 entry.2 = true := by
  induction candidates generalizing fuel accepted with
  | nil => simp [collectCandidates] at completed; subst accepted; simp at member
  | cons candidate rest ih =>
    cases fuel with
    | zero => simp [collectCandidates] at completed
    | succ fuel =>
      cases projected : derive candidate with
      | error cause =>
        cases cause <;> simp only [collectCandidates, projected] at completed
        all_goals try contradiction
        obtain ⟨source, own, checked⟩ := ih fuel accepted completed member
        exact ⟨List.mem_cons_of_mem _ source, own, checked⟩
      | ok evidence =>
        cases tail : collectCandidates derive valid fuel rest with
        | error cause => simp [collectCandidates, projected, tail] at completed
        | ok remaining =>
          by_cases checked : valid candidate evidence = true
          · simp [collectCandidates, projected, tail, checked] at completed
            subst accepted
            rcases List.mem_cons.mp member with equal | later
            · subst entry; exact ⟨by simp, projected, checked⟩
            · obtain ⟨source, own, good⟩ := ih fuel remaining tail later
              exact ⟨List.mem_cons_of_mem _ source, own, good⟩
          · simp [collectCandidates, projected, tail, checked] at completed
            subst accepted
            obtain ⟨source, own, good⟩ := ih fuel remaining tail member
            exact ⟨List.mem_cons_of_mem _ source, own, good⟩

/-- Complete successful scanning retains every admitted candidate. Thus a unique
answer cannot hide another valid layout, and no-solution is relative to the whole
explicit universe rather than to a visited prefix. -/
theorem collectCandidates_complete (derive : Assignment → Except Failure Evidence)
    (valid : Assignment → Evidence → Bool) (fuel candidates accepted)
    (completed : collectCandidates derive valid fuel candidates = .ok accepted)
    (candidate : Assignment) (evidence : Evidence) (source : candidate ∈ candidates)
    (projected : derive candidate = .ok evidence) (checked : valid candidate evidence = true) :
    (candidate, evidence) ∈ accepted := by
  induction candidates generalizing fuel accepted with
  | nil => simp at source
  | cons head rest ih =>
    cases fuel with
    | zero => simp [collectCandidates] at completed
    | succ fuel =>
      cases first : derive head with
      | error cause =>
        cases cause <;> simp only [collectCandidates, first] at completed
        all_goals try contradiction
        rcases List.mem_cons.mp source with equal | later
        · subst head; rw [projected] at first; contradiction
        · exact ih fuel accepted completed later
      | ok value =>
        cases tail : collectCandidates derive valid fuel rest with
        | error cause => simp [collectCandidates, first, tail] at completed
        | ok remaining =>
          rcases List.mem_cons.mp source with equal | later
          · subst head
            have same : value = evidence := by simpa [projected] using first.symm
            subst value
            simp [collectCandidates, first, tail, checked] at completed
            subst accepted
            exact List.mem_cons_self
          · have retained := ih fuel remaining tail later
            by_cases headValid : valid head value = true
            · simp [collectCandidates, first, tail, headValid] at completed
              subst accepted
              exact List.mem_cons_of_mem _ retained
            · simp [collectCandidates, first, tail, headValid] at completed
              subst accepted
              exact retained

/-- Not even a valid first assignment can survive an incomplete scan. -/
theorem collectCandidates_exhausted (derive : Assignment → Except Failure Evidence)
    (valid : Assignment → Evidence → Bool) (candidate : Assignment) (rest : List Assignment) :
    collectCandidates derive valid 0 (candidate :: rest) = .error .exhausted := rfl

/-- A well-formed candidate with the wrong kind is an ordinary negative choice,
not a whole-request syntax error and not an excuse to suppress later errors. -/
theorem collectCandidates_bounds (derive : Assignment → Except Failure Evidence)
    (valid : Assignment → Evidence → Bool) (fuel candidate rest)
    (rejected : derive candidate = .error .bounds) :
    collectCandidates derive valid (fuel + 1) (candidate :: rest) =
      collectCandidates derive valid fuel rest := by
  simp [collectCandidates, rejected]

/-- Prefix binding fixes the first parameters and renumbers only the residual
variables. This is the semantic environment of capture-free residual syntax. -/
def prefixEnvironment (fixed : List Ty) (tail : Nat → Ty) (name : Nat) : Ty :=
  if present : name < fixed.length then fixed[name] else tail (name - fixed.length)

/-- A later inference assignment cannot overwrite an already bound ground prefix. -/
theorem prefixEnvironment_fixed (fixed : List Ty) (tail : Nat → Ty) (name : Nat)
    (present : name < fixed.length) : prefixEnvironment fixed tail name = fixed[name] := by
  simp [prefixEnvironment, present]

/-- The first unbound variable is exactly the first residual parameter. -/
theorem prefixEnvironment_tail (fixed : List Ty) (tail : Nat → Ty) (name : Nat) :
    prefixEnvironment fixed tail (fixed.length + name) = tail name := by
  have absent : ¬ fixed.length + name < fixed.length := by omega
  simp [prefixEnvironment, absent]

/-- Residual variable indices match the existing persistent prefix environment.
This is syntax specialization, not a fresh inference or receiver construction. -/
def specializeExpr (fixed : List Ty) (expression : Expr) : Expr :=
  substituteExpr (fun name => if present : name < fixed.length then .ground fixed[name] else .var (name - fixed.length)) expression

/-- Grounding after a partial specialization agrees with grounding the original
tree at the combined environment, for arbitrary containers and Function variance. -/
theorem substitute_specializeExpr (fixed : List Ty) (tail : Nat → Ty) (expression : Expr) :
    substitute tail (specializeExpr fixed expression) = substitute (prefixEnvironment fixed tail) expression := by
  rw [specializeExpr, substitute_substituteExpr]
  congr 1
  funext name
  by_cases present : name < fixed.length <;> simp [present, substitute, prefixEnvironment]

/-- Entire bound/query lists commute with prefix specialization, not just an
isolated field. The original order and every obligation are retained. -/
theorem satisfies_specializeExpr (fuel : Nat) (fixed : List Ty)
    (constraints : List (Expr × Expr)) (tail : Nat → Ty) :
    satisfies fuel (constraints.map (fun (a, b) => (specializeExpr fixed a, specializeExpr fixed b))) tail =
      satisfies fuel constraints (prefixEnvironment fixed tail) := by
  simp [satisfies, List.all_map, Function.comp_def, substitute_specializeExpr]

/-- Unique complete residual inference establishes every ORIGINAL substituted
bound/query under the combined environment, not just the unbound suffix alone. -/
theorem inferred_prefix_constraints (fuel budget : Nat) (fixed : List Ty)
    (constraints : List (Expr × Expr)) (candidates : List (Nat → Ty))
    (accepted : inferBounded budget (fun tail => satisfies fuel constraints (prefixEnvironment fixed tail))
      candidates = .ok (.unique tail)) (bound : (a,b) ∈ constraints) :
    Subtype (substitute (prefixEnvironment fixed tail) a) (substitute (prefixEnvironment fixed tail) b) := by
  exact satisfies_sound _ _ _ (bounded_unique _ _ _ accepted).2 bound

/-- Direct mathematical arrow replacement: accepting a broader input and
returning a narrower output suffices, assuming the original behavior is valid. -/
theorem function_replacement (sourceIn targetIn sourceOut targetOut : Value → Prop)
    (input : ∀ v, targetIn v → sourceIn v) (output : ∀ v, sourceOut v → targetOut v)
    (f : Value → Value) (behavior : ∀ v, sourceIn v → sourceOut (f v)) :
    ∀ v, targetIn v → targetOut (f v) := fun _v h => output _ (behavior _ (input _ h))
/-- Private-request acceptance witness. Constraints and substitution are the
same captured finite values before and after live binding refresh. This is not
permission to trust public mutable schema fields or arbitrary host predicates. -/
structure CheckedAssignment (fuel : Nat) (constraints : List (Expr × Expr)) where
  environment : Nat → Ty
  accepted : satisfies fuel constraints environment = true
/-- Only a completed unique search supplies the accepted substitution witness. -/
def checkedUnique (fuel constraints candidates environment)
    (completed : inferBounded budget (satisfies fuel constraints) candidates = .ok (.unique environment)) :
    CheckedAssignment fuel constraints :=
  ⟨environment, (bounded_unique _ _ _ completed).2⟩
/-- Refresh live source/binding state before compiling the accepted assignment.
The same assembler retains ordinary intrinsic identity and construction rules. -/
def instantiatePrepared (refresh : Except Error Snapshot) (checked : CheckedAssignment fuel constraints)
    (assemble : Snapshot → (Nat → Ty) → Except Error Artifact) : Except Error Artifact :=
  refresh.bind fun snapshot => assemble snapshot checked.environment
/-- The former replay path repeats only pure captured constraints after the same
live refresh. Its error parameter is unreachable for a complete accepted witness. -/
def instantiateRechecked (refresh : Except Error Snapshot) (checked : CheckedAssignment fuel constraints)
    (assemble : Snapshot → (Nat → Ty) → Except Error Artifact) (denied : Error) : Except Error Artifact :=
  refresh.bind fun snapshot => if satisfies fuel constraints checked.environment then
    assemble snapshot checked.environment else .error denied
/-- Removing redundant pure checks preserves the exact result/error/artifact and
refresh order; equality also covers failed refresh and failed compilation. -/
theorem instantiatePrepared_eq (refresh : Except Error Snapshot)
    (checked : CheckedAssignment fuel constraints)
    (assemble : Snapshot → (Nat → Ty) → Except Error Artifact) (denied : Error) :
    instantiatePrepared refresh checked assemble = instantiateRechecked refresh checked assemble denied := by
  simp [instantiatePrepared, instantiateRechecked, checked.accepted]
/-- A current-source failure still prevents all construction and publication. -/
theorem instantiatePrepared_refuses (cause : Error) (checked : CheckedAssignment fuel constraints)
    (assemble : Snapshot → (Nat → Ty) → Except Error Artifact) :
    instantiatePrepared (.error cause) checked assemble = .error cause := rfl
/-- Every original captured bound remains proved without replaying the checker. -/
theorem checkedUnique_bound (completed : inferBounded budget (satisfies fuel constraints)
    candidates = .ok (.unique environment)) (member : (a,b) ∈ constraints) :
    Subtype (substitute environment a) (substitute environment b) :=
  satisfies_sound fuel constraints environment (bounded_unique _ _ _ completed).2 member
/-- Abstract charged comparison work removes exactly the repeated bound checks.
Copying, allocation, compilation, primitive costs and GC require separate models
or measurements; this is not an elapsed-time or total-allocation speed theorem. -/
theorem accepted_comparison_work (refresh build replay : Nat) :
    refresh + replay + build = (refresh + build) + replay ∧ refresh + build ≤ refresh + replay + build := by
  omega

/-- Whole-call admission uses the standard left-to-right monadic traversal.
It checks every observation before projection; host decoding/Type admission is
an explicit interpretation premise, not inferred from this finite model. -/
def checkCalls (admit : Call → Except Failure Unit) (calls : List Call) :
    Except Failure (List Unit) := calls.mapM admit

/-- One standard traversal step preserves left-to-right admission order. -/
theorem checkCalls_cons (admit : Call → Except Failure Unit) (call : Call) (calls : List Call) :
    checkCalls admit (call :: calls) =
      (admit call).bind (fun result => (checkCalls admit calls).map (result :: ·)) := by
  unfold checkCalls
  rw [List.mapM_cons]
  cases admit call <;> cases calls.mapM admit <;> rfl

/-- A completed preflight has admitted every sibling, including unselected ones. -/
theorem checkCalls_sound (admit : Call → Except Failure Unit) (calls : List Call)
    (checked : List Unit) (accepted : checkCalls admit calls = .ok checked)
    (call : Call) (member : call ∈ calls) : admit call = .ok () := by
  induction calls generalizing checked with
  | nil => simp at member
  | cons head rest ih =>
    cases first : admit head with
    | error cause => simp [checkCalls_cons, first, Except.bind] at accepted
    | ok result =>
      cases result
      cases tail : checkCalls admit rest with
      | error cause => simp [checkCalls_cons, first, tail, Except.bind, Except.map] at accepted
      | ok remaining =>
        rcases List.mem_cons.mp member with equal | later
        · subst call; exact first
        · exact ih remaining tail later

/-- A late invalid sibling keeps its original cause after all valid predecessors;
no projection or candidate search can turn it into an ordinary bounds failure. -/
theorem checkCalls_late_refusal (admit : Call → Except Failure Unit)
    (front : List Call) (bad : Call) (rest : List Call) (cause : Failure)
    (prior : ∀ call ∈ front, admit call = .ok ()) (refused : admit bad = .error cause) :
    checkCalls admit (front ++ bad :: rest) = .error cause := by
  induction front with
  | nil => simp [checkCalls_cons, refused, Except.bind]
  | cons head tail ih =>
    have first := prior head (by simp)
    have later : ∀ call ∈ tail, admit call = .ok () := fun call member => prior call (by simp [member])
    simp [checkCalls_cons, first, ih later, Except.bind, Except.map]

/-- Candidate-independent admission precedes the delayed complete projection.
The same gate serves fixed and candidate-dependent signature layouts. -/
def projectCalls (admit : Call → Except Failure Unit) (calls : List Call)
    (project : Unit → Except Failure Queries) : Except Failure Queries :=
  (checkCalls admit calls).bind (fun _ => project ())

/-- Failed preflight cannot call a projection, including one that would fail bounds. -/
theorem projectCalls_refused (admit : Call → Except Failure Unit) (calls : List Call)
    (project : Unit → Except Failure Queries) (cause : Failure)
    (refused : checkCalls admit calls = .error cause) :
    projectCalls admit calls project = .error cause := by
  simp [projectCalls, refused, Except.bind]

/-- Success preserves the exact original projection plus complete call admission. -/
theorem projectCalls_sound (admit : Call → Except Failure Unit) (calls : List Call)
    (project : Unit → Except Failure Queries) (queries : Queries)
    (accepted : projectCalls admit calls project = .ok queries) :
    project () = .ok queries ∧ ∀ call ∈ calls, admit call = .ok () := by
  cases checked : checkCalls admit calls with
  | error cause => simp [projectCalls, checked, Except.bind] at accepted
  | ok observations =>
    exact ⟨by simpa [projectCalls, checked, Except.bind] using accepted,
      fun call member => checkCalls_sound admit calls observations checked call member⟩

/-- Own the finite constraint syntax before refreshing computed source state.
`capture` must faithfully project the initial host syntax into immutable Lean
data. Heap nonaliasing and callback execution are runtime correspondence premises;
the refreshed state cannot replace the constraints supplied to the existing solver. -/
def inferCaptured (capture : State → Except Failure (List (Expr × Expr)))
    (refresh : State → Except Failure State) (initial : State) (fuel budget : Nat)
    (candidates : List (Nat → Ty)) : Except Failure (Inference (Nat → Ty)) :=
  (capture initial).bind fun constraints =>
    (refresh initial).bind fun _ => inferBounded budget (satisfies fuel constraints) candidates

/-- Finite capture failure precedes every computed getter and candidate search. -/
theorem inferCaptured_capture_refused (capture : State → Except Failure (List (Expr × Expr)))
    (refresh : State → Except Failure State) (initial : State) (fuel budget : Nat)
    (candidates : List (Nat → Ty)) (cause : Failure) (failed : capture initial = .error cause) :
    inferCaptured capture refresh initial fuel budget candidates = .error cause := by
  simp [inferCaptured, failed, Except.bind]

/-- A getter failure keeps its exact cause; no partial search result escapes. -/
theorem inferCaptured_refresh_refused (capture : State → Except Failure (List (Expr × Expr)))
    (refresh : State → Except Failure State) (initial : State) (fuel budget : Nat)
    (candidates : List (Nat → Ty)) (constraints : List (Expr × Expr)) (cause : Failure)
    (captured : capture initial = .ok constraints) (failed : refresh initial = .error cause) :
    inferCaptured capture refresh initial fuel budget candidates = .error cause := by
  simp [inferCaptured, captured, failed, Except.bind]

/-- Any successful source refresh uses the same original complete constraints.
This retains classification, ambiguity, exhaustion and original candidate order. -/
theorem inferCaptured_eq (capture : State → Except Failure (List (Expr × Expr)))
    (refresh : State → Except Failure State) (initial current : State) (fuel budget : Nat)
    (candidates : List (Nat → Ty)) (constraints : List (Expr × Expr))
    (captured : capture initial = .ok constraints) (refreshed : refresh initial = .ok current) :
    inferCaptured capture refresh initial fuel budget candidates =
      inferBounded budget (satisfies fuel constraints) candidates := by
  simp [inferCaptured, captured, refreshed, Except.bind]

/-- A unique result after arbitrary successful refresh still proves every
original bound. A changed live syntax cannot substitute a weaker constraint. -/
theorem inferCaptured_bound (capture : State → Except Failure (List (Expr × Expr)))
    (refresh : State → Except Failure State) (initial : State) (fuel budget : Nat)
    (candidates : List (Nat → Ty)) (constraints : List (Expr × Expr))
    (captured : capture initial = .ok constraints)
    (accepted : inferCaptured capture refresh initial fuel budget candidates = .ok (.unique environment))
    (member : (a,b) ∈ constraints) :
    Subtype (substitute environment a) (substitute environment b) := by
  cases refreshed : refresh initial with
  | error cause => simp [inferCaptured, captured, refreshed, Except.bind] at accepted
  | ok current =>
    rw [inferCaptured_eq capture refresh initial current fuel budget candidates constraints captured refreshed] at accepted
    exact checkedUnique_bound accepted member

/-- One owned finite request retains BOTH its original candidate universe and
its original bound/query obligations. Host call projection and Cartesian
enumeration must faithfully interpret the captured syntax; this is not a heap
or parser model and does not imply arbitrary callback stability. -/
structure InferenceRequest where
  candidates : List (Nat → Ty)
  constraints : List (Expr × Expr)

/-- Reuse constraint capture/refresh ordering with the same captured request's
candidate universe. Source refresh cannot supply a replacement candidate list. -/
def inferCapturedRequest (capture : State → Except Failure InferenceRequest)
    (refresh : State → Except Failure State) (initial : State) (fuel budget : Nat) :
    Except Failure (Inference (Nat → Ty)) :=
  (capture initial).bind fun request =>
    inferCaptured (fun _ => .ok request.constraints) refresh initial fuel budget request.candidates

/-- Cyclic/deep request capture refuses before refresh or any candidate prefix. -/
theorem inferCapturedRequest_refused (capture : State → Except Failure InferenceRequest)
    (refresh : State → Except Failure State) (initial : State) (fuel budget : Nat)
    (cause : Failure) (failed : capture initial = .error cause) :
    inferCapturedRequest capture refresh initial fuel budget = .error cause := by
  simp [inferCapturedRequest, failed, Except.bind]

/-- Any successful refresh preserves exact classification over the original
request, including candidate order, ambiguity, no solution and exhaustion. -/
theorem inferCapturedRequest_eq (capture : State → Except Failure InferenceRequest)
    (refresh : State → Except Failure State) (initial current : State) (fuel budget : Nat)
    (request : InferenceRequest) (captured : capture initial = .ok request)
    (refreshed : refresh initial = .ok current) :
    inferCapturedRequest capture refresh initial fuel budget =
      inferBounded budget (satisfies fuel request.constraints) request.candidates := by
  simp [inferCapturedRequest, captured, inferCaptured, refreshed, Except.bind]

/-- A getter failure keeps its exact cause after successful request capture. -/
theorem inferCapturedRequest_refresh_refused (capture : State → Except Failure InferenceRequest)
    (refresh : State → Except Failure State) (initial : State) (fuel budget : Nat)
    (request : InferenceRequest) (captured : capture initial = .ok request)
    (cause : Failure) (failed : refresh initial = .error cause) :
    inferCapturedRequest capture refresh initial fuel budget = .error cause := by
  simp [inferCapturedRequest, captured, inferCaptured, failed, Except.bind]

/-- Unique publication cannot introduce an assignment outside the original
universe, and every original captured inequality remains proved. -/
theorem inferCapturedRequest_unique (capture : State → Except Failure InferenceRequest)
    (refresh : State → Except Failure State) (initial : State) (fuel budget : Nat)
    (request : InferenceRequest) (captured : capture initial = .ok request)
    (accepted : inferCapturedRequest capture refresh initial fuel budget = .ok (.unique environment)) :
    environment ∈ request.candidates ∧ ∀ a b, (a,b) ∈ request.constraints →
      Subtype (substitute environment a) (substitute environment b) := by
  cases refreshed : refresh initial with
  | error cause =>
    simp [inferCapturedRequest, captured, inferCaptured, refreshed, Except.bind] at accepted
  | ok current =>
    rw [inferCapturedRequest_eq capture refresh initial current fuel budget request captured refreshed] at accepted
    have checked := bounded_unique _ _ _ accepted
    exact ⟨checked.1, fun _ _ member => satisfies_sound _ _ _ checked.2 member⟩

end LeanPoo.Functional.PrototypeTypes
