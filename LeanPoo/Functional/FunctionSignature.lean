import LeanPoo.Functional.Validation
import LeanPoo.Functional.PrototypeTypes
import LeanPoo.Functional.RowTypes

/-! Finite declarative call signatures. These laws describe supplied arguments and
ordered dispatch; host default evaluation and Gerbil procedure arity remain premises. -/
namespace LeanPoo.Functional.FunctionSignature

/-- Required and optional positions, rest permission, and declared/required keys. -/
structure Signature (Key : Type) where
  required : Nat
  optional : Nat := 0
  rest : Bool := false
  keywords : List Key := []
  requiredKeywords : List Key := []
  deriving Repr, DecidableEq

/-- A decoded call retains supplied values only; absent defaults have no entry. -/
structure Call (Key Value : Type) where
  positional : List Value
  keywords : List (Key × Value) := []
  deriving Repr, DecidableEq

/-- Reject duplicate keys as well as arity, unknown-key and missing-key errors. -/
def accepts [DecidableEq Key] (signature : Signature Key) (call : Call Key Value) : Bool :=
  decide (signature.required ≤ call.positional.length) &&
  (signature.rest || decide (call.positional.length ≤ signature.required + signature.optional)) &&
  decide ((call.keywords.map Prod.fst).Nodup) &&
  call.keywords.all (fun entry => decide (entry.1 ∈ signature.keywords)) &&
  signature.requiredKeywords.all (fun key => decide (key ∈ call.keywords.map Prod.fst))

/-- Dispatch by the first structural match, before invoking any type check. -/
def select [DecidableEq Key] (signatures : List (Signature Key)) (call : Call Key Value) :=
  signatures.find? (accepts · call)

/-- A matching earlier clause shadows all later clauses, regardless of value types. -/
theorem select_first [DecidableEq Key] (head : Signature Key) (tail) (call : Call Key Value)
    (matched : accepts head call = true) : select (head :: tail) call = some head := by
  simp [select, List.find?, matched]

/-- Selection returns a member of the declared sequence with an accepted shape. -/
theorem select_sound [DecidableEq Key] (signatures : List (Signature Key)) (call : Call Key Value)
    (signature) (selected : select signatures call = some signature) :
    signature ∈ signatures ∧ accepts signature call = true := by
  induction signatures with
  | nil => simp [select, List.find?] at selected
  | cons head tail ih =>
    by_cases matched : accepts head call = true
    · have same : head = signature := by simpa [select, List.find?, matched] using selected
      subst signature
      exact ⟨by simp, matched⟩
    · have later : select tail call = some signature := by
        simpa [select, List.find?, matched] using selected
      obtain ⟨member, shape⟩ := ih later
      exact ⟨by simp [member], shape⟩

/-- An ill-shaped call cannot reach normalization or the body. -/
def invoke [DecidableEq Key] (signatures : List (Signature Key)) (call : Call Key Value)
    (shapeError : Error) (normalize : Signature Key → Call Key Value → Except Error (Call Key Value))
    (body : Call Key Value → Except Error Result) : Except Error Result :=
  match select signatures call with
  | none => .error shapeError
  | some signature => (normalize signature call).bind body

/-- Structural refusal has no body branch. -/
theorem invoke_shape_error [DecidableEq Key] (signatures) (call : Call Key Value)
    (shapeError : Error) (normalize) (body : Call Key Value → Except Error Result)
    (refused : select signatures call = none) :
    invoke signatures call shapeError normalize body = .error shapeError := by
  simp [invoke, refused]

/-- Type refusal preserves its error and never falls through to another signature. -/
theorem invoke_type_error [DecidableEq Key] (signatures) (call : Call Key Value)
    (shapeError error : Error) (normalize) (body : Call Key Value → Except Error Result)
    (signature) (selected : select signatures call = some signature)
    (refused : normalize signature call = .error error) :
    invoke signatures call shapeError normalize body = .error error := by
  simp [invoke, selected, refused, Except.bind]

/-- Ordered field checking preserves supplied cardinality, so it cannot insert or
execute missing optional defaults. The host remains responsible for those defaults. -/
theorem supplied_length (check : Input → Except Error Value) (values : List Input) (checked : List Value)
    (success : Validation.traverse check values = .ok checked) : checked.length = values.length := by
  induction values generalizing checked with
  | nil => simp [Validation.traverse] at success; subst checked; rfl
  | cons head tail ih =>
    simp only [Validation.traverse] at success
    cases h : check head with
    | error error => simp [h, Except.bind] at success
    | ok value =>
      cases t : Validation.traverse check tail with
      | error error => simp [h, t, Except.bind, Except.map] at success
      | ok rest =>
        simp [h, t, Except.bind, Except.map] at success
        subst checked
        simp [ih rest t]

/-- Typed token view of the standard alist-to-plist conversion. Left tokens
are declared keys; right tokens retain values, including false or keyword data.
The host's untyped representation and escape dispatcher need separate controls. -/
def encodeKeywords (entries : List (Key × Value)) : List (Sum Key Value) :=
  entries.foldr (fun entry rest => .inl entry.1 :: .inr entry.2 :: rest) []

/-- Delegation preserves the former map-and-flatten result exactly. -/
theorem encodeKeywords_flatMap (entries : List (Key × Value)) :
    encodeKeywords entries = entries.flatMap (fun entry => [.inl entry.1, .inr entry.2]) := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      simp only [encodeKeywords] at ih
      simpa [encodeKeywords] using ih

/-- Concatenating keyword bindings preserves their source order. -/
theorem encodeKeywords_append (first second : List (Key × Value)) :
    encodeKeywords (first ++ second) = encodeKeywords first ++ encodeKeywords second := by
  simp [encodeKeywords_flatMap, List.flatMap_append]

/-- One binding contributes exactly two tokens; omitted bindings stay omitted. -/
theorem encodeKeywords_length (entries : List (Key × Value)) :
    (encodeKeywords entries).length = 2 * entries.length := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      simp only [encodeKeywords] at ih
      simp [encodeKeywords]
      omega

/-- Recognize the alternating structural grammar before interpreting key policy. -/
def decodeKeywords : List (Sum Key Value) → Option (List (Key × Value))
  | [] => some []
  | .inl key :: .inr value :: rest => (decodeKeywords rest).map ((key, value) :: ·)
  | _ => none

/-- Standard structural conversion returns the same keys and exact payloads. -/
theorem decode_encodeKeywords (entries : List (Key × Value)) :
    decodeKeywords (encodeKeywords entries) = some entries := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      simp only [encodeKeywords] at ih
      simpa [encodeKeywords, decodeKeywords] using ih

/-- A dangling key refuses before any domain-specific option interpretation. -/
theorem decodeKeywords_dangling (key : Key) :
    decodeKeywords (Value := Value) [.inl key] = none := rfl

variable {Key Value : Type}

/-- Reconstruct the source-ordered keyword bindings from an admitted lookup.
The core dispatcher's table contents and projected identifiers are premises;
enumerating that table instead would not retain the declared keyword order. -/
def restoreKeywords (keys : List Key) (lookup : Key → Option Value) : Option (List (Key × Value)) :=
  keys.mapM (fun key => (lookup key).map (fun value => (key, value)))

/-- Empty keyword metadata performs no lookup. -/
theorem restoreKeywords_nil (lookup : Key → Option Value) : restoreKeywords [] lookup = some [] := rfl

/-- Bindings are restored in declaration order, including an explicitly false value. -/
theorem restoreKeywords_cons (key : Key) (rest) (lookup : Key → Option Value) :
    restoreKeywords (key :: rest) lookup = (do
      let value ← lookup key
      let tail ← restoreKeywords rest lookup
      pure ((key, value) :: tail)) := by
  unfold restoreKeywords
  simp only [List.mapM_cons]
  cases lookup key <;> rfl

/-- An absent projected binding refuses instead of emitting a truncated call. -/
theorem restoreKeywords_missing (key : Key) (rest) (lookup : Key → Option Value)
    (missing : lookup key = none) : restoreKeywords (key :: rest) lookup = none := by
  rw [restoreKeywords_cons, missing]
  rfl

/-- Source order and every original payload survive table reconstruction.
Duplicate-key admission remains the host dispatcher's separate obligation. -/
theorem restoreKeywords_source (entries : List (Key × Value)) (lookup : Key → Option Value)
    (current : ∀ entry ∈ entries, lookup entry.1 = some entry.2) :
    restoreKeywords (entries.map Prod.fst) lookup = some entries := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    have head := current entry (by simp)
    have tail := ih (by intro other member; exact current other (by simp [member]))
    rw [List.map_cons, restoreKeywords_cons, head, tail]
    rfl

/-- Forward only already resolved bindings. The leading receiver and escaped rest
data remain positional; no default expression or predicate is present here. -/
def forwardResolved (leading : List Value) (call : Call Key Value) (rest : List Value) : Call Key Value :=
  ⟨leading ++ call.positional ++ rest, call.keywords⟩

/-- Keyword bindings are unchanged by receiver/rest forwarding. -/
theorem forwardResolved_keywords (leading : List Value) (call : Call Key Value) (rest) :
    (forwardResolved leading call rest).keywords = call.keywords := rfl

/-- Each supplied receiver/position/rest value occurs exactly once, in order. -/
theorem forwardResolved_positional (leading : List Value) (call : Call Key Value) (rest) :
    (forwardResolved leading call rest).positional = leading ++ call.positional ++ rest := rfl

/-- Forwarding inserts no omitted defaults, extra receiver or synthetic arguments. -/
theorem forwardResolved_length (leading : List Value) (call : Call Key Value) (rest) :
    (forwardResolved leading call rest).positional.length =
      leading.length + call.positional.length + rest.length := by simp [forwardResolved, Nat.add_assoc]

/-- Nested wrappers preserve prefix/suffix order without reinterpreting any value. -/
theorem forwardResolved_compose (outer inner : List Value) (call : Call Key Value)
    (innerRest outerRest : List Value) :
    forwardResolved outer (forwardResolved inner call innerRest) outerRest =
      forwardResolved (outer ++ inner) call (innerRest ++ outerRest) := by
  simp [forwardResolved, List.append_assoc]
variable {M : Type → Type} {Fragments Row Result Error : Type}

/-- Historical variadic transport only captures fragments and relays the row.
The host's rest-list construction is a separate implementation obligation. -/
def captureCombination (combine : Fragments → Row → M Result) (fragments : Fragments) : Row → M Result :=
  fun row => combine fragments row

/-- Direct generic lowering selects the combiner, then demands the raw fragments,
then checks the combiner before invoking it on the complete resolved row. -/
def combineDirect [Monad M] (selection : M (Fragments → Row → M Result))
    (lookup : M Fragments) (admit : (Fragments → Row → M Result) → M Unit) (row : Row) : M Result := do
  let combine ← selection
  let fragments ← lookup
  admit combine
  combine fragments row

/-- The preceding lowering has the same ordered stages plus an ephemeral relay. -/
def combineCaptured [Monad M] (selection : M (Fragments → Row → M Result))
    (lookup : M Fragments) (admit : (Fragments → Row → M Result) → M Unit) (row : Row) : M Result := do
  let combine ← selection
  let fragments ← lookup
  admit combine
  captureCombination combine fragments row

/-- Relay elimination preserves monadic effects, complete rows and result carriers.
No associativity rewrite or reordering of selection, lookup or admission is used. -/
theorem combineDirect_eq [Monad M] (selection : M (Fragments → Row → M Result))
    (lookup : M Fragments) (admit) (row : Row) :
    combineDirect selection lookup admit row = combineCaptured selection lookup admit row := rfl

/-- Combiner-selection errors prevent raw lookup and preserve the exact error. -/
theorem combineDirect_selection_error (error : Error) (lookup : Except Error Fragments)
    (admit) (row : Row) :
    combineDirect (.error error : Except Error (Fragments → Row → Except Error Result)) lookup admit row =
      .error error := rfl

/-- Lookup errors precede procedure admission, even when that admission refuses. -/
theorem combineDirect_lookup_error (combine : Fragments → Row → Except Error Result)
    (error : Error) (admit) (row : Row) :
    combineDirect (.ok combine : Except Error (Fragments → Row → Except Error Result)) (.error error) admit row = .error error := rfl

/-- Procedure admission errors cannot execute a method or trigger another clause. -/
theorem combineDirect_admission_error (combine : Fragments → Row → Except Error Result)
    (fragments : Fragments) (error : Error) (row : Row) :
    combineDirect (.ok combine : Except Error (Fragments → Row → Except Error Result)) (.ok fragments) (fun _ => .error error) row = .error error := rfl

/-- Successful transport preserves arbitrary multiple-result representations. -/
theorem combineDirect_success (combine : Fragments → Row → Except Error Result)
    (fragments : Fragments) (row : Row) :
    combineDirect (.ok combine : Except Error (Fragments → Row → Except Error Result)) (.ok fragments) (fun _ => .ok ()) row = combine fragments row := rfl

/-- Explicit source-level transport counts, excluding shared lookup, admission,
combiner work and the runtime representation of the supplied row cells. These
are a model, not a claim about allocations after either compiler optimizes. -/
structure CombinationWork where
  rowCells : Nat
  relayClosures : Nat
  relayCalls : Nat
  deriving Repr, DecidableEq

/-- The historical bridge transports the same row through one temporary relay. -/
def capturedWork (width : Nat) : CombinationWork := ⟨width, 1, 1⟩
/-- Core list/apply lowering transports the row without that temporary relay. -/
def directWork (width : Nat) : CombinationWork := ⟨width, 0, 0⟩
/-- Any nonnegative source-operation prices can be supplied by an implementation. -/
def CombinationWork.charge (work : CombinationWork) (cell closure call : Nat) : Nat :=
  work.rowCells * cell + work.relayClosures * closure + work.relayCalls * call
/-- The model charges the old bridge exactly one closure and relay call more. -/
theorem combination_charge_difference (width cell closure call : Nat) :
    (capturedWork width).charge cell closure call =
      (directWork width).charge cell closure call + closure + call := by
  simp [capturedWork, directWork, CombinationWork.charge]
/-- Eliminating the relay never increases this model's weighted transport cost. -/
theorem combination_charge_le (width cell closure call : Nat) :
    (directWork width).charge cell closure call ≤ (capturedWork width).charge cell closure call := by
  rw [combination_charge_difference]
  omega
/-- The number of encoded row cells is unchanged for every width, including zero. -/
theorem combination_row_cells (width : Nat) :
    (directWork width).rowCells = (capturedWork width).rowCells := rfl
/-- Fixed macro prefix over a copied rest spine. In Scheme, append with an empty
last argument supplies the private spine; this pure model records values only.
Mutable identity and Gerbil allocation require the separate Gerbil controls. -/
def assembleRow (fixed rest : List Value) : List Value :=
  fixed.foldr List.cons (rest.map id)

/-- Fixed-prefix construction preserves the complete apply/list row, including
literal keyword/false payloads represented by the chosen Value type. -/
theorem assembleRow_eq (fixed rest : List Value) :
    assembleRow fixed rest = fixed ++ rest := by
  induction fixed with
  | nil => simp [assembleRow]
  | cons head tail ih => simp [assembleRow] at ih ⊢

/-- Every fixed and rest token occurs once; copying adds no logical arguments. -/
theorem assembleRow_length (fixed rest : List Value) :
    (assembleRow fixed rest).length = fixed.length + rest.length := by
  rw [assembleRow_eq, List.length_append]

/-- Two statically emitted fixed segments compose without reinterpreting the
rest or changing argument order. No host default or contract is re-evaluated. -/
theorem assembleRow_compose (outer inner rest : List Value) :
    assembleRow outer (assembleRow inner rest) = assembleRow (outer ++ inner) rest := by
  simp only [assembleRow_eq, List.append_assoc]

/-- Substitution into arbitrary effectful selection/lookup/admission preserves
their failure order and the combiner's complete result, not just row length. -/
theorem combineDirect_assembled [Monad M]
    (selection : M (Fragments → List Value → M Result)) (lookup : M Fragments)
    (admit : (Fragments → List Value → M Result) → M Unit) (fixed rest : List Value) :
    combineDirect selection lookup admit (assembleRow fixed rest) =
      combineDirect selection lookup admit (fixed ++ rest) := by
  rw [assembleRow_eq]

/-- Parameterized implementation budget: equal logical row cells, but distinct
prices for apply/list redistribution and copying the rest with append. Prices
must come from the implementation; deleting an apply is not free tail copying. -/
def rowAssemblyCharge (width cell applyCall copyRest : Nat) (usesApply : Bool) : Nat :=
  width * cell + if usesApply then applyCall else copyRest

/-- Shared row cost cancels; the removed dispatcher and new copy retain their
own prices. This equality asserts no unconditional implementation speedup. -/
theorem rowAssemblyCharge_difference (width cell applyCall copyRest : Nat) :
    rowAssemblyCharge width cell applyCall copyRest true + copyRest =
      rowAssemblyCharge width cell applyCall copyRest false + applyCall := by
  simp [rowAssemblyCharge]; omega

/-- A transport improvement requires the copying route to cost no more than
apply/list; logical equality alone cannot establish this implementation premise. -/
theorem rowAssemblyCharge_threshold (width cell applyCall copyRest : Nat) :
    rowAssemblyCharge width cell applyCall copyRest false ≤
      rowAssemblyCharge width cell applyCall copyRest true ↔ copyRest ≤ applyCall := by
  simp [rowAssemblyCharge]

/-- Complete-workflow admission retains setup and GC history explicitly. Even a
cheaper transport can lose when construction or GC costs increase. These are
supplied finite cost units, not a model of Gambit's collector or CPU scheduler. -/
theorem rowAssemblyCharge_workflow (width cell applyCall copyRest
    oldSetup newSetup oldGC newGC : Nat) :
    newSetup + rowAssemblyCharge width cell applyCall copyRest false + newGC ≤
      oldSetup + rowAssemblyCharge width cell applyCall copyRest true + oldGC ↔
    newSetup + copyRest + newGC ≤ oldSetup + applyCall + oldGC := by
  simp only [rowAssemblyCharge, Bool.false_eq_true, ↓reduceIte]
  omega

/-- Standard effectful Reader bind with an environment-independent continuation.
The continuation constructs a Reader on every invocation, then runs it at the
same context. This models the old summary workflow, not arbitrary FUN overrides. -/
def nestedObservation [Monad M] (source : Context → M Value)
    (finish : Value → M Result) : Context → M Result :=
  fun context => source context >>= fun value => (fun (_ : Context) => finish value) context

/-- The standard Reader map/Kleisli composition needs no intermediate Reader.
Effects inside finish include reflection, generic calls and post-success review. -/
def fusedObservation [Monad M] (source : Context → M Value)
    (finish : Value → M Result) : Context → M Result :=
  fun context => source context >>= finish

/-- Fusion is extensional equality for arbitrary source/continuation effects.
Environment independence is explicit in finish's type; a continuation that reads
the context again, or a modified FUN implementation, is outside this rewrite. -/
theorem observation_fusion [Monad M] (source : Context → M Value)
    (finish : Value → M Result) :
    nestedObservation source finish = fusedObservation source finish := rfl

/-- Source refusal prevents every reflection/generic/review effect in finish. -/
theorem fusedObservation_refused (source : Context → Except Error Value)
    (finish : Value → Except Error Result) (context : Context) (error : Error)
    (refused : source context = .error error) :
    fusedObservation source finish context = .error error := by
  simp [fusedObservation, refused, bind, Except.bind]

/-- Current source values flow into the complete continuation on every retry;
neither a prior receiver nor a successful result is retained by fusion. -/
theorem fusedObservation_current (source : Context → Except Error Value)
    (finish : Value → Except Error Result) (context : Context) (value : Value)
    (ready : source context = .ok value) :
    fusedObservation source finish context = finish value := by
  simp [fusedObservation, ready, bind, Except.bind]

/-- Finite supplied prices distinguish dynamic map construction from new
completion work; setup and collector history are independent complete-run terms.
These are source budgets, not Gambit allocation or wall-clock predictions. -/
def observationCharge (setup calls common completion gc : Nat) : Nat :=
  setup + calls * (common + completion) + gc

/-- Fusion wins the complete supplied budget exactly under this threshold.
A deleted intermediate Reader alone cannot justify an end-to-end speed claim. -/
theorem observationCharge_threshold (oldSetup newSetup calls common dynamicMap
    fusedCompletion oldGC newGC : Nat) :
    observationCharge newSetup calls common fusedCompletion newGC ≤
      observationCharge oldSetup calls common dynamicMap oldGC ↔
    newSetup + calls * fusedCompletion + newGC ≤
      oldSetup + calls * dynamicMap + oldGC := by
  simp only [observationCharge, Nat.mul_add]
  omega


/-- Type-bearing slots of one ordinary Function descriptor. Required-key order is
metadata; optional defaults and host callback behavior are deliberately absent. -/
structure TypedSignature (Key Ty : Type) where
  outputs : List Ty
  inputs : List Ty
  optional : List Ty := []
  keywords : List (Key × Ty) := []
  requiredKeywords : List Key := []
  rest : Option Ty := none
  deriving Repr, DecidableEq

/-- Project only the finite supplied-call language used before any validator. -/
def TypedSignature.shape (signature : TypedSignature Key Ty) : Signature Key :=
  ⟨signature.inputs.length, signature.optional.length, signature.rest.isSome,
    signature.keywords.map Prod.fst, signature.requiredKeywords⟩

/-- Specialization visits every Type slot, preserving literal keys and clause order. -/
def TypedSignature.mapTypes (substitute : A → B) (signature : TypedSignature Key A) : TypedSignature Key B :=
  ⟨signature.outputs.map substitute, signature.inputs.map substitute,
    signature.optional.map substitute, signature.keywords.map (fun (key, ty) => (key, substitute ty)),
    signature.requiredKeywords, signature.rest.map substitute⟩

/-- Literal option names are separate from Type parameters and keyword labels. -/
inductive SignatureOptionKind where
  | optional | keywords | requiredKeywords | rest
  deriving Repr, DecidableEq
/-- Admitted Function metadata contains Types, not host default expressions. -/
inductive SignatureOption (Key Ty : Type) where
  | optional (types : List Ty)
  | keywords (entries : List (Key × Ty))
  | requiredKeywords (keys : List Key)
  | rest (type : Option Ty)
  deriving Repr
/-- Duplicate-name admission uses names alone, never Type recognizer equality. -/
def signatureOptionKind : SignatureOption Key Ty → SignatureOptionKind
  | .optional _ => .optional
  | .keywords _ => .keywords
  | .requiredKeywords _ => .requiredKeywords
  | .rest _ => .rest
/-- Bind one metadata field without visiting any supplied argument or default. -/
def applySignatureOption (option : SignatureOption Key Ty) (signature : TypedSignature Key Ty) : TypedSignature Key Ty :=
  match option with
  | .optional types => {signature with optional := types}
  | .keywords entries => {signature with keywords := entries}
  | .requiredKeywords keys => {signature with requiredKeywords := keys}
  | .rest type => {signature with rest := type}
/-- Core association lookup projects one effective schema, starting with the
constructor's literal empty/false defaults. Duplicate names are checked separately. -/
def projectSignatureOptions (outputs inputs : List Ty) (options : List (SignatureOption Key Ty)) : TypedSignature Key Ty :=
  options.foldr applySignatureOption ⟨outputs, inputs, [], [], [], none⟩
/-- Options cannot bind outputs or required inputs; those are positional schema
fields throughout projection, normalization and later Type specialization. -/
theorem projectSignatureOptions_header (outputs inputs : List Ty) (options : List (SignatureOption Key Ty)) :
    (projectSignatureOptions outputs inputs options).outputs = outputs ∧
      (projectSignatureOptions outputs inputs options).inputs = inputs := by
  induction options with
  | nil => exact ⟨rfl, rfl⟩
  | cons head tail ih =>
    cases head <;> simpa only [projectSignatureOptions, List.foldr_cons, applySignatureOption] using ih

/-- No duplicate metadata can be silently erased into an accepted signature. Raw
unknown names and malformed payloads remain source-language admission obligations. -/
def readSignatureOptions (outputs inputs : List Ty) (options : List (SignatureOption Key Ty)) : Option (TypedSignature Key Ty) :=
  if (options.map signatureOptionKind).Nodup then some (projectSignatureOptions outputs inputs options) else none
/-- Match Function's fixed metadata order and omission of the all-default tail.
Keyword/case/field order within payloads is never sorted, merged or widened. -/
def canonicalSignatureOptions (signature : TypedSignature Key Ty) : List (SignatureOption Key Ty) :=
  if signature.optional.isEmpty && signature.keywords.isEmpty && signature.requiredKeywords.isEmpty && signature.rest.isNone then []
  else [.optional signature.optional, .keywords signature.keywords, .requiredKeywords signature.requiredKeywords, .rest signature.rest]
/-- Literal metadata aliases normalize through the same effective schema. -/
def normalizeSignatureOptions (outputs inputs : List Ty) (options : List (SignatureOption Key Ty)) :=
  canonicalSignatureOptions (projectSignatureOptions outputs inputs options)
/-- Reordering two different options preserves every field, even with rest and
multiple output Types. Duplicate assignments are intentionally excluded. -/
theorem applySignatureOption_commute (first second : SignatureOption Key Ty) (signature : TypedSignature Key Ty)
    (different : signatureOptionKind first ≠ signatureOptionKind second) :
    applySignatureOption first (applySignatureOption second signature) =
      applySignatureOption second (applySignatureOption first signature) := by
  cases first <;> cases second <;> simp_all [signatureOptionKind, applySignatureOption]
/-- Any admitted option permutation gives the same effective signature; no
ordering premise is made about user validators inside its Type payloads. -/
theorem signatureOptions_fold_perm (first second : List (SignatureOption Key Ty))
    (permutation : first.Perm second) (signature : TypedSignature Key Ty)
    (unique : (first.map signatureOptionKind).Nodup) :
    first.foldr applySignatureOption signature = second.foldr applySignatureOption signature := by
  induction permutation generalizing signature with
  | nil => rfl
  | cons head permutation ih =>
    have tail := (List.nodup_cons.mp unique).2
    simpa only [List.foldr_cons] using congrArg (applySignatureOption head) (ih signature tail)
  | swap first second rest =>
    have distinct : signatureOptionKind second ≠ signatureOptionKind first := by
      have absent := (List.nodup_cons.mp unique).1
      intro same
      exact absent (List.mem_cons.mpr (.inl same))
    exact applySignatureOption_commute second first _ distinct
  | trans left right ihLeft ihRight =>
    exact (ihLeft signature unique).trans
      (ihRight signature ((left.map signatureOptionKind).nodup_iff.mp unique))
/-- Duplicate checks and effective fields both ignore only admitted option order. -/
theorem readSignatureOptions_perm (outputs inputs : List Ty) (first second : List (SignatureOption Key Ty))
    (permutation : first.Perm second) :
    readSignatureOptions outputs inputs first = readSignatureOptions outputs inputs second := by
  have distinct := (permutation.map signatureOptionKind).nodup_iff
  by_cases unique : (first.map signatureOptionKind).Nodup
  · have right := distinct.mp unique
    simp only [readSignatureOptions, unique, right, ↓reduceIte, projectSignatureOptions]
    exact congrArg some (signatureOptions_fold_perm first second permutation ⟨outputs, inputs, [], [], [], none⟩ unique)
  · have right : ¬(second.map signatureOptionKind).Nodup := fun h => unique (distinct.mpr h)
    simp only [readSignatureOptions, unique, right, ↓reduceIte]

/-- Constructor-default omission and explicit defaults are observationally equal. -/
theorem projectSignatureOptions_canonical (signature : TypedSignature Key Ty) :
    projectSignatureOptions signature.outputs signature.inputs (canonicalSignatureOptions signature) = signature := by
  cases signature with
  | mk outputs inputs optional keywords required rest =>
    cases optional <;> cases keywords <;> cases required <;> cases rest <;> rfl
/-- The canonical tail is always duplicate-free, whether empty or complete. -/
theorem canonicalSignatureOptions_unique (signature : TypedSignature Key Ty) :
    ((canonicalSignatureOptions signature).map signatureOptionKind).Nodup := by
  unfold canonicalSignatureOptions
  split <;> simp [signatureOptionKind]
/-- Canonicalization changes no effective signature before a constructor runs. -/
theorem readSignatureOptions_canonical (signature : TypedSignature Key Ty) :
    readSignatureOptions signature.outputs signature.inputs (canonicalSignatureOptions signature) = some signature := by
  simp only [readSignatureOptions, canonicalSignatureOptions_unique, ↓reduceIte, projectSignatureOptions_canonical]
/-- The entire normalization step preserves an admitted projection. -/
theorem normalizeSignatureOptions_sound (outputs inputs : List Ty) (options : List (SignatureOption Key Ty))
    (signature : TypedSignature Key Ty) (accepted : readSignatureOptions outputs inputs options = some signature) :
    readSignatureOptions outputs inputs (normalizeSignatureOptions outputs inputs options) = some signature := by
  unfold readSignatureOptions at accepted
  split at accepted
  · have same := Option.some.inj accepted
    rw [←same]
    have header := projectSignatureOptions_header outputs inputs options
    simpa only [normalizeSignatureOptions, header.1, header.2] using
      readSignatureOptions_canonical (projectSignatureOptions outputs inputs options)
  · simp at accepted
/-- Repeated capture/normalization is stable rather than accumulating defaults. -/
theorem normalizeSignatureOptions_idempotent (outputs inputs : List Ty) (options : List (SignatureOption Key Ty)) :
    normalizeSignatureOptions outputs inputs (normalizeSignatureOptions outputs inputs options) =
      normalizeSignatureOptions outputs inputs options := by
  simp only [normalizeSignatureOptions]
  have same := projectSignatureOptions_canonical (projectSignatureOptions outputs inputs options)
  have header := projectSignatureOptions_header outputs inputs options
  simpa only [header.1, header.2] using congrArg canonicalSignatureOptions same
/-- Duplicate metadata remains refusal, rather than a normalized successful alias. -/
theorem readSignatureOptions_duplicate (outputs inputs : List Ty) (options : List (SignatureOption Key Ty))
    (duplicate : ¬(options.map signatureOptionKind).Nodup) : readSignatureOptions outputs inputs options = none := by
  simp [readSignatureOptions, duplicate]
/-- Specialization visits Type payloads without changing option or keyword names. -/
def mapSignatureOption (substitute : A → B) : SignatureOption Key A → SignatureOption Key B
  | .optional types => .optional (types.map substitute)
  | .keywords entries => .keywords (entries.map (fun (key, type) => (key, substitute type)))
  | .requiredKeywords keys => .requiredKeywords keys
  | .rest type => .rest (type.map substitute)
/-- One metadata binding commutes with prefix/residual Type substitution. -/
theorem applySignatureOption_map (substitute : A → B) (option : SignatureOption Key A) (signature : TypedSignature Key A) :
    applySignatureOption (mapSignatureOption substitute option) (signature.mapTypes substitute) =
      (applySignatureOption option signature).mapTypes substitute := by
  cases option <;> cases signature <;> rfl
/-- The effective schema is the same whether bound before or after all Type slots
are substituted. Missing values and literal required-key metadata remain absent. -/
theorem projectSignatureOptions_map (substitute : A → B) (outputs inputs : List A) (options : List (SignatureOption Key A)) :
    projectSignatureOptions (outputs.map substitute) (inputs.map substitute) (options.map (mapSignatureOption substitute)) =
      (projectSignatureOptions outputs inputs options).mapTypes substitute := by
  have fold (rest : List (SignatureOption Key A)) (signature : TypedSignature Key A) :
      (rest.map (mapSignatureOption substitute)).foldr applySignatureOption (signature.mapTypes substitute) =
        (rest.foldr applySignatureOption signature).mapTypes substitute := by
    induction rest with
    | nil => rfl
    | cons head tail ih => simp only [List.map_cons, List.foldr_cons, ih, applySignatureOption_map]
  exact fold options ⟨outputs, inputs, [], [], [], none⟩

/-- Substitution preserves option names, so it cannot repair duplicate metadata. -/
theorem mapSignatureOption_kind (substitute : A → B) (option : SignatureOption Key A) :
    signatureOptionKind (mapSignatureOption substitute option) = signatureOptionKind option := by
  cases option <;> rfl
/-- One admitted schema binding serves both syntax specialization and descriptor
construction; false admission stays false and no callback/default is evaluated. -/
theorem readSignatureOptions_map (substitute : A → B) (outputs inputs : List A) (options : List (SignatureOption Key A)) :
    readSignatureOptions (outputs.map substitute) (inputs.map substitute) (options.map (mapSignatureOption substitute)) =
      (readSignatureOptions outputs inputs options).map (TypedSignature.mapTypes substitute) := by
  have kinds : (options.map (mapSignatureOption substitute)).map signatureOptionKind = options.map signatureOptionKind := by
    simp only [List.map_map, Function.comp_def, mapSignatureOption_kind]
  simp only [readSignatureOptions, kinds]
  split <;> simp_all only [Option.map_some, Option.map_none, projectSignatureOptions_map]
/-- Canonical semantic candidates are deduplicated before complete inference.
A genuinely different candidate is not merged by this alias-only law. -/
theorem infer_signature_aliases [DecidableEq Key] [DecidableEq Ty]
    (outputs inputs : List Ty) (first second : List (SignatureOption Key Ty))
    (aliases : projectSignatureOptions outputs inputs first = projectSignatureOptions outputs inputs second) :
    PrototypeTypes.infer (fun _ => true)
      ([projectSignatureOptions outputs inputs first, projectSignatureOptions outputs inputs second].eraseDups) =
        .unique (projectSignatureOptions outputs inputs first) := by
  rw [←aliases]
  simp [PrototypeTypes.infer, List.eraseDups_cons]

/-- Binding type parameters cannot change which supplied argument shapes match. -/
@[simp] theorem TypedSignature.mapTypes_shape (substitute : A → B) (signature : TypedSignature Key A) :
    (signature.mapTypes substitute).shape = signature.shape := by
  cases signature with
  | mk outputs inputs optional keywords required rest =>
    cases rest <;> simp [TypedSignature.mapTypes, TypedSignature.shape, List.map_map, Function.comp_def]

/-- Mapping a prefix and residual binding equals one composed Type substitution. -/
theorem TypedSignature.mapTypes_compose (first : A → B) (second : B → C)
    (signature : TypedSignature Key A) :
    (signature.mapTypes first).mapTypes second = signature.mapTypes (second ∘ first) := by
  cases signature
  simp [TypedSignature.mapTypes, List.map_map, Option.map_map, Function.comp_def]

/-- Case-lambda structural selection is unchanged after all Type substitutions.
No value-directed fallback or case permutation is licensed by inference. -/
theorem specialize_selection [DecidableEq Key] (clauses : List (TypedSignature Key A))
    (substitute : A → B) (call : Call Key Value) :
    select ((clauses.map (TypedSignature.mapTypes substitute)).map TypedSignature.shape) call =
      select (clauses.map TypedSignature.shape) call := by
  simp [List.map_map, Function.comp_def]

/-- Flatten contravariant positions only, retaining required/optional/key/rest order. -/
def TypedSignature.arguments (signature : TypedSignature Key Ty) : List Ty :=
  signature.inputs ++ signature.optional ++ signature.keywords.map Prod.snd ++ signature.rest.toList

/-- Decidable conservative replacement: equal call shape, covariant exact results,
contravariant supplied argument Types. Arbitrary case-language coverage is absent. -/
def replaces [DecidableEq Key] (fuel : Nat)
    (source target : TypedSignature Key PrototypeTypes.Ty) : Bool :=
  decide (source.shape = target.shape) &&
  PrototypeTypes.all₂ (PrototypeTypes.check fuel) source.outputs target.outputs &&
  PrototypeTypes.all₂ (PrototypeTypes.check fuel) target.arguments source.arguments

/-- Every accepted rich replacement has genuine structural subtype derivations
in each variance direction, including exact multiple-return cardinality. -/
theorem replaces_sound [DecidableEq Key] (fuel : Nat)
    (source target : TypedSignature Key PrototypeTypes.Ty) (accepted : replaces fuel source target = true) :
    source.shape = target.shape ∧
    PrototypeTypes.RelList PrototypeTypes.Subtype source.outputs target.outputs ∧
    PrototypeTypes.RelList PrototypeTypes.Subtype target.arguments source.arguments := by
  simp only [replaces, Bool.and_eq_true, decide_eq_true_eq] at accepted
  exact ⟨accepted.1.1,
    PrototypeTypes.all₂_sound _ (PrototypeTypes.check_sound fuel) _ _ accepted.1.2,
    PrototypeTypes.all₂_sound _ (PrototypeTypes.check_sound fuel) _ _ accepted.2⟩

/-- Check count BEFORE zipping Type/value rows; then retain every normalized value.
A failed check returns no cache owner or partial output row. -/
def finishValues (outputs : List Ty) (results : List Value) (owner : Owner)
    (arityError : Error) (check : Ty → Value → Except Error Value) : Except Error (List Value × Owner) :=
  if outputs.length = results.length then
    (Validation.traverse (fun pair => check pair.1 pair.2) (outputs.zip results)).map (·, owner)
  else .error arityError

/-- Too many or too few user values cannot be mistaken for a cache successor. -/
theorem finishValues_wrong_count (outputs : List Ty) (results : List Value) (owner : Owner)
    (arityError : Error) (check) (different : outputs.length ≠ results.length) :
    finishValues outputs results owner arityError check = .error arityError := by
  simp [finishValues, different]

/-- Zero user values still transport exactly one explicit owner, never a false user value. -/
theorem finishValues_zero (owner : Owner) (arityError : Error) (check : Ty → Value → Except Error Value) :
    finishValues [] [] owner arityError check = .ok ([], owner) := rfl

/-- A successful result retains the exact successor and the declared output count.
The theorem is conditional on injected validators, not a proof of host procedures. -/
theorem finishValues_success (outputs : List Ty) (results checked : List Value)
    (owner next : Owner) (arityError : Error) (check)
    (success : finishValues outputs results owner arityError check = .ok (checked, next)) :
    next = owner ∧ checked.length = outputs.length := by
  by_cases same : outputs.length = results.length
  · simp only [finishValues, same, ↓reduceIte] at success
    cases run : Validation.traverse (fun pair => check pair.1 pair.2) (outputs.zip results) with
    | error cause => simp [run, Except.map] at success
    | ok row =>
      simp [run, Except.map] at success
      obtain ⟨rfl, rfl⟩ := success
      exact ⟨rfl, by simpa [List.length_zip, same] using supplied_length _ _ _ run⟩
  · simp [finishValues, same] at success


/-- The complete declared call selects one ordered clause, normalizes supplied
arguments, runs one body, and only then validates all results and transfers owner. -/
def invokeValues [DecidableEq Key] (clauses : List (TypedSignature Key Ty))
    (call : Call Key Value) (shapeError countError : Error)
    (normalize : TypedSignature Key Ty → Call Key Value → Except Error (Call Key Value))
    (body : Call Key Value → Except Error (List Value × Owner))
    (check : Ty → Value → Except Error Value) : Except Error (List Value × Owner) :=
  match clauses.find? (fun clause => accepts clause.shape call) with
  | none => .error shapeError
  | some signature => (normalize signature call).bind fun checked =>
    (body checked).bind fun (results, owner) => finishValues signature.outputs results owner countError check

/-- Refusing the selected input Types cannot enter the body or a later clause. -/
theorem invokeValues_type_error [DecidableEq Key] (clauses : List (TypedSignature Key Ty))
    (call : Call Key Value) (shapeError countError error : Error) (normalize) (body : Call Key Value → Except Error (List Value × Owner)) (check signature)
    (selected : clauses.find? (fun clause => accepts clause.shape call) = some signature)
    (refused : normalize signature call = .error error) :
    invokeValues clauses call shapeError countError normalize body check = .error error := by
  simp [invokeValues, selected, refused, Except.bind]

/-- Body errors keep their original cause and cannot become output/overload errors. -/
theorem invokeValues_body_error [DecidableEq Key] (clauses : List (TypedSignature Key Ty))
    (call : Call Key Value) (shapeError countError error : Error) (normalize) (body : Call Key Value → Except Error (List Value × Owner)) (check signature checked)
    (selected : clauses.find? (fun clause => accepts clause.shape call) = some signature)
    (normalized : normalize signature call = .ok checked) (refused : body checked = .error error) :
    invokeValues clauses call shapeError countError normalize body check = .error error := by
  simp [invokeValues, selected, normalized, refused, Except.bind]

/-- A selected body's wrong output count refuses without returning its successor,
even when a later clause would accept that output count. External effects remain. -/
theorem invokeValues_wrong_count [DecidableEq Key] (clauses : List (TypedSignature Key Ty))
    (call : Call Key Value) (shapeError countError : Error) (normalize) (body : Call Key Value → Except Error (List Value × Owner)) (check signature checked results) (owner : Owner)
    (selected : clauses.find? (fun clause => accepts clause.shape call) = some signature)
    (normalized : normalize signature call = .ok checked) (returned : body checked = .ok (results, owner))
    (different : signature.outputs.length ≠ results.length) :
    invokeValues clauses call shapeError countError normalize body check = .error countError := by
  simp [invokeValues, selected, normalized, returned, Except.bind, finishValues, different]


/-- Required/optional positions use their declared Type; later positions use rest.
Defaults have no Type occurrence unless a value was actually supplied. -/
def TypedSignature.positionType (signature : TypedSignature Key Ty) (index : Nat) : Option Ty :=
  (signature.inputs ++ signature.optional)[index]?.or signature.rest

/-- Successful standard mapM cannot silently discard a supplied argument. -/
theorem optionMap_length (check : Input → Option Output) (inputs : List Input) (outputs : List Output)
    (success : inputs.mapM check = some outputs) : outputs.length = inputs.length := by
  induction inputs generalizing outputs with
  | nil => simp at success; subst outputs; rfl
  | cons input rest ih =>
    simp only [List.mapM_cons] at success
    cases head : check input with
    | none => simp [head] at success
    | some value =>
      cases tail : rest.mapM check with
      | none => simp [head, tail] at success
      | some values =>
        simp [head, tail] at success
        subst outputs
        simp [ih values tail]

/-- Supplied argument constraints share the existing shape admission and literal
key lookup. Actual Types are ground; formal Types may refer to scheme variables. -/
def inputConstraints [DecidableEq Key] (signature : TypedSignature Key PrototypeTypes.Expr)
    (call : Call Key PrototypeTypes.Ty) : Option (List (PrototypeTypes.Expr × PrototypeTypes.Expr)) :=
  if accepts signature.shape call then do
    let positionals ← call.positional.zipIdx.mapM fun (actual, index) =>
      (signature.positionType index).map fun formal => (.ground actual, formal)
    let keywords ← call.keywords.mapM fun (key, actual) =>
      (RowTypes.lookup signature.keywords key).map fun formal => (.ground actual, formal)
    return positionals ++ keywords
  else none

/-- A structurally invalid call cannot generate a misleading constraint prefix. -/
theorem inputConstraints_shape_error [DecidableEq Key] (signature : TypedSignature Key PrototypeTypes.Expr)
    (call : Call Key PrototypeTypes.Ty) (refused : accepts signature.shape call = false) :
    inputConstraints signature call = none := by simp [inputConstraints, refused]

/-- All supplied positional and keyword arguments produce one constraint each. -/
theorem inputConstraints_length [DecidableEq Key] (signature : TypedSignature Key PrototypeTypes.Expr)
    (call : Call Key PrototypeTypes.Ty) (queries)
    (success : inputConstraints signature call = some queries) :
    queries.length = call.positional.length + call.keywords.length := by
  unfold inputConstraints at success
  split at success
  · rename_i shape
    cases positions : call.positional.zipIdx.mapM (fun (actual, index) =>
        (signature.positionType index).map fun formal => (PrototypeTypes.Expr.ground actual, formal)) with
    | none => simp [positions] at success
    | some ps =>
      cases keys : call.keywords.mapM (fun (key, actual) =>
          (RowTypes.lookup signature.keywords key).map fun formal => (PrototypeTypes.Expr.ground actual, formal)) with
      | none => simp [positions, keys] at success
      | some ks =>
        simp [positions, keys] at success
        subst queries
        simp only [List.length_append, optionMap_length _ _ _ positions,
          optionMap_length _ _ _ keys, List.length_zipIdx]
  · simp at success

/-- Expected results reverse the subtype direction. None makes no obligation;
some [] requires exactly zero user values, independently of the cache owner. -/
def outputConstraints (outputs : List PrototypeTypes.Expr) (expected : Option (List PrototypeTypes.Ty)) :
    Option (List (PrototypeTypes.Expr × PrototypeTypes.Expr)) :=
  match expected with
  | none => some []
  | some values => if outputs.length = values.length then
      some (outputs.zip (values.map PrototypeTypes.Expr.ground)) else none

/-- Zero requested results are not interchangeable with an omitted obligation. -/
theorem outputConstraints_wrong_count (outputs : List PrototypeTypes.Expr) (expected : List PrototypeTypes.Ty)
    (different : outputs.length ≠ expected.length) : outputConstraints outputs (some expected) = none := by
  simp [outputConstraints, different]

/-- Inference commits to the same first structural clause as invocation. Input
or output failure cannot make a later clause participate in candidate selection. -/
def callConstraints [DecidableEq Key] (clauses : List (TypedSignature Key PrototypeTypes.Expr))
    (call : Call Key PrototypeTypes.Ty) (expected : Option (List PrototypeTypes.Ty)) :
    Option (List (PrototypeTypes.Expr × PrototypeTypes.Expr)) := do
  let signature ← clauses.find? (fun clause => accepts clause.shape call)
  let inputs ← inputConstraints signature call
  let outputs ← outputConstraints signature.outputs expected
  pure (inputs ++ outputs)

/-- The first matching case fixes BOTH input and output obligations. -/
theorem callConstraints_first [DecidableEq Key] (head : TypedSignature Key PrototypeTypes.Expr) (tail)
    (call : Call Key PrototypeTypes.Ty) (expected)
    (selected : accepts head.shape call = true) :
    callConstraints (head :: tail) call expected = (do
      let inputs ← inputConstraints head call
      let outputs ← outputConstraints head.outputs expected
      pure (inputs ++ outputs)) := by simp [callConstraints, List.find?, selected]

/-- Ordered named observations refer to one signature catalog and one assignment.
Lookup is the existing finite row operation; Scheme projects explicit Object paths. -/
def jointConstraints [DecidableEq Path] [DecidableEq Key]
    (catalog : List (Path × List (TypedSignature Key PrototypeTypes.Expr))) :
    List (Path × Call Key PrototypeTypes.Ty × Option (List PrototypeTypes.Ty)) →
      Option (List (PrototypeTypes.Expr × PrototypeTypes.Expr))
  | [] => some []
  | (name, call, expected) :: rest => do
      let clauses ← RowTypes.lookup catalog name
      let queries ← callConstraints clauses call expected
      let tail ← jointConstraints catalog rest
      pure (queries ++ tail)

/-- An absent named signature stops the whole collection before any accepted tail. -/
theorem jointConstraints_missing [DecidableEq Path] [DecidableEq Key]
    (catalog : List (Path × List (TypedSignature Key PrototypeTypes.Expr))) (name call expected rest)
    (missing : RowTypes.lookup catalog name = none) :
    jointConstraints catalog ((name, call, expected) :: rest) = none := by
  simp [jointConstraints, missing]

/-- Successfully collected sibling observations preserve the complete head and
complete tail; no separately admissible observation can be silently omitted. -/
theorem jointConstraints_cons [DecidableEq Path] [DecidableEq Key]
    (catalog : List (Path × List (TypedSignature Key PrototypeTypes.Expr))) (name call expected rest clauses front tail)
    (found : RowTypes.lookup catalog name = some clauses)
    (head : callConstraints clauses call expected = some front)
    (remaining : jointConstraints catalog rest = some tail) :
    jointConstraints catalog ((name, call, expected) :: rest) = some (front ++ tail) := by
  simp [jointConstraints, found, head, remaining]


/-- A refused later observation discards the entire collected prefix. -/
theorem jointConstraints_tail_error [DecidableEq Path] [DecidableEq Key]
    (catalog : List (Path × List (TypedSignature Key PrototypeTypes.Expr))) (name call expected rest clauses)
    (found : RowTypes.lookup catalog name = some clauses)
    (refused : jointConstraints catalog rest = none) :
    jointConstraints catalog ((name, call, expected) :: rest) = none := by
  simp [jointConstraints, found, refused]

/-- Each requested result produces exactly one reversed obligation; zip cannot
truncate an expected row because count admission precedes construction. -/
theorem outputConstraints_length (outputs : List PrototypeTypes.Expr) (expected : List PrototypeTypes.Ty)
    (queries) (success : outputConstraints outputs (some expected) = some queries) :
    queries.length = expected.length := by
  by_cases same : outputs.length = expected.length
  · have row : outputs.zip (expected.map PrototypeTypes.Expr.ground) = queries := by
      simpa [outputConstraints, same] using success
    subst queries
    simp [List.length_zip, same]
  · simp [outputConstraints, same] at success


/-- Value projection of constructor-owned declaration rows. Type tokens and rest
retain their supplied identities; all list fields and keyword binding pairs are
copied. Lean lists have value semantics: actual Scheme nonaliasing is a separate
runtime obligation, not a consequence of this equality model. -/
def TypedSignature.capture (signature : TypedSignature Key Ty) : TypedSignature Key Ty :=
  ⟨signature.outputs.map id, signature.inputs.map id, signature.optional.map id,
    signature.keywords.map (fun (key, ty) => (key, ty)),
    signature.requiredKeywords.map id, signature.rest⟩

/-- Capturing topology changes none of the declared Types, literal keys or counts. -/
@[simp] theorem TypedSignature.capture_eq (signature : TypedSignature Key Ty) :
    signature.capture = signature := by
  cases signature
  simp [TypedSignature.capture]

/-- Capturing a declaration commutes with existing parameter specialization. -/
theorem TypedSignature.capture_mapTypes (substitute : A → B) (signature : TypedSignature Key A) :
    (signature.capture).mapTypes substitute = (signature.mapTypes substitute).capture := by simp

/-- Ordered case selection keeps the first matching ORIGINAL clause after capture. -/
theorem capture_selection [DecidableEq Key] (clauses : List (TypedSignature Key Ty)) (call : Call Key Value) :
    select ((clauses.map TypedSignature.capture).map TypedSignature.shape) call =
      select (clauses.map TypedSignature.shape) call := by
  simp [List.map_map, Function.comp_def]

/-- A missing declared required key is structural refusal, irrespective of the
supplied values or any later host default/body behavior. -/
theorem accepts_missing_required [DecidableEq Key] (signature : Signature Key)
    (call : Call Key Value) (key : Key) (required : key ∈ signature.requiredKeywords)
    (missing : key ∉ call.keywords.map Prod.fst) : accepts signature call = false := by
  cases accepted : accepts signature call with
  | false => rfl
  | true =>
    have complete : signature.requiredKeywords.all (fun key => decide (key ∈ call.keywords.map Prod.fst)) = true := by
      simp only [accepts, Bool.and_eq_true] at accepted
      exact accepted.2
    have present := of_decide_eq_true ((List.all_eq_true.mp complete) key required)
    exact False.elim (missing present)

/-- A captured signature still refuses its original missing keys before calling
normalizers or bodies. The host must supply the faithful captured row projection. -/
theorem invoke_capture_missing [DecidableEq Key] (signature : TypedSignature Key Ty)
    (call : Call Key Value) (key : Key) (required : key ∈ signature.requiredKeywords)
    (missing : key ∉ call.keywords.map Prod.fst) (shapeError : Error)
    (normalize : Signature Key → Call Key Value → Except Error (Call Key Value))
    (body : Call Key Value → Except Error Result) :
    invoke [signature.capture.shape] call shapeError normalize body = .error shapeError := by
  apply invoke_shape_error
  have refused : accepts signature.shape call = false :=
    accepts_missing_required _ _ _ required missing
  simp [select, refused]

/-- Full invocation preserves normalization, exact result checks, causes and
cache owners. This delegates to the existing invoker instead of adding dispatch. -/
theorem invokeValues_capture [DecidableEq Key] (clauses : List (TypedSignature Key Ty))
    (call : Call Key Value) (shapeError countError : Error)
    (normalize : TypedSignature Key Ty → Call Key Value → Except Error (Call Key Value))
    (body : Call Key Value → Except Error (List Value × Owner))
    (check : Ty → Value → Except Error Value) :
    invokeValues (clauses.map TypedSignature.capture) call shapeError countError normalize body check =
      invokeValues clauses call shapeError countError normalize body check := by
  have unchanged : (TypedSignature.capture : TypedSignature Key Ty → TypedSignature Key Ty) = id :=
    funext TypedSignature.capture_eq
  simp only [unchanged, List.map_id]

/-- Capture the finite field path before any source refresh. The host supplies
faithful finite copying/admission and final source checks; callback effects are
not rolled back and this theorem does not certify arbitrary Scheme mutation. -/
def prepareSelectedPath (capture : State → Except Error (List Key))
    (refresh : State → Except Error Catalog)
    (compile : Catalog → List Key → Except Error Artifact) (initial : State) : Except Error Artifact :=
  (capture initial).bind fun path => (refresh initial).bind fun catalog => compile catalog path

/-- Malformed/cyclic/exhausted path capture refuses before source refresh. -/
theorem prepareSelectedPath_capture_error (capture : State → Except Error (List Key))
    (refresh : State → Except Error Catalog) (compile : Catalog → List Key → Except Error Artifact)
    (initial : State) (cause : Error) (failed : capture initial = .error cause) :
    prepareSelectedPath capture refresh compile initial = .error cause := by
  simp [prepareSelectedPath, failed, Except.bind]

/-- A source getter failure retains its original cause after successful capture. -/
theorem prepareSelectedPath_refresh_error (capture : State → Except Error (List Key))
    (refresh : State → Except Error Catalog) (compile : Catalog → List Key → Except Error Artifact)
    (initial : State) (path : List Key) (cause : Error)
    (captured : capture initial = .ok path) (failed : refresh initial = .error cause) :
    prepareSelectedPath capture refresh compile initial = .error cause := by
  simp [prepareSelectedPath, captured, failed, Except.bind]

/-- Preparation always compiles the ORIGINAL path, including after refresh has
edited the caller's request buffer. A later independent capture may select another path. -/
theorem prepareSelectedPath_eq (capture : State → Except Error (List Key))
    (refresh : State → Except Error Catalog) (compile : Catalog → List Key → Except Error Artifact)
    (initial : State) (path : List Key) (catalog : Catalog)
    (captured : capture initial = .ok path) (refreshed : refresh initial = .ok catalog) :
    prepareSelectedPath capture refresh compile initial = compile catalog path := by
  simp [prepareSelectedPath, captured, refreshed, Except.bind]

/-- Successful preparation has a successful refresh and a compilation at the
captured path; it cannot justify a different sibling merely because that sibling is valid. -/
theorem prepareSelectedPath_sound (capture : State → Except Error (List Key))
    (refresh : State → Except Error Catalog) (compile : Catalog → List Key → Except Error Artifact)
    (initial : State) (path : List Key) (artifact : Artifact)
    (captured : capture initial = .ok path)
    (accepted : prepareSelectedPath capture refresh compile initial = .ok artifact) :
    ∃ catalog, refresh initial = .ok catalog ∧ compile catalog path = .ok artifact := by
  cases stage : refresh initial with
  | error cause => simp [prepareSelectedPath, captured, stage, Except.bind] at accepted
  | ok catalog =>
    exact ⟨catalog, rfl, by simpa [prepareSelectedPath, captured, stage, Except.bind] using accepted⟩

end LeanPoo.Functional.FunctionSignature
