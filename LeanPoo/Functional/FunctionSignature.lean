import LeanPoo.Functional.Validation

/-! Finite declarative call signatures. These laws describe supplied arguments and
ordered dispatch; host default evaluation and native procedure arity remain premises. -/
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
theorem supplied_length (check : Value → Except Error Value) (values checked : List Value)
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
Mutable identity and native allocation require the separate Gerbil controls. -/
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

end LeanPoo.Functional.FunctionSignature
