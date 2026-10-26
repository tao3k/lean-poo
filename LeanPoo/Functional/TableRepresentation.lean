import LeanPoo.Functional.TableBatch

/-! Derive table operations from an existing carrier and explicit isomorphisms.
The construction transfers algorithms; no second balancing/indexing algorithm is assumed. -/
namespace LeanPoo.Functional.OrderedDictionary
open Prototype (DictionaryBridge)

variable {K L V W A B : Type} [DecidableEq K] [DecidableEq L]

/-- Conjugate the existing backend's read/write operations by carrier, key and
value isomorphisms. Optional absence remains distinct from every stored payload. -/
def TableCarrier.conjugate (ops : TableCarrier K V A)
    (keys : DictionaryBridge K L) (values : DictionaryBridge V W)
    (carrier : DictionaryBridge A B) : TableCarrier L W B where
  read := fun target => transportView keys values (ops.read (carrier.fromFields target))
  write := fun target key value => carrier.toFields
    (ops.write (carrier.fromFields target) (keys.fromFields key) (value.map values.fromFields))
  read_write := by
    intro target key value
    simp only [carrier.from_to, ops.read_write, transport_replace]
    simp [keys.to_from, Option.map_map, Function.comp_def, values.to_from]

/-- Point reads follow source lookup plus value conversion, without enumeration. -/
theorem TableCarrier.conjugate_read (ops : TableCarrier K V A)
    (keys : DictionaryBridge K L) (values : DictionaryBridge V W)
    (carrier : DictionaryBridge A B) (source : A) (key : K) :
    (ops.conjugate keys values carrier).read (carrier.toFields source) (keys.toFields key) =
      (ops.read source key).map values.toFields := by
  simp [TableCarrier.conjugate, transportView, carrier.from_to, keys.from_to]

/-- A generated write runs the existing backend write with the original payload. -/
theorem TableCarrier.conjugate_write (ops : TableCarrier K V A)
    (keys : DictionaryBridge K L) (values : DictionaryBridge V W)
    (carrier : DictionaryBridge A B) (source : A) (key : K) (value : Option V) :
    (ops.conjugate keys values carrier).write (carrier.toFields source) (keys.toFields key)
      (value.map values.toFields) = carrier.toFields (ops.write source key value) := by
  simp [TableCarrier.conjugate, carrier.from_to, keys.from_to, Option.map_map,
    Function.comp_def, values.from_to]

/-- Generated complete delta execution preserves the actual carrier result and
first conflict key, including repeated edits and cancelled/intermediate writes. -/
theorem TableCarrier.conjugate_apply [DecidableEq V] [DecidableEq W]
    (ops : TableCarrier K V A) (keys : DictionaryBridge K L)
    (values : DictionaryBridge V W) (carrier : DictionaryBridge A B)
    (edits : List (Change K V)) (source : A) :
    (ops.conjugate keys values carrier).apply (transportChanges keys values edits)
      (carrier.toFields source) = ((ops.apply edits source).mapError keys.toFields).map carrier.toFields := by
  induction edits generalizing source with
  | nil => rfl
  | cons edit rest ih =>
    simp only [transportChanges, List.map_cons, TableCarrier.apply, transportChange,
      TableCarrier.conjugate_read]
    have same : (ops.read source edit.key).map values.toFields = edit.before.map values.toFields ↔
        ops.read source edit.key = edit.before := (transport_option_injective values).eq_iff
    by_cases aligned : ops.read source edit.key = edit.before
    · simp only [aligned, ↓reduceIte]
      rw [TableCarrier.conjugate_write]
      exact ih _
    · simp only [same, aligned, ↓reduceIte]
      rfl

/-- Whole batches reuse the generated table protocol rather than another installer. -/
theorem TableCarrier.conjugate_batch [DecidableEq V] [DecidableEq W]
    (ops : TableCarrier K V A) (keys : DictionaryBridge K L)
    (values : DictionaryBridge V W) (carrier : DictionaryBridge A B)
    (batches : List (List (Change K V))) (source : A) :
    (ops.conjugate keys values carrier).apply
      (batchChanges (batches.map (transportChanges keys values))) (carrier.toFields source) =
      ((ops.apply (batchChanges batches) source).mapError keys.toFields).map carrier.toFields := by
  rw [← transport_batchChanges]
  exact ops.conjugate_apply keys values carrier _ source

/-- Undo operates on the generated representation and restores the same original
observations, using existing installation and inverse laws. -/
theorem TableCarrier.conjugate_undo [DecidableEq V] [DecidableEq W]
    (ops : TableCarrier K V A) (keys : DictionaryBridge K L)
    (values : DictionaryBridge V W) (carrier : DictionaryBridge A B)
    (edits : List (Change K V)) (source after : A)
    (success : ops.apply edits source = .ok after) :
    ((ops.conjugate keys values carrier).apply
      (inverseChanges (transportChanges keys values edits)) (carrier.toFields after)).map
        (ops.conjugate keys values carrier).read =
          .ok ((ops.conjugate keys values carrier).read (carrier.toFields source)) := by
  rw [TableCarrier.apply_read]
  apply applyChanges_inverse
  rw [← TableCarrier.apply_read, ops.conjugate_apply, success]
  rfl

/-- Applying the explicit inverse derivation restores the original lookup and
write algorithms, not merely selected example observations. -/
theorem TableCarrier.conjugate_inverse (ops : TableCarrier K V A)
    (keys : DictionaryBridge K L) (values : DictionaryBridge V W)
    (carrier : DictionaryBridge A B) :
    (ops.conjugate keys values carrier |>.conjugate keys.inverse values.inverse carrier.inverse).read = ops.read ∧
    (ops.conjugate keys values carrier |>.conjugate keys.inverse values.inverse carrier.inverse).write = ops.write := by
  constructor
  · funext source key
    simp [TableCarrier.conjugate, transportView, DictionaryBridge.inverse,
      carrier.from_to, keys.from_to, Option.map_map, Function.comp_def, values.from_to]
  · funext source key value
    simp [TableCarrier.conjugate, DictionaryBridge.inverse, carrier.from_to,
      keys.from_to, Option.map_map, Function.comp_def, values.from_to]

/-- Multi-stage representation derivations preserve the same complete lookup. -/
theorem TableCarrier.conjugate_trans_read {M X C : Type} [DecidableEq M]
    (ops : TableCarrier K V A) (keys : DictionaryBridge K L) (nextKeys : DictionaryBridge L M)
    (values : DictionaryBridge V W) (nextValues : DictionaryBridge W X)
    (carrier : DictionaryBridge A B) (nextCarrier : DictionaryBridge B C) :
    (ops.conjugate keys values carrier |>.conjugate nextKeys nextValues nextCarrier).read =
      (ops.conjugate (keys.trans nextKeys) (values.trans nextValues) (carrier.trans nextCarrier)).read := by
  funext source key
  simp [TableCarrier.conjugate, transportView, DictionaryBridge.trans, Option.map_map,
    Function.comp_def]

/-- Multi-stage derivation delegates exactly the same persistent backend write. -/
theorem TableCarrier.conjugate_trans_write {M X C : Type} [DecidableEq M]
    (ops : TableCarrier K V A) (keys : DictionaryBridge K L) (nextKeys : DictionaryBridge L M)
    (values : DictionaryBridge V W) (nextValues : DictionaryBridge W X)
    (carrier : DictionaryBridge A B) (nextCarrier : DictionaryBridge B C) :
    (ops.conjugate keys values carrier |>.conjugate nextKeys nextValues nextCarrier).write =
      (ops.conjugate (keys.trans nextKeys) (values.trans nextValues) (carrier.trans nextCarrier)).write := by
  funext source key value
  simp [TableCarrier.conjugate, DictionaryBridge.trans, Option.map_map, Function.comp_def]

omit [DecidableEq K] [DecidableEq L] in
/-- Map the backend's enumeration in its supplied order; key negation alone does
not sort or reverse the list. Function payloads remain abstract unchanged values. -/
def transportBindings (keys : DictionaryBridge K L) (values : DictionaryBridge V W)
    (bindings : List (K × V)) : List (L × W) :=
  bindings.map (fun (key, value) => (keys.toFields key, values.toFields value))

omit [DecidableEq K] [DecidableEq L] in
/-- Every source binding yields exactly one target binding; derivation adds no scan. -/
theorem transportBindings_length (keys : DictionaryBridge K L) (values : DictionaryBridge V W)
    (bindings : List (K × V)) : (transportBindings keys values bindings).length = bindings.length := by
  simp [transportBindings]

omit [DecidableEq K] [DecidableEq L] in
/-- Standard left-fold delegation preserves callback order and the full accumulator. -/
theorem transportBindings_foldl {R : Type} (keys : DictionaryBridge K L)
    (values : DictionaryBridge V W) (bindings : List (K × V))
    (f : R → L × W → R) (seed : R) :
    (transportBindings keys values bindings).foldl f seed =
      bindings.foldl (fun acc (key, value) => f acc (keys.toFields key, values.toFields value)) seed := by
  simp [transportBindings, List.foldl_map]

omit [DecidableEq K] [DecidableEq L] in
/-- Standard right-fold delegation retains the other backend traversal order. -/
theorem transportBindings_foldr {R : Type} (keys : DictionaryBridge K L)
    (values : DictionaryBridge V W) (bindings : List (K × V))
    (f : L × W → R → R) (seed : R) :
    (transportBindings keys values bindings).foldr f seed =
      bindings.foldr (fun (key, value) acc => f (keys.toFields key, values.toFields value) acc) seed := by
  simp [transportBindings, List.foldr_map]

omit [DecidableEq K] [DecidableEq L] in
/-- Retraction of all enumerated bindings follows the explicit inverses. -/
theorem transportBindings_inverse (keys : DictionaryBridge K L) (values : DictionaryBridge V W)
    (bindings : List (K × V)) :
    transportBindings keys.inverse values.inverse (transportBindings keys values bindings) = bindings := by
  simp [transportBindings, List.map_map, Function.comp_def, DictionaryBridge.inverse,
    keys.from_to, values.from_to]

/-- A derived wrapper's admission scope cannot drop any source/converter origin. -/
theorem wrapper_sources_current {Id : Type} (source converter : List Id)
    (expected current : Id → Option Nat) :
    stampMatches (source ++ converter) expected current =
      (stampMatches source expected current && stampMatches converter expected current) :=
  stampMatches_append _ _ _ _

/-- Nested derivation scopes retain every original converter dependency. -/
theorem wrapper_sources_nested {Id : Type} (origins : List (List Id)) (converter : List Id)
    (expected current : Id → Option Nat) :
    stampMatches (origins.flatten ++ converter) expected current =
      (origins.all (fun scope => stampMatches scope expected current) &&
        stampMatches converter expected current) := by
  rw [stampMatches_append, batch_stampMatches]

omit [DecidableEq K] [DecidableEq L] in
/-- Wrapping a lawful codec preserves roundtrip by ordinary unary composition.
Parser correctness and exact rational normalization remain premises, not inferred facts. -/
theorem conjugate_codec_roundtrip {Wire : Type} (carrier : DictionaryBridge A B)
    (encode : A → Wire) (decode : Wire → A) (law : Function.LeftInverse decode encode) (target : B) :
    carrier.toFields (decode (encode (carrier.fromFields target))) = target := by
  rw [law, carrier.to_from]

omit [DecidableEq K] [DecidableEq L] in
/-- Pair decoding delegates to both child codecs; retaining raw wire children is
insufficient whenever an integer, container or wrapper has a nonidentity decoder. -/
theorem pair_codec_roundtrip {X Y : Type} (encodeLeft : A → X) (decodeLeft : X → A)
    (encodeRight : B → Y) (decodeRight : Y → B)
    (leftLaw : Function.LeftInverse decodeLeft encodeLeft)
    (rightLaw : Function.LeftInverse decodeRight encodeRight) (left : A) (right : B) :
    (decodeLeft (encodeLeft left), decodeRight (encodeRight right)) = (left, right) := by
  rw [leftLaw, rightLaw]


/-- Charge the actually executed revision prefix. A charge may depend on the
current persistent carrier, edit and comparison outcome: conversion, equality,
recognition, metadata and backend work need not have constant costs. -/
def TableCarrier.applyCost (ops : TableCarrier K V A) [DecidableEq V]
    (charge : A → Change K V → Bool → Nat) : List (Change K V) → A → Nat
  | [], _ => 0
  | edit :: rest, source =>
    if ops.read source edit.key = edit.before then
      charge source edit true + ops.applyCost charge rest (ops.write source edit.key edit.after)
    else charge source edit false

/-- A conflict charges its read/comparison and conversions, but neither a backend
write nor any suffix. The caller's charge must likewise exclude a refused write. -/
theorem TableCarrier.applyCost_conflict (ops : TableCarrier K V A) [DecidableEq V]
    (charge : A → Change K V → Bool → Nat) (edit : Change K V)
    (rest : List (Change K V)) (source : A)
    (conflict : ops.read source edit.key ≠ edit.before) :
    ops.applyCost charge (edit :: rest) source = charge source edit false := by
  simp [TableCarrier.applyCost, conflict]

/-- Independent cost categories add over the same execution, including an early
conflict. This permits charging actual equality/conversion/preparation separately
without erasing them from a claimed backend improvement. -/
theorem TableCarrier.applyCost_add (ops : TableCarrier K V A) [DecidableEq V]
    (left right : A → Change K V → Bool → Nat) (edits : List (Change K V)) (source : A) :
    ops.applyCost (fun state edit ok => left state edit ok + right state edit ok) edits source =
      ops.applyCost left edits source + ops.applyCost right edits source := by
  induction edits generalizing source with
  | nil => rfl
  | cons edit rest ih =>
    simp only [TableCarrier.applyCost]
    split
    · rw [ih]; omega
    · rfl

/-- Isomorphic execution charges the same successful/failed prefix when the
explicit target quote includes the corresponding source quote. No equality,
conversion, metadata, allocation or GC cost is inferred from an isomorphism law. -/
theorem TableCarrier.conjugate_cost [DecidableEq V] [DecidableEq W]
    (ops : TableCarrier K V A) (keys : DictionaryBridge K L)
    (values : DictionaryBridge V W) (carrier : DictionaryBridge A B)
    (sourceCharge : A → Change K V → Bool → Nat)
    (targetCharge : B → Change L W → Bool → Nat)
    (quotes : ∀ state edit ok,
      targetCharge (carrier.toFields state) (transportChange keys values edit) ok =
        sourceCharge state edit ok)
    (edits : List (Change K V)) (source : A) :
    (ops.conjugate keys values carrier).applyCost targetCharge
      (transportChanges keys values edits) (carrier.toFields source) =
        ops.applyCost sourceCharge edits source := by
  induction edits generalizing source with
  | nil => rfl
  | cons edit rest ih =>
    simp only [transportChanges, List.map_cons, TableCarrier.applyCost]
    have same : (ops.read source edit.key).map values.toFields = edit.before.map values.toFields ↔
        ops.read source edit.key = edit.before := (transport_option_injective values).eq_iff
    simp only [transportChange, TableCarrier.conjugate_read, same]
    by_cases aligned : ops.read source edit.key = edit.before
    · simp only [aligned, ↓reduceIte]
      rw [TableCarrier.conjugate_write]
      have q := quotes source edit true
      simp only [transportChange] at q
      rw [q]
      exact congrArg (fun n => sourceCharge source edit true + n) (ih _)
    · simp only [aligned, ↓reduceIte]
      exact quotes _ _ _

/-- Full workflow accounting retains preparation, observation and undo in addition
 to installation. Costs are externally measured or justified; units are explicit. -/
def tableWorkflowCost (prepare install observe undo : Nat) : Nat :=
  prepare + install + observe + undo

/-- A cheaper installer implies a cheaper full workflow only after charging the
additional preparation/conversion/equality/observation overhead against its saving. -/
theorem tableWorkflowCost_breakEven (prepare install observe undo extra saving : Nat)
    (bounded : extra ≤ saving) (available : saving ≤ install) :
    tableWorkflowCost (prepare + extra) (install - saving) observe undo ≤
      tableWorkflowCost prepare install observe undo := by
  unfold tableWorkflowCost; omega

/-- Wrapper overhead is retained over the same actually executed prefix. A source
backend speedup alone cannot cancel conversion/equality/guard work silently. -/
theorem TableCarrier.conjugate_cost_overhead [DecidableEq V] [DecidableEq W]
    (ops : TableCarrier K V A) (keys : DictionaryBridge K L)
    (values : DictionaryBridge V W) (carrier : DictionaryBridge A B)
    (backend overhead : A → Change K V → Bool → Nat)
    (target : B → Change L W → Bool → Nat)
    (quotes : ∀ state edit ok,
      target (carrier.toFields state) (transportChange keys values edit) ok =
        backend state edit ok + overhead state edit ok)
    (edits : List (Change K V)) (source : A) :
    (ops.conjugate keys values carrier).applyCost target
      (transportChanges keys values edits) (carrier.toFields source) =
        ops.applyCost backend edits source + ops.applyCost overhead edits source := by
  rw [ops.conjugate_cost keys values carrier
    (fun state edit ok => backend state edit ok + overhead state edit ok) target quotes]
  exact ops.applyCost_add backend overhead edits source

/-- Sharing an encountered pure conversion leaves both inverse comparisons and
short-circuit refusal unchanged. Stateful/effectful callback semantics are not
inferred from this equality and are not justified for cross-call memoization. -/
theorem carrier_check_share {X Y : Type} (encode : X → Y) (decode : Y → X)
    (sameX : X → X → Bool) (sameY : Y → Y → Bool) (input : X) :
    (let output := encode input
     sameX (decode output) input && sameY (encode (decode output)) output) =
    (let output := encode input
     let recovered := decode output
     sameX recovered input && sameY (encode recovered) output) := rfl


/-- A per-attempt quote scales over the actual executed prefix, including the
failed comparison but not an unexecuted suffix. This prices repeated Type lookup
without pretending that each edit or each callback has unit machine cost. -/
theorem TableCarrier.applyCost_scale (ops : TableCarrier K V A) [DecidableEq V]
    (unit : A → Change K V → Bool → Nat) (price : Nat)
    (edits : List (Change K V)) (source : A) :
    ops.applyCost (fun state edit ok => price * unit state edit ok) edits source =
      price * ops.applyCost unit edits source := by
  induction edits generalizing source with
  | nil => simp [TableCarrier.applyCost]
  | cons edit rest ih =>
    simp only [TableCarrier.applyCost]
    split
    · rw [ih, Nat.mul_add]
    · rfl

/-- Direct Type selection and already captured field access have separate prices.
Extra preparation includes all captured-record allocation, validation and GC costs;
conversion/equality/backend costs are common, not erased from the total. -/
def typeContextCost (prepare visits selection common : Nat) : Nat :=
  prepare + visits * (2 * selection + common)

/-- Capture is beneficial only after paying its complete preparation premium.
The saved selection price is an explicit premise; no host timing is inferred. -/
theorem typeContextCost_breakEven (prepare extra visits field saved common : Nat)
    (budget : extra ≤ visits * (2 * saved)) :
    typeContextCost (prepare + extra) visits field common ≤
      typeContextCost prepare visits (field + saved) common := by
  simp only [typeContextCost, Nat.mul_add] at *
  omega

omit [DecidableEq K] [DecidableEq L] in
/-- Equivalent captured child selections leave every mapped key/value unchanged.
This law requires the live selection to agree while the existing origin guard is
current; it does not license reusing a context after a revision change. -/
theorem transportBindings_captured (keys liveKeys : DictionaryBridge K L)
    (values liveValues : DictionaryBridge V W) (bindings : List (K × V))
    (keyCurrent : liveKeys.toFields = keys.toFields)
    (valueCurrent : liveValues.toFields = values.toFields) :
    transportBindings liveKeys liveValues bindings = transportBindings keys values bindings := by
  simp only [transportBindings, keyCurrent, valueCurrent]

/-- Any stale captured dependency, including a child Type, refuses admission;
there is no exception for an empty revision batch or an unused conversion. -/
theorem typeContext_stale {Id : Type} (ids : List Id) (expected current : Id → Option Nat)
    (id : Id) (present : id ∈ ids) (changed : expected id ≠ current id) :
    stampMatches ids expected current = false := by
  unfold stampMatches
  apply Bool.eq_false_iff.mpr
  intro aligned
  exact changed (beq_iff_eq.mp ((List.all_eq_true.mp aligned) id present))

/-- An observed selection performs the live getter, including its refusal. The
unobserved branch may reuse a guarded child identity, not its access authority. -/
def readTypeContext {E T : Type} (observed : Bool)
    (read : Unit → Except E T) (saved : T) : Except E T :=
  if observed then read () else .ok saved

/-- Observation preserves the exact access-denial cause rather than serving a
cached value. This is an Except-level law, not a VM trace or timing theorem. -/
theorem readTypeContext_denied {E T : Type} (cause : E) (saved : T) :
    readTypeContext true (fun _ => Except.error cause) saved = .error cause := rfl

/-- Both selection modes agree only when the current live getter admits the
captured identity; stale-origin rejection remains a separate prerequisite. -/
theorem readTypeContext_current {E T : Type} (observed : Bool)
    (read : Unit → Except E T) (saved : T) (current : read () = .ok saved) :
    readTypeContext observed read saved = .ok saved := by
  cases observed <;> simp [readTypeContext, current]

/-- Standard two-list traversal needs an explicit length check: truncation must
not admit a missing origin. Revision reads are pure state observations. -/
def revisionsCurrent {Id Version : Type} [BEq Version]
    (sources : List Id) (versions : List Version) (revision : Id → Version) : Bool :=
  (sources.length == versions.length) &&
    (sources.zip versions).all (fun (source, expected) => revision source == expected)

/-- Paired comparison admits exactly the same complete revision
sequence as mapping every revision and comparing the resulting list. -/
theorem revisionsCurrent_eq {Id Version : Type} [BEq Version]
    (sources : List Id) (versions : List Version) (revision : Id → Version) :
    revisionsCurrent sources versions revision = (sources.map revision == versions) := by
  induction sources generalizing versions with
  | nil => cases versions <;> simp [revisionsCurrent]
  | cons source rest ih =>
    cases versions with
    | nil => simp [revisionsCurrent]
    | cons version tail =>
      have len : (rest.length + 1 == tail.length + 1) =
          (rest.length == tail.length) := by simp
      simp only [revisionsCurrent, List.length_cons, len,
        List.zip_cons_cons, List.all_cons, List.map_cons, List.cons_beq_cons]
      rw [← ih]
      simp only [revisionsCurrent]
      cases (rest.length == tail.length) <;>
        cases (revision source == version) <;> simp_all

/-- Wall cost explicitly retains a signed residual beyond measured CPU. A
non-GC improvement does not by itself establish a wall-clock improvement. -/
def measuredWall (nonGC gc : Nat) (residual : Int) : Int := nonGC + gc + residual

/-- A measured CPU saving implies a wall saving only if the residual increase
fits inside that saving. The premise is empirical, not a scheduler theorem. -/
theorem measuredWall_bound (oldWork oldGC newWork newGC : Nat) (oldR newR : Int)
    (budget : newR - oldR ≤ (oldWork : Int) + oldGC - ((newWork : Int) + newGC)) :
    measuredWall newWork newGC newR ≤ measuredWall oldWork oldGC oldR := by
  unfold measuredWall
  omega

/-- Whole-entry non-GC CPU is partitioned into disjoint preparation, fixed prefix,
first-call, batch and remaining work. GC and signed wall residual are charged once;
per-stage medians are not additive observations. -/
def measuredEntry (prepare warmup firstCall batch remaining gc : Nat) (residual : Int) : Int :=
  measuredWall (prepare + warmup + firstCall + batch + remaining) gc residual

/-- Removing unused fixture preparation improves complete entry wall only when
changes in every other stage, GC and residual fit the measured preparation saving.
These inequalities are empirical premises, not a runtime or scheduler guarantee. -/
theorem measuredEntry_prepare_bound
    (oldPrepare oldPrefix oldFirst oldBatch oldRemaining oldGC : Nat)
    (newPrepare newPrefix newFirst newBatch newRemaining newGC : Nat) (oldR newR : Int)
    (budget : ((newPrefix : Int) + newFirst + newBatch + newRemaining + newGC + newR) -
        ((oldPrefix : Int) + oldFirst + oldBatch + oldRemaining + oldGC + oldR) ≤
      (oldPrepare : Int) - newPrepare) :
    measuredEntry newPrepare newPrefix newFirst newBatch newRemaining newGC newR ≤
      measuredEntry oldPrepare oldPrefix oldFirst oldBatch oldRemaining oldGC oldR := by
  simp only [measuredEntry, measuredWall]
  omega

/-- A collector-policy saving is admissible only if it pays for every other
complete-entry cost, including preparation, first calls and signed wall residual.
This is an accounting condition on retained observations, not a collector theorem. -/
theorem measuredEntry_gc_bound
    (oldPrepare newPrepare oldPrefix newPrefix oldFirst newFirst oldBatch newBatch
      oldRemaining newRemaining oldGC newGC : Nat) (oldR newR : Int)
    (covered :
      ((newPrepare : Int) + newPrefix + newFirst + newBatch + newRemaining + newR) -
        ((oldPrepare : Int) + oldPrefix + oldFirst + oldBatch + oldRemaining + oldR) ≤
      (oldGC : Int) - newGC) :
    measuredEntry newPrepare newPrefix newFirst newBatch newRemaining newGC newR ≤
      measuredEntry oldPrepare oldPrefix oldFirst oldBatch oldRemaining oldGC oldR := by
  simp only [measuredEntry, measuredWall]
  omega

/-- The empirical nonnegative upper envelope retains every adverse observation.
Zero is the floor so an all-negative sample set claims no future negative bound. -/
def measuredTail (samples : List Int) : Int := samples.foldr max 0

/-- A tail bound requires every retained observation, rather than its mean, to
meet the bound. Sample admission and correspondence are separate host obligations. -/
theorem measuredTail_bound (samples : List Int) (limit : Int) (nonnegative : 0 ≤ limit)
    (bounded : ∀ sample ∈ samples, sample ≤ limit) : measuredTail samples ≤ limit := by
  induction samples with
  | nil => exact nonnegative
  | cons head rest ih =>
    exact Int.max_le.mpr ⟨bounded head (by simp),
      ih (fun sample inside => bounded sample (by simp [inside]))⟩

/-- Capture the actual ordered successful prefix and the original first failure.
Reporting consumes this log after sampling; it must not mutate sample state or
throw. This finite Except model does not model GC, the VM or arbitrary IO effects. -/
def measurePair {Side Sample Cause : Type} (sample : Side → Except Cause Sample) :
    List Side → List (Side × Sample) × Except Cause Unit
  | [] => ([], .ok ())
  | side :: rest => match sample side with
    | .error cause => ([], .error cause)
    | .ok value =>
      let following := measurePair sample rest
      ((side, value) :: following.1, following.2)

/-- Deferred reporting changes neither admission nor the first refusal relative
 to the existing ordered checks. Host sample/trace interpretation is a premise. -/
theorem measurePair_status {Side Sample Cause : Type}
    (sample : Side → Except Cause Sample) (order : List Side) :
    (measurePair sample order).2 =
      runEntryChecks (order.map (fun side _ => (sample side).map (fun _ => ()))) := by
  induction order with
  | nil => rfl
  | cons side rest ih =>
    cases admitted : sample side <;>
      simp [measurePair, admitted, runEntryChecks, Except.map, ih] <;> rfl

/-- A failed second side retains the exact completed first sample for the reporter,
without pretending to have measured the failed side or replacing its cause. -/
theorem measurePair_second_error {Side Sample Cause : Type}
    (sample : Side → Except Cause Sample) (first second : Side) (value : Sample) (cause : Cause)
    (left : sample first = .ok value) (right : sample second = .error cause) :
    measurePair sample [first, second] = ([(first, value)], .error cause) := by
  simp [measurePair, left, right]

/-- Refusal at the first side has no completed samples; successful pairs retain
both observations exactly once in the original order, including repeated sides. -/
theorem measurePair_complete {Side Sample Cause : Type}
    (sample : Side → Except Cause Sample) (first second : Side) (a b : Sample)
    (left : sample first = .ok a) (right : sample second = .ok b) :
    measurePair sample [first, second] = ([(first, a), (second, b)], .ok ()) := by
  simp [measurePair, left, right]

/-- Private construction protects origins; publication adds the completed receiver.
The prepared list is reused only within this derived protocol, never globally. -/
def receiverScope {Id : Type} (receiver : Option Id) (sources : List Id) : List Id :=
  receiver.toList ++ sources

/-- Reusing a completed scope retains protection for its receiver and every
origin. This is a membership/protection law, not a VM allocation theorem. -/
theorem receiverScope_closed {Id : Type} (owner : Id) (sources : List Id)
    (allows : Id → Prop) :
    (∀ id ∈ receiverScope (some owner) sources, allows id) ↔
      allows owner ∧ (∀ id ∈ sources, allows id) := by
  simp [receiverScope]

/-- A complete source is admitted before row projection or the existing encoder.
Leaf normalization and inferred serialization of opaque handles are not introduced. -/
def encodeCollection (admit : A → Except E Unit) (rows : A → Rows)
    (encode : Rows → Except E Wire) (source : A) : Except E Wire :=
  match admit source with
  | .error cause => .error cause
  | .ok () => encode (rows source)

/-- Decode privately, delegate the existing complete builder, and expose only an
admitted root. Parser/builder laws and finite input are explicit premises. -/
def decodeCollection (decode : Wire → Except E Rows) (build : Rows → Except E A)
    (admit : A → Except E Unit) (wire : Wire) : Except E A :=
  match decode wire with
  | .error cause => .error cause
  | .ok rows => match build rows with
    | .error cause => .error cause
    | .ok root => match admit root with
      | .error cause => .error cause
      | .ok () => .ok root

/-- Invalid source refusal precedes every child encoder and returns its exact cause. -/
theorem encodeCollection_refused (admit : A → Except E Unit) (rows : A → Rows)
    (encode : Rows → Except E Wire) (source : A) (cause : E)
    (refused : admit source = .error cause) :
    encodeCollection admit rows encode source = .error cause := by simp [encodeCollection, refused]

/-- Parser refusal is preserved instead of returning an empty or partial collection. -/
theorem decodeCollection_parser_refused (decode : Wire → Except E Rows)
    (build : Rows → Except E A) (admit : A → Except E Unit) (wire : Wire) (cause : E)
    (refused : decode wire = .error cause) :
    decodeCollection decode build admit wire = .error cause := by simp [decodeCollection, refused]

/-- Complete construction failure retains the backend's duplicate/index policy. -/
theorem decodeCollection_builder_refused (decode : Wire → Except E Rows)
    (build : Rows → Except E A) (admit : A → Except E Unit) (wire : Wire) (rows : Rows) (cause : E)
    (parsed : decode wire = .ok rows) (refused : build rows = .error cause) :
    decodeCollection decode build admit wire = .error cause := by simp [decodeCollection, parsed, refused]

/-- A decoded carrier with invalid final invariants never escapes as a successful root. -/
theorem decodeCollection_root_refused (decode : Wire → Except E Rows)
    (build : Rows → Except E A) (admit : A → Except E Unit) (wire : Wire) (rows : Rows)
    (root : A) (cause : E) (parsed : decode wire = .ok rows) (built : build rows = .ok root)
    (refused : admit root = .error cause) :
    decodeCollection decode build admit wire = .error cause := by simp [decodeCollection, parsed, built, refused]

/-- Ordinary representation/child codec inverse laws imply the admitted roundtrip.
The statement makes no assertion about a particular JSON/binary parser implementation. -/
theorem collection_codec_roundtrip (admit : A → Except E Unit) (rows : A → Rows)
    (build : Rows → A) (encode : Rows → Wire) (decode : Wire → Rows)
    (carrierLaw : Function.LeftInverse build rows) (codecLaw : Function.LeftInverse decode encode)
    (source : A) (ready : admit source = .ok ()) :
    (encodeCollection admit rows (fun input => .ok (encode input)) source).bind
      (decodeCollection (fun wire => .ok (decode wire)) (fun input => .ok (build input)) admit) =
        .ok source := by
  simp only [encodeCollection, ready, Except.bind, decodeCollection]
  rw [codecLaw (rows source), carrierLaw source]
  simp [ready]

/-- Port effects are retained explicitly beside failure. Admission happens before
any write, but a later failing child codec is not a transaction over the port. -/
def marshalCollection (admit : A → Except E Unit) (write : A → Port → Port × Except E Unit)
    (source : A) (port : Port) : Port × Except E Unit :=
  match admit source with
  | .error cause => (port, .error cause)
  | .ok () => write source port

/-- Invalid roots leave the port untouched, before even a length prefix is emitted. -/
theorem marshalCollection_refused (admit : A → Except E Unit)
    (write : A → Port → Port × Except E Unit) (source : A) (port : Port) (cause : E)
    (refused : admit source = .error cause) :
    marshalCollection admit write source port = (port, .error cause) := by
  simp [marshalCollection, refused]

/-- A late codec refusal preserves both its exact cause and the prior emitted prefix. -/
theorem marshalCollection_late_refused (admit : A → Except E Unit)
    (write : A → Port → Port × Except E Unit) (source : A) (before after : Port) (cause : E)
    (ready : admit source = .ok ()) (failed : write source before = (after, .error cause)) :
    marshalCollection admit write source before = (after, .error cause) := by
  simp [marshalCollection, ready, failed]

/-- A partial collection family exposes empty and finite-input construction as
independent computations. Declaring a view does not assert empty membership. -/
structure CollectionConstructors (E Rows A : Type) where
  empty : Unit → Except E A
  fromRows : Rows → Except E A

/-- Existing revision protection and checked conversion are shared by each
requested constructor. Neither callback is evaluated while the view is derived. -/
def CollectionConstructors.derive (source : CollectionConstructors E Rows A)
    (current : Unit → Except E Unit) (encode : A → Except E B) : CollectionConstructors E Rows B where
  empty := fun _ => (current ()).bind fun _ => (source.empty ()).bind encode
  fromRows := fun rows => (current ()).bind fun _ => (source.fromRows rows).bind encode

/-- Changing the partial empty constructor cannot change finite construction,
including through nested representation, index and ordered view derivations. -/
theorem CollectionConstructors.derive_rows_independent
    (source : CollectionConstructors E Rows A) (otherEmpty : Unit → Except E A)
    (current : Unit → Except E Unit) (encode : A → Except E B) :
    (source.derive current encode).fromRows =
      (({ source with empty := otherEmpty } : CollectionConstructors E Rows A).derive current encode).fromRows := rfl

/-- Empty construction still returns the original source refusal when requested. -/
theorem CollectionConstructors.derive_empty_refused
    (source : CollectionConstructors E Rows A) (current : Unit → Except E Unit)
    (encode : A → Except E B) (cause : E) (ready : current () = .ok ())
    (refused : source.empty () = .error cause) :
    (source.derive current encode).empty () = .error cause := by
  simp [CollectionConstructors.derive, ready, refused, Except.bind]

/-- A stale declaration refuses before either source construction or conversion. -/
theorem CollectionConstructors.derive_stale
    (source : CollectionConstructors E Rows A) (current : Unit → Except E Unit)
    (encode : A → Except E B) (rows : Rows) (cause : E)
    (stale : current () = .error cause) :
    (source.derive current encode).empty () = .error cause ∧
    (source.derive current encode).fromRows rows = .error cause := by
  simp [CollectionConstructors.derive, stale, Except.bind]

/-- A successful nonempty construction does not require a lawful empty value. -/
theorem CollectionConstructors.derive_rows_ready
    (source : CollectionConstructors E Rows A) (current : Unit → Except E Unit)
    (encode : A → Except E B) (rows : Rows) (root : A) (result : B)
    (ready : current () = .ok ()) (built : source.fromRows rows = .ok root)
    (encoded : encode root = .ok result) :
    (source.derive current encode).fromRows rows = .ok result := by
  simp [CollectionConstructors.derive, ready, built, encoded, Except.bind]

/-- Two view layers preserve their source-to-target conversion order and exact
failure causes. The second layer's revision check precedes the inner request. -/
theorem CollectionConstructors.derive_rows_chain {C : Type}
    (source : CollectionConstructors E Rows A)
    (inner outer : Unit → Except E Unit) (encode : A → Except E B) (next : B → Except E C)
    (rows : Rows) (innerReady : inner () = .ok ()) (outerReady : outer () = .ok ()) :
    ((source.derive inner encode).derive outer next).fromRows rows =
      (source.fromRows rows).bind (fun root => (encode root).bind next) := by
  cases built : source.fromRows rows <;>
    simp [CollectionConstructors.derive, innerReady, outerReady, built, Except.bind]

/-- Once metadata is rederived, an old refusal is not retained as a cached
construction result. Retry uses current checks and the original persistent input. -/
theorem CollectionConstructors.derive_retry
    (source : CollectionConstructors E Rows A) (old fresh : Unit → Except E Unit)
    (encode : A → Except E B) (rows : Rows) (cause : E) (root : A) (result : B)
    (stale : old () = .error cause) (ready : fresh () = .ok ())
    (built : source.fromRows rows = .ok root) (encoded : encode root = .ok result) :
    (source.derive old encode).fromRows rows = .error cause ∧
    (source.derive fresh encode).fromRows rows = .ok result := by
  constructor
  · exact (source.derive_stale old encode rows cause stale).2
  · exact source.derive_rows_ready fresh encode rows root result ready built encoded

/-- The encountered carrier check keeps callback failures and inverse refusals
explicit. Admission observes the output; it cannot replace the returned carrier.
Callbacks may fail, but arbitrary IO effects or termination are outside this model. -/
def checkTableCarrier {X Y E : Type} [DecidableEq X] [DecidableEq Y]
    (forward : X → Except E Y) (backward : Y → Except E X)
    (admit : Y → Except E Unit) (leftFailure : X → E) (rightFailure : Y → E)
    (input : X) : Except E Y :=
  (forward input).bind fun output => (admit output).bind fun _ =>
    (backward output).bind fun recovered =>
      if recovered ≠ input then .error (leftFailure input)
      else (forward recovered).bind fun replay =>
        if replay ≠ output then .error (rightFailure output) else .ok output

/-- Output admission refuses before either inverse callback is demanded. -/
theorem checkTableCarrier_admission_failure {X Y E : Type}
    [DecidableEq X] [DecidableEq Y]
    (forward : X → Except E Y) (backward : Y → Except E X)
    (admit : Y → Except E Unit) (leftFailure : X → E) (rightFailure : Y → E)
    (input : X) (output : Y) (cause : E)
    (built : forward input = .ok output) (refused : admit output = .error cause) :
    checkTableCarrier forward backward admit leftFailure rightFailure input = .error cause := by
  simp [Except.bind, checkTableCarrier, built, refused]

/-- A left-inverse refusal retains the input and precedes the replay check. -/
theorem checkTableCarrier_left_failure {X Y E : Type}
    [DecidableEq X] [DecidableEq Y]
    (forward : X → Except E Y) (backward : Y → Except E X)
    (admit : Y → Except E Unit) (leftFailure : X → E) (rightFailure : Y → E)
    (input recovered : X) (output : Y)
    (built : forward input = .ok output) (admitted : admit output = .ok ())
    (restored : backward output = .ok recovered) (different : recovered ≠ input) :
    checkTableCarrier forward backward admit leftFailure rightFailure input =
      .error (leftFailure input) := by
  simp [Except.bind, checkTableCarrier, built, admitted, restored, different]

/-- Under stable callback laws the check returns the original output. Neither
normalization nor cross-call caching follows from these finite equations. -/
theorem checkTableCarrier_roundtrip {X Y E : Type}
    [DecidableEq X] [DecidableEq Y]
    (forward : X → Except E Y) (backward : Y → Except E X)
    (admit : Y → Except E Unit) (leftFailure : X → E) (rightFailure : Y → E)
    (input : X) (output : Y)
    (built : forward input = .ok output) (admitted : admit output = .ok ())
    (restored : backward output = .ok input) :
    checkTableCarrier forward backward admit leftFailure rightFailure input = .ok output := by
  simp [Except.bind, checkTableCarrier, built, admitted, restored]

/-- Prepare every protected participant before reading the captured revision
family. The action runs only after a successful comparison; callback costs remain
charged separately, and this does not certify arbitrary mutable leaf data. -/
def withTableRevisions {E Stamp Result : Type} [DecidableEq Stamp]
    (prepare : Unit → Except E Unit) (read : Unit → Except E Stamp)
    (expected : Stamp) (stale : E) (action : Unit → Except E Result) : Except E Result :=
  (prepare ()).bind fun _ => (read ()).bind fun current =>
    if current ≠ expected then .error stale else action ()

/-- Recursive-construction or source preparation failure is never hidden by a
revision comparison or by an action that would otherwise succeed. -/
theorem withTableRevisions_prepare_failure {E Stamp Result : Type} [DecidableEq Stamp]
    (prepare : Unit → Except E Unit) (read : Unit → Except E Stamp)
    (expected : Stamp) (stale cause : E) (action : Unit → Except E Result)
    (refused : prepare () = .error cause) :
    withTableRevisions prepare read expected stale action = .error cause := by
  simp [Except.bind, withTableRevisions, refused]

/-- Stale captures refuse before the operation, retaining the caller's cause. -/
theorem withTableRevisions_stale {E Stamp Result : Type} [DecidableEq Stamp]
    (prepare : Unit → Except E Unit) (read : Unit → Except E Stamp)
    (expected current : Stamp) (stale : E) (action : Unit → Except E Result)
    (ready : prepare () = .ok ()) (observed : read () = .ok current)
    (different : current ≠ expected) :
    withTableRevisions prepare read expected stale action = .error stale := by
  simp [Except.bind, withTableRevisions, ready, observed, different]

/-- A current family delegates the exact action outcome, including its failure;
sharing the guard cannot turn a refused operation into a successful publication. -/
theorem withTableRevisions_current {E Stamp Result : Type} [DecidableEq Stamp]
    (prepare : Unit → Except E Unit) (read : Unit → Except E Stamp)
    (expected : Stamp) (stale : E) (action : Unit → Except E Result)
    (ready : prepare () = .ok ()) (observed : read () = .ok expected) :
    withTableRevisions prepare read expected stale action = action () := by
  simp [Except.bind, withTableRevisions, ready, observed]

end LeanPoo.Functional.OrderedDictionary
