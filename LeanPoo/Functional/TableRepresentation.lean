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

end LeanPoo.Functional.OrderedDictionary
