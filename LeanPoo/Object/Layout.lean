import LeanPoo.Object.Memo

/-!
The paper's object-layout and inline-cache path, expressed with Lean values.
The C4 suffix tail occupies the front of the field array. Each field is a
shared lazy cell from the existing memoized object, so offset access does not
change final-self recursion or force any value during layout construction.
Offsets are array positions, not machine byte offsets.
-/

namespace LeanPoo.Object

universe u v

/-- Suffix specifications form a stable least-specific-first prefix. -/
def Plan.suffixNames {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (plan : Plan Key Value) : List String :=
  plan.precedence.reverse.takeWhile fun name =>
    match plan.schema.graph.findNode? name with
    | some node => node.suffix
    | none => false

/-- Direct keys contributed by the suffix tail, in least-specific-first C4
order. C4 validation puts suffix specifications at the end of precedence, so
they occupy the front of `LeanPoo.allSlots`. -/
def Plan.suffixKeys {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (plan : Plan Key Value) : List Key :=
  let (_, reversed) := plan.suffixNames.foldl (fun (seen, reversed) name =>
    let keys := (plan.schema.declaration name).map Declaration.directKeys |>.getD []
    keys.foldl (fun (seen, reversed) key =>
      if seen.contains key then (seen, reversed)
      else (seen.insert key, key :: reversed)) (seen, reversed))
    (({} : Std.HashSet Key), [])
  reversed.reverse

/-- A cell is prepared from the existing lazy table. Its equation is enough
to prove that array access agrees with ordinary keyed access. -/
structure CellProgram {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (object : Memoized Key Value) (key : Key) where
  run : Unit → Option (Value key)
  sound : run () = object.read key

private def Memoized.cellProgram {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (object : Memoized Key Value) (key : Key) : CellProgram object key :=
  match found : object.thunks.get? key with
  | some thunk =>
      ⟨fun _ => thunk.get, by simp [Memoized.read, found]⟩
  | none =>
      ⟨fun _ => none, by simp [Memoized.read, found]⟩

/-- A validated object with direct array positions for its lazy cells. The
hash table is used only to find an offset for a dynamic key. -/
structure SlotLayout (Key : Type u) (Value : Key → Type v)
    [BEq Key] [LawfulBEq Key] [Hashable Key] where
  object : Memoized Key Value
  fields : Array (Entry Key (fun key => CellProgram object key))
  offsets : Std.HashMap Key Nat
  suffixSize : Nat
  suffixAncestors : Array String
  shapeId : UInt64

private def Memoized.layoutEntry {Key : Type u} {Value : Key → Type v}
    [DecidableEq Key] [BEq Key] [LawfulBEq Key] [Hashable Key]
    (object : Memoized Key Value) (key : Key) :
    Entry Key (fun key => CellProgram object key) :=
  ⟨key, object.cellProgram key, fun _ => inferInstance⟩

/-- The existing declaration-owned order starts with the validated C4
suffix tail. Materialization shares each already allocated thunk. -/
def Memoized.layout {Key : Type u} {Value : Key → Type v}
    [DecidableEq Key] [BEq Key] [LawfulBEq Key] [Hashable Key]
    (object : Memoized Key Value) : SlotLayout Key Value :=
  let keys := LeanPoo.allSlots object.plan
  let fields := keys.toArray.map object.layoutEntry
  let (offsets, _) := fields.foldl (fun (offsets, next) entry =>
    (offsets.insert entry.key next, next + 1))
    (({} : Std.HashMap Key Nat), 0)
  { object, fields, offsets, suffixSize := object.plan.suffixKeys.length
    suffixAncestors := object.plan.suffixNames.toArray
    shapeId := hash (keys, object.plan.suffixNames) }

/-- Check an array position before treating it as a typed field offset. -/
def SlotLayout.matchesAt {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (layout : SlotLayout Key Value) (offset : Nat) (key : Key) : Bool :=
  match layout.fields[offset]? with
  | some entry => entry.key == key
  | none => false

/-- Check an offset and read its lazy cell in one array access. A mismatch
falls back to the authoritative object and reports a cache miss. -/
def SlotLayout.readAtChecked {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (layout : SlotLayout Key Value) (offset : Nat) (key : Key) :
    Option (Value key) × Bool :=
  match layout.fields[offset]? with
  | none => (layout.object.read key, false)
  | some entry =>
      letI : Decidable (key = entry.key) := entry.decideEq key
      if same : key = entry.key then
        ((same.symm ▸ entry.value).run (), true)
      else (layout.object.read key, false)

theorem SlotLayout.readAtChecked_sound {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (layout : SlotLayout Key Value) (offset : Nat) (key : Key) :
    (layout.readAtChecked offset key).1 = layout.object.read key := by
  unfold SlotLayout.readAtChecked
  split
  · rfl
  · rename_i entry fieldEq
    by_cases same : key = entry.key
    · subst key
      simpa using entry.value.sound
    · simp [same]

/-- Read by a checked offset; a stale position preserves keyed meaning. -/
def SlotLayout.readAt {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (layout : SlotLayout Key Value) (offset : Nat) (key : Key) :
    Option (Value key) :=
  (layout.readAtChecked offset key).1

theorem SlotLayout.readAt_sound {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (layout : SlotLayout Key Value) (offset : Nat) (key : Key) :
    layout.readAt offset key = layout.object.read key :=
  layout.readAtChecked_sound offset key

/-- Dynamic name lookup uses a hash index and then the checked array slot. -/
def SlotLayout.read {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (layout : SlotLayout Key Value) (key : Key) : Option (Value key) :=
  match layout.offsets.get? key with
  | some offset => layout.readAt offset key
  | none => layout.object.read key

theorem SlotLayout.read_sound {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (layout : SlotLayout Key Value) (key : Key) :
    layout.read key = layout.object.read key := by
  unfold SlotLayout.read
  split
  · exact layout.readAt_sound _ key
  · rfl

/-- A statically named field from the C4 suffix prefix. Its introducer's
position in the least-specific-first ancestry remains fixed in descendants. -/
structure SuffixField (Key : Type u) where
  key : Key
  offset : Nat
  introducedBy : String
  ancestorIndex : Nat

def SlotLayout.suffixField? {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (layout : SlotLayout Key Value) (key : Key) : Option (SuffixField Key) :=
  match layout.offsets.get? key with
  | none => none
  | some offset =>
      if offset < layout.suffixSize && layout.matchesAt offset key then
        let names := layout.suffixAncestors
        let origin := (List.range names.size).findSome? fun (index : Nat) =>
          match names[index]? with
          | none => none
          | some name =>
              match layout.object.plan.schema.declaration name with
              | none => none
              | some declaration =>
                  if declaration.directKeys.any (· == key) then
                    some (name, index)
                  else none
        origin.map fun (name, index) => ⟨key, offset, name, index⟩
      else none

/-- A fast hit requires both the introducing suffix ancestor and the field at
the fixed offset. A foreign same-name field falls back to keyed lookup. -/
def SuffixField.read {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (field : SuffixField Key) (layout : SlotLayout Key Value) :
    Option (Value field.key) × Bool :=
  if layout.suffixAncestors[field.ancestorIndex]? == some field.introducedBy then
    layout.readAtChecked field.offset field.key
  else (layout.object.read field.key, false)

theorem SuffixField.read_sound {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
  (field : SuffixField Key) (layout : SlotLayout Key Value) :
    (field.read layout).1 = layout.object.read field.key :=
  by
    unfold SuffixField.read
    split
    · exact layout.readAtChecked_sound field.offset field.key
    · rfl

/-- One access site holds only a speculative offset. It does not own a
descriptor or method body, so it can be reused across object layouts. -/
structure SlotAccessSite (Key : Type u) where
  key : Key
  offset : Option Nat := none

/-- The Boolean reports whether the speculative offset matched this layout.
On a miss, the site learns the new object's offset. -/
def SlotAccessSite.read {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (site : SlotAccessSite Key) (layout : SlotLayout Key Value) :
    Option (Value site.key) × SlotAccessSite Key × Bool :=
  match site.offset with
  | some offset =>
      let (value, hit) := layout.readAtChecked offset site.key
      if hit then (value, site, true)
      else
        let next := layout.offsets.get? site.key
        (value, { site with offset := next }, false)
  | none =>
      let next := layout.offsets.get? site.key
      (layout.read site.key, { site with offset := next }, false)

theorem SlotAccessSite.read_sound {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (site : SlotAccessSite Key) (layout : SlotLayout Key Value) :
    (site.read layout).1 = layout.object.read site.key := by
  unfold SlotAccessSite.read
  cases site.offset with
  | none => simp [layout.read_sound]
  | some offset =>
      cases checked : layout.readAtChecked offset site.key with
      | mk value hit =>
          have sound := layout.readAtChecked_sound offset site.key
          rw [checked] at sound
          cases hit <;> simpa [checked] using sound

/-- Recently learned offsets for each field name, shared by independently
created access sites. Offsets are speculative: every use checks the layout. -/
structure SharedSlotOffsets (Key : Type u) [BEq Key] [Hashable Key] where
  recent : Std.HashMap Key (List Nat) := {}

namespace SharedSlotOffsets

def capacity : Nat := 8

def candidates {Key : Type u} [BEq Key] [Hashable Key]
    (cache : SharedSlotOffsets Key) (key : Key) : List Nat :=
  (cache.recent.get? key).getD []

def remember {Key : Type u} [BEq Key] [Hashable Key]
    (cache : SharedSlotOffsets Key) (key : Key) (offset : Nat) :
    SharedSlotOffsets Key :=
  if (cache.candidates key).head? == some offset then cache
  else
    { recent := cache.recent.insert key
        ((offset :: (cache.candidates key).filter (· != offset)).take capacity) }

end SharedSlotOffsets

/-- A polymorphic field access site keeps four learned descriptor-offset
pairs. Its field key is fixed, while the object layout may vary on every call.
The descriptor fingerprint is only a hint; each offset is checked. -/
structure PolySlotAccessSite (Key : Type u) where
  key : Key
  recent : List (UInt64 × Nat) := []

namespace PolySlotAccessSite

def capacity : Nat := 4

def remember (site : PolySlotAccessSite Key) (shapeId : UInt64)
    (offset : Nat) :
    PolySlotAccessSite Key :=
  if site.recent.any (· == (shapeId, offset)) then site
  else { site with recent :=
      ((shapeId, offset) :: site.recent.filter (·.1 != shapeId)).take capacity }

/-- A checked probe does not evaluate the object on a mismatch. -/
private def matching {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (layout : SlotLayout Key Value) (key : Key) (offsets : List Nat) :
    Option Nat :=
  offsets.find? (layout.matchesAt · key)

private def readShared {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (site : PolySlotAccessSite Key) (shared : SharedSlotOffsets Key)
    (layout : SlotLayout Key Value) :
    Option (Value site.key) × PolySlotAccessSite Key ×
      SharedSlotOffsets Key × Bool × Bool :=
  match matching layout site.key (shared.candidates site.key) with
  | some offset =>
      ((layout.readAtChecked offset site.key).1,
        site.remember layout.shapeId offset,
        shared.remember site.key offset, false, true)
  | none =>
      let updated := layout.offsets.get? site.key
      (layout.read site.key,
        updated.elim site (site.remember layout.shapeId),
        updated.elim shared (shared.remember site.key), false, false)

private theorem readShared_sound {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (site : PolySlotAccessSite Key) (shared : SharedSlotOffsets Key)
    (layout : SlotLayout Key Value) :
    (readShared site shared layout).1 = layout.object.read site.key := by
  unfold readShared
  split
  · exact layout.readAtChecked_sound _ _
  · exact layout.read_sound _

/-- The Boolean pair records a local or shared hit. A local hit leaves the
shared cache alone. On a cold miss, keyed lookup supplies the authoritative
value and teaches both levels. -/
def read {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (site : PolySlotAccessSite Key) (shared : SharedSlotOffsets Key)
    (layout : SlotLayout Key Value) :
    Option (Value site.key) × PolySlotAccessSite Key ×
      SharedSlotOffsets Key × Bool × Bool :=
  match site.recent.find? (·.1 == layout.shapeId) with
  | none => readShared site shared layout
  | some (_, offset) =>
      let (value, hit) := layout.readAtChecked offset site.key
      if hit then
        (value, site, shared, true, false)
      else readShared site shared layout

theorem read_sound {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (site : PolySlotAccessSite Key) (shared : SharedSlotOffsets Key)
    (layout : SlotLayout Key Value) :
    (site.read shared layout).1 = layout.object.read site.key := by
  unfold read
  split
  · exact readShared_sound site shared layout
  · rename_i candidate found
    cases checked : layout.readAtChecked candidate site.key with
    | mk value hit =>
        cases hit
        · simpa [checked] using readShared_sound site shared layout
        · have sound := layout.readAtChecked_sound candidate site.key
          rw [checked] at sound
          simpa [checked] using sound

end PolySlotAccessSite

end LeanPoo.Object
