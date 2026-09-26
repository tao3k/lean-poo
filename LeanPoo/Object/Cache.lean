import LeanPoo.Object.Prepare

namespace LeanPoo.Object

universe u v

variable {Key : Type u} {Value : Key → Type v}
variable [BEq Key] [LawfulBEq Key] [Hashable Key]

/-- A cached value is tied to the prepared resolver and the final self. -/
structure CachedValue (prepared : Prepared Key Value) (self : Self Key Value)
    (key : Key) where
  value : Option (Value key)
  sound : value = prepared.resolve key self

/-- An explicit immutable instance cache. -/
structure Cache (prepared : Prepared Key Value) (self : Self Key Value) where
  entries : Std.DHashMap Key (CachedValue prepared self)

def Cache.empty (prepared : Prepared Key Value) (self : Self Key Value) :
    Cache prepared self :=
  ⟨{}⟩

/-- Observe cached state without evaluating a slot. The outer option
distinguishes an uncached key from an entry explicitly storing absence. -/
def Cache.peek {prepared : Prepared Key Value} {self : Self Key Value}
    (cache : Cache prepared self) (key : Key) : Option (Option (Value key)) :=
  ((Cache.entries cache).get? key).map
    (CachedValue.value (prepared := prepared) (self := self) (key := key))

/-- Carry previously evaluated entries to a new resolver only where the
caller proves that the resolved value is unchanged. A rejected entry is
absent from the new cache and will be evaluated by the ordinary read path. -/
def Cache.rebase {before : Prepared Key Value} {oldSelf : Self Key Value}
    (cache : Cache before oldSelf) (after : Prepared Key Value)
    (newSelf : Self Key Value) (reusable : Key → Prop)
    [DecidablePred reusable]
    (stable : ∀ key, reusable key →
      before.resolve key oldSelf = after.resolve key newSelf) :
    Cache after newSelf :=
  let entries := (Cache.entries cache).toList.foldl (fun result item =>
    let key := item.1
    let cached := item.2
    if canReuse : reusable key then
      result.insert key
        ⟨CachedValue.value (prepared := before) (self := oldSelf)
            (key := key) cached,
          (CachedValue.sound (prepared := before) (self := oldSelf)
            (key := key) cached).trans (stable key canReuse)⟩
    else result)
    ({} : Std.DHashMap Key (CachedValue after newSelf))
  ⟨entries⟩

/-- A miss evaluates one slot and caches an actual value; absence leaves the
cache unchanged, following object.ss .ref. -/
def Cache.read {prepared : Prepared Key Value} {self : Self Key Value}
    (cache : Cache prepared self) (key : Key) :
    Option (Value key) × Cache prepared self :=
  match (Cache.entries cache).get? key with
  | some entry =>
    (CachedValue.value (prepared := prepared) (self := self) (key := key) entry, cache)
  | none =>
    let value := prepared.resolve key self
    if value.isSome then
      (value, ⟨(Cache.entries cache).insert key ⟨value, rfl⟩⟩)
    else
      (value, cache)

theorem Cache.read_sound {prepared : Prepared Key Value}
    {self : Self Key Value} (cache : Cache prepared self) (key : Key) :
    (cache.read key).1 = prepared.resolve key self := by
  unfold Cache.read
  split
  · rename_i entry condition
    exact CachedValue.sound (prepared := prepared) (self := self) (key := key) entry
  · by_cases present : (prepared.resolve key self).isSome
    · simp [present]
    · simp [present]

/-- Looking up an absent slot does not grow the evaluated-value cache. -/
theorem Cache.read_absent {prepared : Prepared Key Value}
    {self : Self Key Value} (cache : Cache prepared self) (key : Key)
    (missing : prepared.resolve key self = none) :
    (cache.read key).2 = cache := by
  unfold Cache.read
  split
  · rfl
  · simp [missing]

/-- Required lookup uses the same cache and reports an absent method. -/
def Cache.ref {prepared : Prepared Key Value} {self : Self Key Value}
    (cache : Cache prepared self) (key : Key) :
    Except (LookupError Key) (Value key) × Cache prepared self :=
  let (value, updated) := cache.read key
  (match value with
    | some present => .ok present
    | none => .error (.noApplicableMethod key), updated)

theorem Cache.ref_sound {prepared : Prepared Key Value}
    {self : Self Key Value} (cache : Cache prepared self) (key : Key) :
    (cache.ref key).1 = prepared.plan.ref key self := by
  have sound := cache.read_sound key
  rw [prepared.resolve_sound] at sound
  unfold Cache.ref Plan.ref
  cases result : cache.read key with
  | mk value updated =>
    simp [result] at sound ⊢
    rw [sound]
    rfl

/-- Eagerly fill a finite selection of cache entries. -/
def Cache.force {prepared : Prepared Key Value} {self : Self Key Value}
    (cache : Cache prepared self) (keys : List Key) : Cache prepared self :=
  keys.foldl (fun current key => (current.read key).2) cache

end LeanPoo.Object
