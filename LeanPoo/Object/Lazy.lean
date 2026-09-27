import LeanPoo.Object.Incremental

/-!
Lazy runtime sharing for a proof-bearing instance. Each cell memoizes a value
from the total fixed point; the cell carries the equation that permits sound
reuse across a checked revision. This does not wrap the partial general
`Plan.memoize` knot.
-/

namespace LeanPoo.Object

universe u v

/-- A runtime thunk tied to one value of a certified fixed point. -/
structure LazyCell {Key : Type u} {Value : Key → Type v}
    {plan : Plan Key Value} (instanceValue : Instance Key Value plan)
    (key : Key) where
  thunk : Thunk (Option (Value key))
  sound : thunk.get = instanceValue.state key

/-- The selected keys share cells; other keys read the same certified state
directly. No separate slot-resolution semantics is introduced. -/
structure LazyInstance {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    {plan : Plan Key Value} (instanceValue : Instance Key Value plan) where
  keys : List Key
  cells : Std.DHashMap Key (LazyCell instanceValue)

private def LazyCell.fresh {Key : Type u} {Value : Key → Type v}
    {plan : Plan Key Value} (instanceValue : Instance Key Value plan)
    (key : Key) : LazyCell instanceValue key :=
  ⟨Thunk.mk (fun _ => instanceValue.state key), rfl⟩

/-- Allocate one call-by-need cell per selected key. -/
def Instance.lazy {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    {plan : Plan Key Value} (instanceValue : Instance Key Value plan)
    (keys : List Key) : LazyInstance instanceValue :=
  { keys
    cells := keys.foldl (fun cells key =>
      cells.insert key (LazyCell.fresh instanceValue key)) {} }

def LazyInstance.read {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    {plan : Plan Key Value} {instanceValue : Instance Key Value plan}
    (lazy : LazyInstance instanceValue) (key : Key) : Option (Value key) :=
  match lazy.cells.get? key with
  | some cell => cell.thunk.get
  | none => instanceValue.state key

theorem LazyInstance.read_sound {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    {plan : Plan Key Value} {instanceValue : Instance Key Value plan}
    (lazy : LazyInstance instanceValue) (key : Key) :
    lazy.read key = instanceValue.state key := by
  unfold LazyInstance.read
  split
  · rename_i cell condition
    exact cell.sound
  · rfl

/-- Which selected keys can retain their existing thunk after the revision. -/
def Revision.reusedLazyKeys {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    {oldPlan newPlan : Plan Key Value}
    {spec : Dependencies Key Value newPlan}
    {roots keys : List Key} (revision : Revision spec roots keys)
    {current : Instance Key Value oldPlan}
    (lazy : LazyInstance current) : List Key :=
  lazy.keys.filter fun key =>
    !(revision.impact.affected key) && lazy.cells.contains key

/-- Retain a thunk only when the checked dependency footprint proves its
value unchanged; install a fresh cell for each affected selected key. An
unforced retained thunk may keep its original instance closure alive. -/
def Revision.rebaseLazy {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    {oldPlan newPlan : Plan Key Value}
    {spec : Dependencies Key Value newPlan}
    {roots keys : List Key} (revision : Revision spec roots keys)
    (current : Instance Key Value oldPlan)
    (lazy : LazyInstance current)
    (sameResolver : ∀ key, key ∉ roots →
      oldPlan.resolve key current.state =
        newPlan.resolve key current.state) :
    LazyInstance revision.instanceValue :=
  let cells := lazy.keys.foldl (fun result key =>
    match lazy.cells.get? key with
    | some oldCell =>
        if stable : revision.impact.affected key = false then
          result.insert key
            ⟨oldCell.thunk,
              oldCell.sound.trans
                (revision.scheduled.stableState roots revision.impact
                  current revision.instanceValue sameResolver key stable)⟩
        else
          result.insert key (LazyCell.fresh revision.instanceValue key)
    | none =>
        result.insert key (LazyCell.fresh revision.instanceValue key))
      ({} : Std.DHashMap Key (LazyCell revision.instanceValue))
  ⟨lazy.keys, cells⟩

end LeanPoo.Object
