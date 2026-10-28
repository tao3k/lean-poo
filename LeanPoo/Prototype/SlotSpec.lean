/-!
The four slot-spec forms are translated from François-René Rideau's
Gerbil-POO object.ss.
The upstream implementation uses Apache-2.0.
-/

namespace LeanPoo.Prototype

universe u v

/-- A delayed inherited computation. Keeping it delayed preserves the
Gerbil-POO distinction between overriding a slot and requesting its parent. -/
abbrev Next (α : Type v) := Unit → α

/-- An open method receives the final self and a delayed inherited result. -/
abbrev Method (Self : Type u) (α : Type v) := Self → Next α → α

def Method.identity : Method Self α := fun _ inherited => inherited ()

/-- Child methods may choose whether to request their parent's result. -/
def Method.compose (child parent : Method Self α) : Method Self α :=
  fun self inherited => child self (fun _ => parent self inherited)

theorem Method.compose_identity_left (method : Method Self α) :
    Method.compose Method.identity method = method := by
  funext self inherited
  rfl

theorem Method.compose_identity_right (method : Method Self α) :
    Method.compose method Method.identity = method := by
  funext self inherited
  rfl

theorem Method.compose_assoc (outer middle inner : Method Self α) :
    Method.compose (Method.compose outer middle) inner =
      Method.compose outer (Method.compose middle inner) := by
  funext self inherited
  rfl

/-- The semantic target of Gerbil-POO's object/slot-spec syntax normalization. -/
inductive SlotSpec (Self : Type u) (α : Type v) where
  | constant (value : α)
  | thunk (value : Next α)
  | self (compute : Self → α)
  | computed (compute : Self → Next α → α)

/-- One interpretation owns all slot-spec forms. -/
def SlotSpec.eval (spec : SlotSpec Self α) (self : Self)
    (next : Next α) : α :=
  match spec with
  | .constant value => value
  | .thunk value => value ()
  | .self compute => compute self
  | .computed compute => compute self next

def SlotSpec.toMethod (spec : SlotSpec Self α) : Method Self α :=
  fun self inherited => spec.eval self inherited

/-- The common inherited-value modifier represented by the computed form. -/
def SlotSpec.modify (f : α → α) : SlotSpec Self α :=
  .computed (fun _ next => f (next ()))

/-- The inherited instance method is selected by the class's C4 slot chain.
The receiver is supplied only when the resulting method is called, so it may
belong to a subclass of the class that contributed this specification. -/
abbrev NextInstanceMethod (Receiver : Type u) (Result : Type v) :=
  Receiver → Option Result

/-- Focus an open class specification onto an instance method. The class
`self` is deliberately unused; method dispatch uses the eventual receiver. -/
def SlotSpec.instanceMethod {ClassSelf : Type} {Receiver : Type u}
    {Result : Type v}
    (body : NextInstanceMethod Receiver Result → Receiver → Result) :
    SlotSpec ClassSelf (Option (Receiver → Result)) :=
  .computed fun _ inherited =>
    let parent := Thunk.mk inherited
    some fun receiver =>
      body (fun target => parent.get.map (fun method => method target)) receiver

/-- A base method does not request an inherited method. -/
def SlotSpec.baseInstanceMethod {ClassSelf : Type} {Receiver : Type u}
    {Result : Type v} (body : Receiver → Result) :
    SlotSpec ClassSelf (Option (Receiver → Result)) :=
  .constant (some body)

theorem SlotSpec.instanceMethod_eval {ClassSelf : Type}
    {Receiver : Type u} {Result : Type v}
    (body : NextInstanceMethod Receiver Result → Receiver → Result)
    (self : ClassSelf)
    (inherited : Next (Option (Receiver → Result)))
    (receiver : Receiver) :
    ((SlotSpec.instanceMethod body).eval self inherited).map
        (fun method => method receiver) =
      some (body (fun target => (Thunk.mk inherited).get.map
        (fun method => method target)) receiver) := rfl

theorem SlotSpec.baseInstanceMethod_eval {ClassSelf : Type}
    {Receiver : Type u} {Result : Type v}
    (body : Receiver → Result) (self : ClassSelf)
    (inherited : Next (Option (Receiver → Result)))
    (receiver : Receiver) :
    ((SlotSpec.baseInstanceMethod body).eval self inherited).map
      (fun method => method receiver) = some (body receiver) := rfl

/-- Only explicit super-independent constructors discard earlier contributions.
Computed Functions remain opaque, even if one happens not to request super. -/
def SlotSpec.discardsSuper : SlotSpec Self α → Bool
  | .computed _ => false
  | _ => true

/-- Construction retains a most-specific-first stack, resetting at an override. -/
def SlotSpec.push (saved : List (SlotSpec Self α)) (spec : SlotSpec Self α) :=
  if spec.discardsSuper then [spec] else spec :: saved

/-- Interpret a retained stack using the original SlotSpec evaluator. No body
is forced merely by producing this delayed result. -/
def SlotSpec.compile (specs : List (SlotSpec Self α)) (self : Self) (next : Next α) : Next α :=
  match specs with
  | [] => next
  | spec :: tail => fun _ => spec.eval self (SlotSpec.compile tail self next)

/-- Discarding a prefix preserves every result, including opaque Function values
or explicit error results when α is an Except type. -/
theorem SlotSpec.compile_push (saved : List (SlotSpec Self α)) (spec : SlotSpec Self α)
    (self : Self) (next : Next α) :
    SlotSpec.compile (SlotSpec.push saved spec) self next =
      (fun _ => spec.eval self (SlotSpec.compile saved self next)) := by
  cases spec <;> rfl

/-- The chronological source fold and retained-stack interpretation agree. -/
theorem SlotSpec.compile_fold (source saved : List (SlotSpec Self α))
    (self : Self) (next : Next α) :
    SlotSpec.compile (source.foldl SlotSpec.push saved) self next =
      source.foldl (fun inherited spec => fun _ => spec.eval self inherited)
        (SlotSpec.compile saved self next) := by
  induction source generalizing saved with
  | nil => rfl
  | cons spec tail ih =>
    simp only [List.foldl]
    rw [ih, SlotSpec.compile_push]

/-- Validate EVERY chronological row, including malformed shadowed prefixes.
Successful rows may compact immediately, but never bypass a later refusal. -/
def SlotSpec.prepare (source : List (Except E (SlotSpec Self α)))
    (saved : List (SlotSpec Self α) := []) : Except E (List (SlotSpec Self α)) :=
  match source with
  | [] => .ok saved
  | .error cause :: _ => .error cause
  | .ok spec :: tail => SlotSpec.prepare tail (SlotSpec.push saved spec)

/-- A later constant override cannot hide an earlier validation failure. -/
theorem SlotSpec.prepare_refused (earlier : List (SlotSpec Self α)) (cause : E)
    (suffix : List (Except E (SlotSpec Self α))) (saved : List (SlotSpec Self α)) :
    SlotSpec.prepare (earlier.map Except.ok ++ .error cause :: suffix) saved = .error cause := by
  induction earlier generalizing saved with
  | nil => rfl
  | cons spec tail ih => simpa [SlotSpec.prepare] using ih (SlotSpec.push saved spec)

/-- Fully admitted input compacts exactly once through the original source fold. -/
theorem SlotSpec.prepare_ready (source saved : List (SlotSpec Self α)) :
    SlotSpec.prepare (E := E) (source.map Except.ok) saved =
      .ok (source.foldl SlotSpec.push saved) := by
  induction source generalizing saved with
  | nil => rfl
  | cons spec tail ih => simpa [SlotSpec.prepare] using ih (SlotSpec.push saved spec)

/-- A super-independent contribution makes all previous construction irrelevant. -/
theorem SlotSpec.reset_suffix (earlier suffix : List (SlotSpec Self α))
    (spec : SlotSpec Self α) (reset : spec.discardsSuper = true) :
    (earlier ++ spec :: suffix).foldl SlotSpec.push [] =
      suffix.foldl SlotSpec.push [spec] := by
  simp [List.foldl_append, SlotSpec.push, reset]

/-- Prefix-independent means final self is still supplied at invocation. -/
theorem SlotSpec.compile_self (f : Self → α) (saved : List (SlotSpec Self α))
    (self : Self) (next : Next α) :
    SlotSpec.compile (SlotSpec.push saved (.self f)) self next = (fun _ => f self) := rfl

/-- Keeping computed constructors is mandatory; body inspection is not admission. -/
theorem SlotSpec.push_computed (f : Self → Next α → α) (saved : List (SlotSpec Self α)) :
    SlotSpec.push saved (.computed f) = .computed f :: saved := rfl

/-- A retained stack never grows by more than one entry per admitted source row. -/
theorem SlotSpec.retained_bound (source saved : List (SlotSpec Self α)) :
    (source.foldl SlotSpec.push saved).length ≤ saved.length + source.length := by
  induction source generalizing saved with
  | nil => simp
  | cons spec tail ih =>
    have h := ih (SlotSpec.push saved spec)
    have step : (SlotSpec.push saved spec).length ≤ saved.length + 1 := by
      simp only [SlotSpec.push]
      split <;> simp
    simp only [List.foldl, List.length_cons]
    omega

/-- Logical preparation counts one source visit and one retained reversal cell.
Hash probes, admission, descriptor preparation, closures, GC and wall time are extra. -/
def SlotSpec.preparationWork (source : List (SlotSpec Self α)) :=
  source.length + (source.foldl SlotSpec.push []).length

/-- Compaction adds at most a second linear pass; it is not free preparation. -/
theorem SlotSpec.preparationWork_bound (source : List (SlotSpec Self α)) :
    SlotSpec.preparationWork source ≤ 2 * source.length := by
  have h := SlotSpec.retained_bound source []
  simp only [List.length_nil, Nat.zero_add] at h
  simp only [SlotSpec.preparationWork]
  omega

/-- Source-level builder requests: thunk reuses its original procedure; the other
three constructors request an effective closure. Physical allocation may differ. -/
def SlotSpec.builderRequest : SlotSpec Self α → Nat
  | .thunk _ => 0
  | _ => 1

/-- Count only effective builders, excluding defaults/metadata, list preparation,
fallback construction, MOP hooks, lookup, collector and compiler costs. -/
def SlotSpec.builderWork (specs : List (SlotSpec Self α)) : Nat :=
  (specs.map SlotSpec.builderRequest).sum

/-- No retained constructor requests more than one effective builder. -/
theorem SlotSpec.builderWork_bound (specs : List (SlotSpec Self α)) :
    SlotSpec.builderWork specs ≤ specs.length := by
  induction specs with
  | nil => simp [SlotSpec.builderWork]
  | cons spec tail ih =>
    cases spec <;> simp [SlotSpec.builderWork, SlotSpec.builderRequest] at * <;> omega

/-- Prefix removal erases its builder requests, not its validation/preparation cost. -/
theorem SlotSpec.builderWork_reset (earlier suffix : List (SlotSpec Self α))
    (spec : SlotSpec Self α) (reset : spec.discardsSuper = true) :
    SlotSpec.builderWork ((earlier ++ spec :: suffix).foldl SlotSpec.push []) =
      SlotSpec.builderWork (suffix.foldl SlotSpec.push [spec]) := by
  rw [SlotSpec.reset_suffix earlier suffix spec reset]

end LeanPoo.Prototype
