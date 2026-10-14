import LeanPoo.Prototype.Lens
import LeanPoo.Prototype.SkewLens
import LeanPoo.Prototype.DictionaryBridge

/-! A typed research extension of generalized prototypes: raw construction,
cooked final-self interfaces and fragment compilation share existing delayed
inheritance. Finite observations and witnessed closure do not add a knot axiom. -/
namespace LeanPoo.Prototype.Generalized
universe u v w x y

abbrev Compiler (Raw : Type u) (Cooked : Type v) (Fragment : Type w) :=
  Fragment → DelayedProto Cooked Raw Raw

/-- Adapt the existing monomorphic focus and generalized lens constructor. -/
def lensCompiler (focus : MonoLens Raw Method)
    (wrap : Fragment → Thunk Cooked → Thunk Method → Method) : Compiler Raw Cooked Fragment :=
  lensGen focus.view (fun value => focus.modify (fun _ => value)) wrap

/-- Restrict the self interface available to an independently written compiler. -/
def Compiler.viewSelf (view : Cooked → Narrow) (compiler : Compiler Raw Narrow Fragment) :
    Compiler Raw Cooked Fragment :=
  fun fragment self parent => compiler fragment (self.map view) parent

/-- Different fragment families share one raw carrier and cooked self. -/
def sumCompiler (left : Compiler Raw Cooked Left) (right : Compiler Raw Cooked Right) :
    Compiler Raw Cooked (Sum Left Right)
  | .inl fragment => left fragment
  | .inr fragment => right fragment

structure Protocol (Raw : Type u) (Cooked : Type v) (Fragment : Type w) where
  cook : Raw → Cooked
  compile : Compiler Raw Cooked Fragment

variable {Raw : Type u} {Cooked : Type v} {Fragment : Type w}

def Protocol.assemble (protocol : Protocol Raw Cooked Fragment) (fragments : List Fragment) :
    DelayedProto Cooked Raw Raw := DelayedProto.composeAll (fragments.map protocol.compile)

private theorem composeAll_append (front back : List (DelayedProto Cooked Raw Raw)) :
    DelayedProto.composeAll (front ++ back) =
      DelayedProto.compose (DelayedProto.composeAll front) (DelayedProto.composeAll back) := by
  induction front with
  | nil => rfl
  | cons first rest ih =>
    change DelayedProto.compose first (DelayedProto.composeAll (rest ++ back)) = _
    rw [ih]
    rfl

theorem Protocol.assemble_append (protocol : Protocol Raw Cooked Fragment) (front back : List Fragment) :
    protocol.assemble (front ++ back) =
      DelayedProto.compose (protocol.assemble front) (protocol.assemble back) := by
  simp only [Protocol.assemble, List.map_append, composeAll_append]

/-- Cook final self at the boundary, retaining raw inheritance internally. -/
def Protocol.step (protocol : Protocol Raw Cooked Fragment) (fragments : List Fragment) : Proto Raw Raw Raw :=
  fun final base => protocol.assemble fragments (Thunk.mk fun _ => protocol.cook final) (Thunk.mk fun _ => base)

def Protocol.approximate (protocol : Protocol Raw Cooked Fragment) (fragments : List Fragment)
    (base seed : Raw) (depth : Nat) : Raw := FiniteFix.iterate (protocol.step fragments) base seed depth

def Protocol.observe (protocol : Protocol Raw Cooked Fragment) (fragments : List Fragment)
    (base seed : Raw) (depth : Nat) : Cooked := protocol.cook (protocol.approximate fragments base seed depth)

theorem Protocol.approximate_succ (protocol : Protocol Raw Cooked Fragment) (fragments : List Fragment)
    (base seed : Raw) (depth : Nat) :
    protocol.approximate fragments base seed (depth + 1) =
      protocol.step fragments (protocol.approximate fragments base seed depth) base := rfl

theorem Protocol.step_cook_congr (protocol : Protocol Raw Cooked Fragment) (fragments : List Fragment)
    (base first second : Raw) (same : protocol.cook first = protocol.cook second) :
    protocol.step fragments first base = protocol.step fragments second base := by
  unfold Protocol.step
  rw [same]

/-- A triangular dependency becomes closed after two steps if cooking any
one-step result is constant. This is an explicit locality/stability premise. -/
theorem Protocol.stable_two (protocol : Protocol Raw Cooked Fragment) (fragments : List Fragment)
    (base seed : Raw) (value : Cooked)
    (reset : ∀ final, protocol.cook (protocol.step fragments final base) = value) :
    protocol.approximate fragments base seed 3 = protocol.approximate fragments base seed 2 := by
  apply protocol.step_cook_congr fragments base
  exact (reset _).trans (reset _).symm

/-- Change the public interface while exposing only a chosen view to fragments. -/
def Protocol.reindexSelf (protocol : Protocol Raw Cooked Fragment)
    (view : Other → Cooked) (cook : Raw → Other) : Protocol Raw Other Fragment :=
  ⟨cook, Compiler.viewSelf view protocol.compile⟩

theorem Protocol.assemble_reindexSelf (protocol : Protocol Raw Cooked Fragment)
    (view : Other → Cooked) (cook : Raw → Other) (fragments : List Fragment)
    (self : Thunk Other) (parent : Thunk Raw) :
    (protocol.reindexSelf view cook).assemble fragments self parent =
      protocol.assemble fragments (self.map view) parent := by
  induction fragments with
  | nil => rfl
  | cons fragment rest ih =>
    change protocol.compile fragment (self.map view)
      (Thunk.mk fun _ => (protocol.reindexSelf view cook).assemble rest self parent) =
      protocol.compile fragment (self.map view) (Thunk.mk fun _ => protocol.assemble rest (self.map view) parent)
    simp only [ih]

theorem Protocol.step_reindexSelf (protocol : Protocol Raw Cooked Fragment)
    (view : Other → Cooked) (cook : Raw → Other)
    (compatible : ∀ raw, view (cook raw) = protocol.cook raw) (fragments : List Fragment) :
    (protocol.reindexSelf view cook).step fragments = protocol.step fragments := by
  funext final base
  unfold Protocol.step
  rw [Protocol.assemble_reindexSelf]
  change protocol.assemble fragments (Thunk.mk fun _ => view (cook final)) _ = _
  rw [compatible]

/-- Closure requires an actual raw fixed-point equation, never a fuel claim. -/
structure Closed (protocol : Protocol Raw Cooked Fragment) (fragments : List Fragment) (base : Raw) where
  raw : Raw
  fixed : protocol.step fragments raw base = raw

def Closed.interface {protocol : Protocol Raw Cooked Fragment} {fragments : List Fragment} {base : Raw}
    (closed : Closed protocol fragments base) : Cooked := protocol.cook closed.raw

def Protocol.closeAt (protocol : Protocol Raw Cooked Fragment) (fragments : List Fragment)
    (base seed : Raw) (depth : Nat)
    (stable : protocol.approximate fragments base seed (depth + 1) = protocol.approximate fragments base seed depth) :
    Closed protocol fragments base :=
  ⟨protocol.approximate fragments base seed depth, stable⟩

theorem Protocol.stable (protocol : Protocol Raw Cooked Fragment) (fragments : List Fragment)
    (base seed : Raw) (depth : Nat)
    (stable : protocol.approximate fragments base seed depth = protocol.approximate fragments base seed (depth + 1))
    (extra : Nat) :
    protocol.approximate fragments base seed (depth + extra) = protocol.approximate fragments base seed depth :=
  FiniteFix.stable_forever _ _ _ _ stable extra

/-- A compiler can state a frame condition without assuming every lens is lawful. -/
theorem lensCompiler_frame (focus : MonoLens Raw Method)
    (wrap : Fragment → Thunk Cooked → Thunk Method → Method)
    (frame : Raw → Frame) (preserved : ∀ value raw, frame (focus.modify (fun _ => value) raw) = frame raw)
    (fragment : Fragment) (self : Thunk Cooked) (parent : Thunk Raw) :
    frame (lensCompiler focus wrap fragment self parent) = frame parent.get := by
  apply preserved

theorem Protocol.assemble_frame (protocol : Protocol Raw Cooked Fragment) (fragments : List Fragment)
    (frame : Raw → Frame)
    (preserved : ∀ fragment self parent, frame (protocol.compile fragment self parent) = frame parent.get)
    (self : Thunk Cooked) (parent : Thunk Raw) :
    frame (protocol.assemble fragments self parent) = frame parent.get := by
  induction fragments with
  | nil => rfl
  | cons fragment rest ih =>
    change frame (protocol.compile fragment self (Thunk.mk fun _ => protocol.assemble rest self parent)) = _
    rw [preserved]
    exact ih

theorem Protocol.approximate_frame (protocol : Protocol Raw Cooked Fragment) (fragments : List Fragment)
    (frame : Raw → Frame)
    (preserved : ∀ fragment self parent, frame (protocol.compile fragment self parent) = frame parent.get)
    (base seed : Raw) (depth : Nat) :
    frame (protocol.approximate fragments base seed (depth + 1)) = frame base :=
  protocol.assemble_frame fragments frame preserved _ _

theorem Closed.assembly {protocol : Protocol Raw Cooked Fragment} {fragments : List Fragment} {base : Raw}
    (closed : Closed protocol fragments base) :
    protocol.assemble fragments (Thunk.mk fun _ => closed.interface) (Thunk.mk fun _ => base) = closed.raw :=
  closed.fixed

/-- Transport raw storage and the cooked interface interface independently. -/
def Protocol.transport (protocol : Protocol Raw Cooked Fragment)
    (raw : DictionaryBridge Raw NewRaw) (interface : DictionaryBridge Cooked NewCooked) :
    Protocol NewRaw NewCooked Fragment where
  cook := fun value => interface.toFields (protocol.cook (raw.fromFields value))
  compile := fun fragment => DictionaryBridge.toDelayedPrototype interface raw raw (protocol.compile fragment)

theorem Protocol.assemble_transport (protocol : Protocol Raw Cooked Fragment)
    (raw : DictionaryBridge Raw NewRaw) (interface : DictionaryBridge Cooked NewCooked) (fragments : List Fragment) :
    (protocol.transport raw interface).assemble fragments =
      DictionaryBridge.toDelayedPrototype interface raw raw (protocol.assemble fragments) := by
  induction fragments with
  | nil =>
    funext self parent
    simp [Protocol.assemble, Protocol.transport, DelayedProto.composeAll, DelayedProto.Chain.ofList,
      DelayedProto.Chain.toProto, DelayedProto.identity, DictionaryBridge.toDelayedPrototype, Thunk.map, Thunk.get, raw.to_from]
  | cons fragment rest ih =>
    change DelayedProto.compose _ ((protocol.transport raw interface).assemble rest) =
      DictionaryBridge.toDelayedPrototype interface raw raw (DelayedProto.compose _ (protocol.assemble rest))
    rw [ih, DictionaryBridge.toDelayedPrototype_compose]
    rfl

theorem Protocol.step_transport (protocol : Protocol Raw Cooked Fragment)
    (raw : DictionaryBridge Raw NewRaw) (interface : DictionaryBridge Cooked NewCooked) (fragments : List Fragment) :
    (protocol.transport raw interface).step fragments =
      DictionaryBridge.toPrototype raw raw raw (protocol.step fragments) := by
  funext final base
  unfold Protocol.step
  rw [Protocol.assemble_transport]
  simp only [DictionaryBridge.toDelayedPrototype, Protocol.transport, DictionaryBridge.toPrototype]
  congr 2
  apply congrArg Thunk.mk
  funext token
  simp [Thunk.get, interface.from_to]

theorem Protocol.approximate_transport (protocol : Protocol Raw Cooked Fragment)
    (raw : DictionaryBridge Raw NewRaw) (interface : DictionaryBridge Cooked NewCooked)
    (fragments : List Fragment) (base seed : Raw) (depth : Nat) :
    (protocol.transport raw interface).approximate fragments (raw.toFields base) (raw.toFields seed) depth =
      raw.toFields (protocol.approximate fragments base seed depth) := by
  unfold Protocol.approximate
  rw [Protocol.step_transport]
  exact DictionaryBridge.iterate_toPrototype raw raw _ _ _ _

theorem Protocol.observe_transport (protocol : Protocol Raw Cooked Fragment)
    (raw : DictionaryBridge Raw NewRaw) (interface : DictionaryBridge Cooked NewCooked)
    (fragments : List Fragment) (base seed : Raw) (depth : Nat) :
    (protocol.transport raw interface).observe fragments (raw.toFields base) (raw.toFields seed) depth =
      interface.toFields (protocol.observe fragments base seed depth) := by
  unfold Protocol.observe
  rw [Protocol.approximate_transport]
  simp only [Protocol.transport, raw.from_to]

def Closed.transport {protocol : Protocol Raw Cooked Fragment} {fragments : List Fragment} {base : Raw}
    (closed : Closed protocol fragments base) (raw : DictionaryBridge Raw NewRaw)
    (interface : DictionaryBridge Cooked NewCooked) :
    Closed (protocol.transport raw interface) fragments (raw.toFields base) where
  raw := raw.toFields closed.raw
  fixed := by
    rw [Protocol.step_transport, DictionaryBridge.toPrototype_apply, closed.fixed]

theorem Closed.transport_interface {protocol : Protocol Raw Cooked Fragment} {fragments : List Fragment} {base : Raw}
    (closed : Closed protocol fragments base) (raw : DictionaryBridge Raw NewRaw)
    (interface : DictionaryBridge Cooked NewCooked) :
    (closed.transport raw interface).interface = interface.toFields closed.interface := by
  simp [Closed.interface, Closed.transport, Protocol.transport, raw.from_to]

end LeanPoo.Prototype.Generalized
