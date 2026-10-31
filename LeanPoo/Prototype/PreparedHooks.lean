import LeanPoo.Prototype.GeneralizedInheritance

/-! Prepared generalized hooks advance the generalized-prototype future work.
Compilation is shared across finite observations, without asserting a Scheme knot
or callback termination. Native preparation must preserve this assembly equation. -/
namespace LeanPoo.Prototype.Generalized
/-- A compiled hook snapshot retains the exact ordered assembly it represents. -/
structure PreparedHooks (protocol : Protocol Raw Cooked Fragment) (fragments : List Fragment) where
  program : DelayedProto Cooked Raw Raw
  correct : program = protocol.assemble fragments
/-- Capture assembly once; the kernel equation is independent of runtime caching. -/
def Protocol.prepareHooks (protocol : Protocol Raw Cooked Fragment) (fragments : List Fragment) :
    PreparedHooks protocol fragments := ⟨protocol.assemble fragments, rfl⟩
/-- A prepared step cooks only the self boundary and retains delayed raw inheritance. -/
def PreparedHooks.step {protocol : Protocol Raw Cooked Fragment} {fragments : List Fragment}
    (snapshot : PreparedHooks protocol fragments) : Proto Raw Raw Raw :=
  fun final base => snapshot.program (Thunk.mk fun _ => protocol.cook final) (Thunk.mk fun _ => base)
/-- Hoisting compilation preserves each step, including the exact inherited base. -/
theorem PreparedHooks.step_eq {protocol : Protocol Raw Cooked Fragment} {fragments : List Fragment}
    (snapshot : PreparedHooks protocol fragments) : snapshot.step = protocol.step fragments := by
  unfold PreparedHooks.step Protocol.step
  rw [snapshot.correct]
/-- One shared compiled program preserves every finite-depth raw observation. -/
theorem PreparedHooks.iterate_eq {protocol : Protocol Raw Cooked Fragment} {fragments : List Fragment}
    (snapshot : PreparedHooks protocol fragments) (base seed : Raw) (depth : Nat) :
    FiniteFix.iterate snapshot.step base seed depth = protocol.approximate fragments base seed depth := by
  rw [snapshot.step_eq]
  rfl
/-- Compatible public-interface adaptation preserves finite raw construction at
all depths; compatibility is a premise, not an inferred law of arbitrary hooks. -/
theorem Protocol.approximate_reindexSelf (protocol : Protocol Raw Cooked Fragment)
    (view : Other → Cooked) (cook : Raw → Other)
    (compatible : ∀ raw, view (cook raw) = protocol.cook raw)
    (fragments : List Fragment) (base seed : Raw) (depth : Nat) :
    (protocol.reindexSelf view cook).approximate fragments base seed depth =
      protocol.approximate fragments base seed depth := by
  unfold Protocol.approximate
  rw [protocol.step_reindexSelf view cook compatible]
end LeanPoo.Prototype.Generalized

namespace LeanPoo.Prototype.Generalized
/-- Bind the exact compiled snapshot/base/depth, retaining a fresh raw seed for
EACH call. This is reader composition, not a cache of previously observed values. -/
def PreparedHooks.bindObserver {protocol : Protocol Raw Cooked Fragment} {fragments : List Fragment}
    (snapshot : PreparedHooks protocol fragments) (base : Raw) (depth : Nat) : Raw → Cooked :=
  fun seed => protocol.cook (FiniteFix.iterate snapshot.step base seed depth)
/-- Reusing the binding is valid for every seed, without a seed-equality premise. -/
theorem PreparedHooks.bindObserver_eq {protocol : Protocol Raw Cooked Fragment} {fragments : List Fragment}
    (snapshot : PreparedHooks protocol fragments) (base seed : Raw) (depth : Nat) :
    snapshot.bindObserver base depth seed = protocol.observe fragments base seed depth := by
  unfold PreparedHooks.bindObserver Protocol.observe
  rw [snapshot.iterate_eq]
/-- One shared cooked-self thunk models native delay/force. Lean's total functions
make sharing extensional; arbitrary Scheme callback effects are outside this law. -/
def Protocol.stepShared (protocol : Protocol Raw Cooked Fragment) (fragments : List Fragment) : Proto Raw Raw Raw :=
  fun final base =>
    let shared := Thunk.mk fun _ => protocol.cook final
    protocol.assemble fragments shared (Thunk.mk fun _ => base)
/-- Sharing the pure cooked self retains the original delayed construction equation. -/
theorem Protocol.stepShared_eq (protocol : Protocol Raw Cooked Fragment) (fragments : List Fragment) :
    protocol.stepShared fragments = protocol.step fragments := rfl
/-- Replace only the raw-to-public cooking strategy. Demand-driven native cooking
must satisfy the supplied extensional law on the public interface. -/
def Protocol.withCook (protocol : Protocol Raw Cooked Fragment) (cook : Raw → Cooked) :
    Protocol Raw Cooked Fragment := ⟨cook, protocol.compile⟩
/-- Pointwise-equivalent cooking preserves ALL finite observations, including
cooked self read by earlier dependent stages, not merely the final projection. -/
theorem Protocol.observe_withCook (protocol : Protocol Raw Cooked Fragment)
    (cook : Raw → Cooked) (same : ∀ raw, cook raw = protocol.cook raw)
    (fragments : List Fragment) (base seed : Raw) (depth : Nat) :
    (protocol.withCook cook).observe fragments base seed depth =
      protocol.observe fragments base seed depth := by
  have equal : cook = protocol.cook := funext same
  rw [equal]
  rfl
end LeanPoo.Prototype.Generalized

namespace LeanPoo.Prototype.Generalized
/-- Laws required to fuse local inheritance into one surrounding write. Native
object carriers require an extensional abstraction; ancestry/identity is excluded. -/
structure FocusLaws (get : Outer → Inner) (set : Inner → Outer → Outer) : Prop where
  get_set : ∀ value raw, get (set value raw) = value
  set_get : ∀ raw, set (get raw) raw = raw
  set_set : ∀ next previous raw, set next (set previous raw) = set next raw
/-- Focus a complete local delayed program through one raw getter/setter boundary. -/
def focusDelayed (get : Outer → Inner) (set : Inner → Outer → Outer)
    (view : Other → Cooked) (program : DelayedProto Cooked Inner Inner) :
    DelayedProto Other Outer Outer :=
  fun self parent => set (program (self.map view) (parent.map get)) parent.get
/-- Focus fusion needs actual lens laws, not merely two callbacks of the right shape. -/
theorem focusDelayed_compose (get : Outer → Inner) (set : Inner → Outer → Outer)
    (laws : FocusLaws get set) (view : Other → Cooked)
    (first rest : DelayedProto Cooked Inner Inner) :
    focusDelayed get set view (DelayedProto.compose first rest) =
      DelayedProto.compose (focusDelayed get set view first) (focusDelayed get set view rest) := by
  funext self parent
  simp only [focusDelayed, DelayedProto.compose, Thunk.map, Thunk.get]
  simp only [laws.get_set, laws.set_set]
/-- Per-fragment focused assembly agrees with one focused local assembly. -/
theorem focusDelayed_assemble (get : Outer → Inner) (set : Inner → Outer → Outer)
    (laws : FocusLaws get set) (view : Other → Cooked)
    (compiler : Compiler Inner Cooked Fragment) (fragments : List Fragment) :
    DelayedProto.composeAll (fragments.map (fun fragment => focusDelayed get set view (compiler fragment))) =
      focusDelayed get set view (DelayedProto.composeAll (fragments.map compiler)) := by
  induction fragments with
  | nil =>
    funext self parent
    exact (laws.set_get parent.get).symm
  | cons first rest ih =>
    change DelayedProto.compose (focusDelayed get set view (compiler first))
        (DelayedProto.composeAll (rest.map (fun fragment => focusDelayed get set view (compiler fragment)))) =
      focusDelayed get set view
        (DelayedProto.compose (compiler first) (DelayedProto.composeAll (rest.map compiler)))
    rw [ih, focusDelayed_compose get set laws view]
/-- Reference protocol lifts every fragment independently into surrounding storage. -/
def Protocol.focusRaw (protocol : Protocol Inner Cooked Fragment)
    (get : Outer → Inner) (set : Inner → Outer → Outer)
    (view : Other → Cooked) (cook : Outer → Other) : Protocol Outer Other Fragment :=
  ⟨cook, fun fragment => focusDelayed get set view (protocol.compile fragment)⟩
/-- Compile locally and write the surrounding focus once. The snapshot's assembly
certificate uses the supplied lens laws; empty assembly bypasses the lens entirely. -/
def Protocol.prepareFocused (protocol : Protocol Inner Cooked Fragment)
    (get : Outer → Inner) (set : Inner → Outer → Outer) (laws : FocusLaws get set)
    (view : Other → Cooked) (cook : Outer → Other) (fragments : List Fragment) :
    PreparedHooks (protocol.focusRaw get set view cook) fragments :=
  match fragments with
  | [] => (protocol.focusRaw get set view cook).prepareHooks []
  | first :: rest =>
    ⟨focusDelayed get set view (protocol.assemble (first :: rest)),
      (focusDelayed_assemble get set laws view protocol.compile (first :: rest)).symm⟩
/-- Focus fusion preserves every finite observation, with arbitrary base and seed. -/
theorem Protocol.prepareFocused_observe (protocol : Protocol Inner Cooked Fragment)
    (get : Outer → Inner) (set : Inner → Outer → Outer) (laws : FocusLaws get set)
    (view : Other → Cooked) (cook : Outer → Other) (fragments : List Fragment)
    (base seed : Outer) (depth : Nat) :
    (protocol.prepareFocused get set laws view cook fragments).bindObserver base depth seed =
      (protocol.focusRaw get set view cook).observe fragments base seed depth :=
  PreparedHooks.bindObserver_eq _ _ _ _
end LeanPoo.Prototype.Generalized

namespace LeanPoo.Prototype.Generalized
/-- Bridging law for the existing nested getter/setter method constructor: lifting
one local lensGen equals composing its getters/setters in the surrounding carrier. -/
theorem focusDelayed_lensGen (get : Outer → Inner) (set : Inner → Outer → Outer)
    (methodGet : Inner → Inherited) (methodSet : Result → Inner → Inner)
    (view : Other → Cooked)
    (wrapper : Fragment → Thunk Cooked → Thunk Inherited → Result) (fragment : Fragment) :
    focusDelayed get set view (lensGen methodGet methodSet wrapper fragment) =
      lensGen (fun raw => methodGet (get raw))
        (fun value raw => set (methodSet value (get raw)) raw)
        (fun item self parent => wrapper item (self.map view) parent) fragment := by
  rfl
end LeanPoo.Prototype.Generalized

namespace LeanPoo.Prototype.Generalized
/-- Retain immutable compiled hooks while selecting both raw inputs from each
current context. This shares code, never a cooked value or an approval decision. -/
def PreparedHooks.bindContextObserver {protocol : Protocol Raw Cooked Fragment}
    {fragments : List Fragment} (snapshot : PreparedHooks protocol fragments)
    (depth : Nat) (base seed : Context → Raw) : Context → Cooked :=
  fun context => snapshot.bindObserver (base context) depth (seed context)
/-- Every context is interpreted with its own base and seed. Reuse requires the
same protocol and fragment list; changing either requires a new certificate. -/
theorem PreparedHooks.bindContextObserver_eq {protocol : Protocol Raw Cooked Fragment}
    {fragments : List Fragment} (snapshot : PreparedHooks protocol fragments)
    (depth : Nat) (base seed : Context → Raw) (context : Context) :
    snapshot.bindContextObserver depth base seed context =
      protocol.observe fragments (base context) (seed context) depth :=
  snapshot.bindObserver_eq _ _ _
/-- Native standard-identity specialization can omit both selector captures and
calls. Arbitrary selector equality/effects are not assumed by this pure law. -/
theorem PreparedHooks.bindContextObserver_identity {protocol : Protocol Raw Cooked Fragment}
    {fragments : List Fragment} (snapshot : PreparedHooks protocol fragments) (depth : Nat) :
    snapshot.bindContextObserver depth id id =
      (fun raw => snapshot.bindObserver raw depth raw) := rfl
/-- Reader mapping is ordinary function composition. The older bind/pure form
has the same pure value semantics; host allocation and exceptions need controls. -/
theorem readerMap_eq_bindPure (action : Context → Value) (transform : Value → Result) :
    transform ∘ action = (fun context => (fun value => fun _ : Context => transform value) (action context) context) := rfl
/-- Projecting a reusable context observer preserves the current observation,
including any modeled refusal carried by the result type. -/
theorem PreparedHooks.mapContextObserver_eq {protocol : Protocol Raw Cooked Fragment}
    {fragments : List Fragment} (snapshot : PreparedHooks protocol fragments)
    (depth : Nat) (base seed : Context → Raw) (project : Cooked → Result) (context : Context) :
    (project ∘ snapshot.bindContextObserver depth base seed) context =
      project (protocol.observe fragments (base context) (seed context) depth) := by
  simp only [Function.comp_apply, PreparedHooks.bindContextObserver_eq]
end LeanPoo.Prototype.Generalized


namespace LeanPoo.Prototype.Generalized
/-- Transport finite observations across a raw representation relation. The step
and cooking premises must be established for the specific representation; they
are not automatically inferred for arbitrary native callbacks or object identity. -/
theorem Protocol.observe_related (source : Protocol Raw Cooked Fragment)
    (target : Protocol OtherRaw Cooked OtherFragment) (fragments : List Fragment)
    (otherFragments : List OtherFragment) (related : Raw → OtherRaw → Prop)
    (base : Raw) (otherBase : OtherRaw) (seed : Raw) (otherSeed : OtherRaw)
    (seedRelated : related seed otherSeed)
    (stepRelated : ∀ first second, related first second →
      related (source.step fragments first base) (target.step otherFragments second otherBase))
    (cookRelated : ∀ first second, related first second → source.cook first = target.cook second)
    (depth : Nat) : source.observe fragments base seed depth =
      target.observe otherFragments otherBase otherSeed depth :=
  cookRelated _ _ (FiniteFix.iterate_relation _ _ related base otherBase seed otherSeed
    seedRelated stepRelated depth)
end LeanPoo.Prototype.Generalized

namespace LeanPoo.Prototype.Generalized
/-- Supplied logical work prices for finite hook observations. Preparation covers
C3/declaration capture and compilation; observation includes cook/lens/bind work.
These are explicit bounds, not measured Scheme allocation or elapsed-time facts. -/
structure HookCosts where
  preparation : Nat
  observation : Nat
/-- Shared preparation pays once; every requested observation still pays its bound. -/
def HookCosts.shared (cost : HookCosts) (observations : Nat) : Nat :=
  cost.preparation + observations * cost.observation
/-- Rebuilding before each observation repeats the full preparation bound. -/
def HookCosts.repeated (cost : HookCosts) (observations : Nat) : Nat :=
  observations * (cost.preparation + cost.observation)
/-- Hoisting cannot increase this additive work bound when at least one observation
is demanded. Zero-demand preparation has no amortization guarantee. -/
theorem HookCosts.shared_le_repeated (cost : HookCosts) (observations : Nat)
    (demanded : 1 ≤ observations) : cost.shared observations ≤ cost.repeated observations := by
  have preparation := Nat.mul_le_mul_right cost.preparation demanded
  simp only [Nat.one_mul] at preparation
  calc
    cost.preparation + observations * cost.observation ≤
        observations * cost.preparation + observations * cost.observation :=
      Nat.add_le_add_right preparation _
    _ = observations * (cost.preparation + cost.observation) :=
      (Nat.mul_add observations cost.preparation cost.observation).symm
end LeanPoo.Prototype.Generalized

namespace LeanPoo.Prototype.Generalized
/-- Supplied work units distinguish binding, actual self demands, cooking frames,
field preparation and hook calls. Native GC/allocator costs require separate data. -/
structure ObservationWork where
  binding : Nat
  cookFrame : Nat
  field : Nat
  hook : Nat
/-- Separate fixed hook work from variable binding/cooking/field construction. -/
def ObservationWork.cost (prices : ObservationWork) (bindings cooks fields hooks : Nat) : Nat :=
  bindings * prices.binding + cooks * prices.cookFrame + fields * prices.field + hooks * prices.hook
/-- Demand cooking and shared binding reduce a supplied additive work bound only
under explicit operation-count inequalities. Promise allocation is not free: its
price must be included in the caller's frame/binding bounds. -/
theorem ObservationWork.cost_mono (prices : ObservationWork)
    (bindings cooks fields hooks oldBindings oldCooks oldFields : Nat)
    (bindingBound : bindings ≤ oldBindings) (cookBound : cooks ≤ oldCooks)
    (fieldBound : fields ≤ oldFields) :
    prices.cost bindings cooks fields hooks ≤ prices.cost oldBindings oldCooks oldFields hooks := by
  unfold ObservationWork.cost
  exact Nat.add_le_add_right (Nat.add_le_add
    (Nat.add_le_add (Nat.mul_le_mul_right _ bindingBound) (Nat.mul_le_mul_right _ cookBound))
    (Nat.mul_le_mul_right _ fieldBound)) _
end LeanPoo.Prototype.Generalized

namespace LeanPoo.Prototype.Generalized
/-- Logical surrounding writes: general construction writes once per fragment
per stage; focused assembly writes once per nonempty stage. No allocator price. -/
def focusedWrites (fragments stages : Nat) : Nat := stages * min 1 fragments
/-- The outer write-count bound decreases without changing local fragment count.
Extra preparation/projection costs must still be priced separately by callers. -/
theorem focusedWrites_le (fragments stages : Nat) : focusedWrites fragments stages ≤ stages * fragments :=
  Nat.mul_le_mul_left stages (Nat.min_le_right _ _)
/-- Nonempty focused assembly has precisely one logical outer write per stage. -/
theorem focusedWrites_nonempty (fragments stages : Nat) (nonempty : 1 ≤ fragments) :
    focusedWrites fragments stages = stages := by
  simp [focusedWrites, Nat.min_eq_left nonempty]
end LeanPoo.Prototype.Generalized

namespace LeanPoo.Prototype.Generalized
/-- Reusing one immutable declaration graph pays its preparation/binding once.
Fresh current observations remain charged on every call. Prices are supplied
logical work bounds, not measured bytes, execution time or a GC model. -/
def contextReuseWork (prepare bind observe calls : Nat) : Nat := prepare + bind + calls * observe
/-- A nonempty batch can amortize preparation and binding without omitting any
observation. Native closure elimination and heap history are separate questions. -/
theorem contextReuseWork_le (prepare bind observe calls : Nat) (nonempty : 1 ≤ calls) :
    contextReuseWork prepare bind observe calls ≤ calls * (prepare + bind + observe) := by
  unfold contextReuseWork
  have fixed : prepare + bind ≤ calls * (prepare + bind) := by
    simpa using Nat.mul_le_mul_right (prepare + bind) nonempty
  simpa [Nat.mul_add] using Nat.add_le_add_right fixed (calls * observe)
end LeanPoo.Prototype.Generalized

namespace LeanPoo.Prototype.Generalized
/-- Supplied prices distinguish common work from qualified descriptor creation,
first-slot-cache preparation and item grouping. Compact methods retain the same
body/closure work, which must be included in common. No native byte/time price. -/
def qualifiedItemWork (common descriptors caches grouping : Nat) : Nat :=
  common + descriptors + caches + grouping
/-- Known item-only representation removes the supplied redundant work. This
bound says nothing about allocator/GC history or unconditional wall-clock speed. -/
theorem itemWork_le (common descriptors caches grouping : Nat) :
    common ≤ qualifiedItemWork common descriptors caches grouping := by
  unfold qualifiedItemWork
  omega
end LeanPoo.Prototype.Generalized
