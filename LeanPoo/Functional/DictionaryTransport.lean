import LeanPoo.Prototype.DictionaryBridge
import LeanPoo.Functional.ContextObservation
import LeanPoo.Functional.SharedViews

/-! Use generated dictionary representations in existing provider selection,
joint requirement admission and one-context caches. Conversion preserves missing
errors, functions, dependent data/proofs and exact hit decisions. -/
namespace LeanPoo.Functional.DictionaryTransport
open Requirements
universe u v w x y
variable {Context : Type u} {Key : Type v}
variable {Value : Context → Key → Type w} {Fields : Context → Key → Type x}

abbrev Family (Value : Context → Key → Type w) (Fields : Context → Key → Type x) :=
  ∀ context key, Prototype.DictionaryBridge (Value context key) (Fields context key)

def expose (bridge : Family Value Fields) : ∀ c key, Value c key → Fields c key :=
  fun c key => (bridge c key).toFields

def reveal (bridge : Family Value Fields) : ∀ c key, Fields c key → Value c key :=
  fun c key => (bridge c key).fromFields

def inverse (bridge : Family Value Fields) : Family Fields Value := fun c key => (bridge c key).inverse

/-- Select functions without applying a context or invoking dictionary methods. -/
def provider (bridge : Family Value Fields) (source : Provider Context Key Value) : Provider Context Key Fields :=
  fun key => (source key).map (fun factory c => (bridge c key).toFields (factory c))

theorem provider_from_to (bridge : Family Value Fields) (source : Provider Context Key Value) :
    provider (inverse bridge) (provider bridge source) = source := by
  funext key
  cases selected : source key with
  | none => simp only [provider, selected, Option.map]
  | some factory =>
    simp only [provider, selected, Option.map]
    apply congrArg some
    funext context
    exact (bridge context key).from_to (factory context)

theorem select_provider (bridge : Family Value Fields) (names : List String)
    (source : String → Provider Context Key Value) :
    select names (fun name => provider bridge (source name)) = provider bridge (select names source) := by
  funext key
  induction names with
  | nil => rfl
  | cons name rest ih =>
    cases selected : source name key with
    | none => simpa only [select, provider, selected, Option.map] using ih
    | some _ => simp only [select, provider, selected, Option.map]

theorem assemble_provider (bridge : Family Value Fields) (order : C4.VerifiedOrder graph root)
    (source : String → Provider Context Key Value) :
    assemble order (fun name => provider bridge (source name)) = provider bridge (assemble order source) :=
  select_provider bridge order.output source

/-- Every heterogeneous success and the exact first missing error commute. -/
theorem prepare_provider (bridge : Family Value Fields) (source : Provider Context Key Value) (keys : List Key) :
    prepare (provider bridge source) keys = (prepare source keys).map (Requirements.observe (expose bridge)) := by
  induction keys with
  | nil => rfl
  | cons key rest ih =>
    cases selected : source key with
    | none => simp only [prepare, provider, selected, Option.map]; rfl
    | some factory =>
      simp only [prepare, provider, selected, Option.map]
      rw [ih]
      cases remaining : prepare source rest <;> rfl

theorem results_from_to (bridge : Family Value Fields) (data : Results Value context keys) :
    observeResults (reveal bridge) (observeResults (expose bridge) data) = data := by
  induction keys with
  | nil => cases data; rfl
  | cons key rest ih =>
    rcases data with ⟨head, tail⟩
    simp only [observeResults, expose, reveal, (bridge context key).from_to, ih tail]
    rfl

theorem results_to_from (bridge : Family Value Fields) (data : Results Fields context keys) :
    observeResults (expose bridge) (observeResults (reveal bridge) data) = data :=
  results_from_to (inverse bridge) data

variable {keys : List Key} {Claim : ∀ c, Results Value c keys → Prop}

/-- Arbitrary joint contracts are retained without proving them again. -/
def certified (bridge : Family Value Fields) (ready : Certified keys Claim) :
    Certified keys (fun c data => Claim c (observeResults (reveal bridge) data)) :=
  ready.observe (expose bridge) (fun c data => Claim c (observeResults (reveal bridge) data))
    (fun _ data valid => by rw [results_from_to]; exact valid)

theorem certified_build (bridge : Family Value Fields) (ready : Certified keys Claim) (context : Context) :
    observeResults (reveal bridge) ((certified bridge ready).build context).val = (ready.build context).val := by
  simp only [Certified.build_val, certified, Certified.observe_factories, build_observe, results_from_to]

/-- Convert retained built values through the existing observation cache API.
No provider/factory executes; contexts and arbitrary joint proofs are retained. -/
def slot (bridge : Family Value Fields) {ready : Certified keys Claim} (source : ContextSlot ready) :
    ContextSlot (certified bridge ready) :=
  source.observe (expose bridge) (fun c data => Claim c (observeResults (reveal bridge) data))
    (fun _ data valid => by rw [results_from_to]; exact valid)

theorem slot_read_value [DecidableEq Context] (bridge : Family Value Fields)
    {ready : Certified keys Claim} (source : ContextSlot ready) (context : Context) :
    observeResults (reveal bridge) ((slot bridge source).read context).1.val = (source.read context).1.val := by
  rw [ContextSlot.read_value, ContextSlot.read_value]
  simp only [certified, Certified.observe_factories, build_observe, results_from_to]

theorem slot_read_reused [DecidableEq Context] (bridge : Family Value Fields)
    {ready : Certified keys Claim} (source : ContextSlot ready) (context : Context) :
    ((slot bridge source).read context).2.2 = (source.read context).2.2 := by
  cases stored : source.retained with
  | none => simp only [slot, ContextSlot.observe, ContextSlot.read, stored, Option.map]
  | some pair =>
    rcases pair with ⟨previous, data⟩
    by_cases same : previous = context <;>
      simp [slot, ContextSlot.observe, ContextSlot.read, stored, same]

/-- Decode an aligned generated-field snapshot into the original dictionary
family, including its complete joint proof. Conversion calls no factory. -/
def snapshot (bridge : Family Value Fields) {ready : Certified keys Claim} {context : Context}
    (data : Snapshot (certified bridge ready) context) : Snapshot ready context :=
  ⟨observeResults (reveal bridge) data.val, by
    constructor
    · rw [data.property.1, ← Certified.build_val]
      exact certified_build bridge ready context
    · exact data.property.2⟩

/-- Read the generated-field cache once, decode one snapshot and invoke an
original-dictionary consumer. The next cache remains in field representation. -/
def consumeSnapshot [DecidableEq Context] (bridge : Family Value Fields)
    {ready : Certified keys Claim} (source : ContextSlot (certified bridge ready))
    {Output : Context → Type y} (construct : ∀ c, Snapshot ready c → Output c) (context : Context) :
    Output context × ContextSlot (certified bridge ready) × Bool :=
  source.consumeSnapshot (fun c data => construct c (snapshot bridge data)) context

theorem consumeSnapshot_state [DecidableEq Context] (bridge : Family Value Fields)
    {ready : Certified keys Claim} (source : ContextSlot (certified bridge ready))
    {Output : Context → Type y} (construct : ∀ c, Snapshot ready c → Output c) (context : Context) :
    (consumeSnapshot bridge source construct context).2 = (source.read context).2 := rfl

/-- Every dependent dictionary consumer agrees with the original uncached build,
even when it invokes retained typeclass methods and their law fields. -/
theorem consumeSnapshot_value [DecidableEq Context] (bridge : Family Value Fields)
    {ready : Certified keys Claim} (source : ContextSlot (certified bridge ready))
    {Output : Context → Type y} (construct : ∀ c, Snapshot ready c → Output c) (context : Context) :
    (consumeSnapshot bridge source construct context).1 =
      construct context ⟨build ready.factories context, rfl, ready.valid context⟩ := by
  unfold consumeSnapshot
  rw [ContextSlot.consumeSnapshot_value]
  congr 1
  apply Subtype.ext
  exact certified_build bridge ready context

end LeanPoo.Functional.DictionaryTransport
