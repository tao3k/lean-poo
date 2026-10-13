import LeanPoo.Functional.MetadataFamily
import LeanPoo.Object.Ranked

/-! Close the actual captured metadata program using proved local reads.
The scheduler produces final factories and their closure equation; clients
provide dependency locality, rather than a precomputed final provider. -/
namespace LeanPoo.Functional.MetadataFamily
open Prototype
variable {Context Key : Type} {Value : Context → Key → Type}
  {plan : MetaPrototype.Prepared (FactoryRecord Context Key Value)}
  {base : FactoryRecord Context Key Value}

def resolver (plan : MetaPrototype.Prepared (FactoryRecord Context Key Value))
    (base : FactoryRecord Context Key Value) (key : Key) (self : Provider Context Key Value) :=
  apply plan { lookup := self } base key

/-- A layer observes only the declared final-self keys and its inherited slot.
This property composes through arbitrary parent orders and wrappers. -/
def LayerLocal (reads : Key → List Key) (layer : MetaPrototype.Layer (FactoryRecord Context Key Value)) : Prop :=
  ∀ key (left right oldLeft oldRight : FactoryRecord Context Key Value),
    (∀ dependency ∈ reads key, left.lookup dependency = right.lookup dependency) →
    oldLeft.lookup key = oldRight.lookup key →
    (layer (Thunk.pure left) (Thunk.pure oldLeft)).lookup key =
      (layer (Thunk.pure right) (Thunk.pure oldRight)).lookup key

theorem LayerLocal.identity (reads : Key → List Key) :
    LayerLocal (Context := Context) (Value := Value) reads DelayedProto.identity := by
  intro key left right oldLeft oldRight _ same
  exact same

theorem LayerLocal.compose {reads : Key → List Key} {child parent : MetaPrototype.Layer (FactoryRecord Context Key Value)}
    (childLocal : LayerLocal reads child) (parentLocal : LayerLocal reads parent) :
    LayerLocal reads (DelayedProto.compose child parent) := by
  intro key left right oldLeft oldRight same inherited
  exact childLocal key left right _ _ same (parentLocal key left right oldLeft oldRight same inherited)

theorem LayerLocal.slot [DecidableEq Key] (reads : Key → List Key) (key : Key)
    (compute : Thunk (FactoryRecord Context Key Value) →
      Thunk (Option (Factory Context (fun c => Value c key))) → Option (Factory Context (fun c => Value c key)))
    (locality : ∀ left right oldLeft oldRight,
      (∀ dependency ∈ reads key, left.lookup dependency = right.lookup dependency) →
      oldLeft = oldRight → compute (Thunk.pure left) (Thunk.pure oldLeft) = compute (Thunk.pure right) (Thunk.pure oldRight)) :
    LayerLocal reads (Object.recordSlotGen key compute) := by
  intro query left right oldLeft oldRight same inherited
  by_cases equal : query = key
  · subst query
    simp only [Object.recordSlotGen, dite_true]
    exact locality left right _ _ same inherited
  · simpa only [Object.recordSlotGen, equal, dite_false, Thunk.get, Thunk.pure] using inherited

structure Dependencies (plan : MetaPrototype.Prepared (FactoryRecord Context Key Value))
    (base : FactoryRecord Context Key Value) where
  keys : List Key
  reads : Key → List Key
  supported : ∀ key dependency, dependency ∈ reads key → key ∈ keys
  dependsOnlyOn : ∀ key (left right : Provider Context Key Value),
    (∀ dependency, dependency ∈ reads key → left dependency = right dependency) →
    resolver plan base key left = resolver plan base key right

structure Scheduled (spec : Dependencies plan base) where
  order : List Key
  ranked : RankedResolver (resolver plan base)
  edgeLower : ∀ key dependency, dependency ∈ spec.reads key →
    ranked.rank dependency < ranked.rank key

def Dependencies.schedule [BEq Key] [LawfulBEq Key] [Hashable Key]
    (spec : Dependencies plan base) : Except (LeanPoo.Object.DependencyError Key) (Scheduled spec) := do
  let order ← LeanPoo.Object.dependencyOrder spec.keys spec.reads
  let rank := fun key => order.idxOf key
  if checked : spec.keys.all (fun key => (spec.reads key).all
      (fun dependency => decide (rank dependency < rank key))) = true then
    have edgeLower : ∀ key dependency, dependency ∈ spec.reads key → rank dependency < rank key := by
      intro key dependency member
      exact of_decide_eq_true (List.all_eq_true.mp
        (List.all_eq_true.mp checked key (spec.supported key dependency member)) dependency member)
    return ⟨order, ⟨rank, by
      intro key left right lower
      exact spec.dependsOnlyOn key left right (fun dependency member => lower dependency (edgeLower key dependency member))⟩,
      edgeLower⟩
  else throw (.invalidOrder order)

def Scheduled.family {spec : Dependencies plan base} (scheduled : Scheduled spec) : MetadataFamily plan base :=
  ⟨scheduled.ranked.close, scheduled.ranked.closed⟩

def Dependencies.close [BEq Key] [LawfulBEq Key] [Hashable Key]
    (spec : Dependencies plan base) : Except (LeanPoo.Object.DependencyError Key) (MetadataFamily plan base) :=
  spec.schedule.map Scheduled.family

/-- Any other closed provider for this program/base agrees at every key. -/
theorem Scheduled.unique {spec : Dependencies plan base} (scheduled : Scheduled spec)
    (other : MetadataFamily plan base) (key : Key) : other.provider key = scheduled.family.provider key :=
  scheduled.ranked.unique other.provider other.closed key

/-- The automatically constructed family is the only closed family for the
actual captured program and base, including every factory and absent key. -/
theorem Dependencies.close_unique [BEq Key] [LawfulBEq Key] [Hashable Key]
    (spec : Dependencies plan base) (family : MetadataFamily plan base)
    (closed : spec.close = .ok family) (other : MetadataFamily plan base) (key : Key) :
    other.provider key = family.provider key := by
  cases checked : spec.schedule with
  | error error => simp [Dependencies.close, checked, Except.map] at closed
  | ok scheduled =>
    have same : scheduled.family = family := by simpa [Dependencies.close, checked, Except.map] using closed
    rw [← same]
    exact scheduled.unique other key

structure Construction (base : FactoryRecord Context Key Value) where
  plan : MetaPrototype.Prepared (FactoryRecord Context Key Value)
  dependencies : Dependencies plan base
  scheduled : Scheduled dependencies

def Construction.family (construction : Construction base) := construction.scheduled.family

/-- Prepare C3 and construct the unique closed factory family in one operation.
Layer-locality evidence is transferred through the exact captured registry. -/
def prepareClosed [BEq Key] [LawfulBEq Key] [Hashable Key]
    (name : String) (own : MetaPrototype.Layer (FactoryRecord Context Key Value)) (parents : List String)
    (registry : MetaPrototype.Registry (FactoryRecord Context Key Value)) (base : FactoryRecord Context Key Value)
    (keys : List Key) (reads : Key → List Key)
    (supported : ∀ key dependency, dependency ∈ reads key → key ∈ keys)
    (ownLocal : LayerLocal reads own)
    (parentLocal : ∀ name layer, MetaPrototype.lookupFunction registry name = .ok layer → LayerLocal reads layer) :
    Except (Sum String (LeanPoo.Object.DependencyError Key)) (Construction base) := do
  let metadata := constantMetadata own parents []
  match admitted : MetaPrototype.prepareChecked name metadata registry with
  | .error error => throw (.inl error)
  | .ok prepared =>
    have origin := MetaPrototype.prepareChecked_origin name metadata registry prepared admitted
    have actual : LayerLocal reads prepared.program := prepared.program_property _
      (LayerLocal.identity reads) (fun _ _ => LayerLocal.compose)
      (by
        intro layer selected
        rw [origin.2] at selected
        have same : own = layer := Option.some.inj selected
        exact same ▸ ownLocal)
      (by intro name layer selected; rw [origin.1] at selected; exact parentLocal name layer selected)
    let dependencies : Dependencies prepared base := ⟨keys, reads, supported, by
      intro key left right same
      exact actual key { lookup := left } { lookup := right } base base same rfl⟩
    let scheduled ← dependencies.schedule.mapError Sum.inr
    return ⟨prepared, dependencies, scheduled⟩

/-- Annotated parent metadata uses the same three source slots as checked preparation. -/
structure Parent (reads : Key → List Key) where
  name : String
  supers : List String
  precedence : List String
  layer : MetaPrototype.Layer (FactoryRecord Context Key Value)
  locality : LayerLocal reads layer

def Parent.registry {reads : Key → List Key} (parents : List (Parent (Context := Context) (Value := Value) reads)) :
    MetaPrototype.Registry (FactoryRecord Context Key Value) :=
  parents.map fun parent => (parent.name,
    ⟨Thunk.pure Record.empty, some (constantMetadata parent.layer parent.supers parent.precedence),
      fun _ inherited => inherited.get⟩)

theorem Parent.registry_local {reads : Key → List Key}
    (parents : List (Parent (Context := Context) (Value := Value) reads))
    (name : String) (layer : MetaPrototype.Layer (FactoryRecord Context Key Value))
    (selected : MetaPrototype.lookupFunction (Parent.registry parents) name = .ok layer) : LayerLocal reads layer := by
  unfold MetaPrototype.lookupFunction at selected
  cases found : (Parent.registry parents).find? (fun entry => entry.1 == name) with
  | none => simp [found] at selected
  | some entry =>
    obtain ⟨parent, _, same⟩ := List.mem_map.mp (List.mem_of_find?_eq_some found)
    subst entry
    have sameLayer : parent.layer = layer := by
      rw [found] at selected
      change Except.ok parent.layer = .ok layer at selected
      exact Except.ok.inj selected
    exact sameLayer ▸ parent.locality

end LeanPoo.Functional.MetadataFamily
