import LeanPoo.Functional.GeneralizedMOP
import LeanPoo.Object.DispatchTable
import Std.Data.DHashMap.Lemmas

/-! Checked heterogeneous generic families reuse DispatchTable and each generic's
existing construction, negative watches, invocation and cache laws. Future work. -/
namespace LeanPoo.Functional.GenericFamily
open Object DispatchExtension

/-- Pure heterogeneous constructor protocol: current support, empty-cache seeds,
method edits and negative watches. Policy/cooked inputs remain explicit. -/
structure Model (G Policy Cooked : Type) (Args Method Result : G → Type) where
  keys : List G
  seed : (key : G) → Policy → Cooked → Multimethod (Args key) (Method key) (Result key)
  seedEmpty : ∀ key policy cooked, (seed key policy cooked).cache = {}
  methods : (key : G) → Policy → Cooked → List (Edit (Args key) (Method key))
  watches : (key : G) → List (Watch (Args key))

variable {G Policy Cooked : Type} {Args Method Result : G → Type}
variable [DecidableEq G] [BEq G] [LawfulBEq G] [Hashable G]
variable (model : Model G Policy Cooked Args Method Result) (policy : Policy) (cooked : Cooked)

/-- Bind a generic to its actual source construction, negative-watch certificate
and sound warm cache under this model/policy/cooked triple. -/
structure Certified (key : G) (generic : Multimethod (Args key) (Method key) (Result key)) where
  origin : ∃ cold, patch (model.seed key policy cooked) (model.methods key policy cooked) = .ok cold ∧
    GeneralizedMOP.definition generic = GeneralizedMOP.definition cold
  negative : Certificate generic (model.watches key)
  sound : generic.CacheSound

/-- Privately staged heterogeneous table with a construction receipt for every installed entry. -/
structure Partial where
  table : DispatchTable G Args Method Result
  certified : ∀ key generic, table.get? key = some generic → Certified model policy cooked key generic

/-- Retain exact receipts for every requested generic and no missing signatures. -/
structure Family extends Partial model policy cooked where
  complete : ∀ key ∈ model.keys, (table.get? key).isSome = true

/-- Typed registration/negative-watch refusal or incomplete requested support.
The publisher must retain its old version when preparation fails. -/
inductive Failure where
  | registration (key : G) (error : MultimethodError)
  | negative (key : G) (generic : Multimethod (Args key) (Method key) (Result key))
      (conflict : Conflict generic (model.watches key))
  | incomplete

/-- Begin staging with an empty table and vacuous per-entry certificates. -/
def Partial.empty : Partial model policy cooked :=
  ⟨DispatchTable.empty,by intro key generic found; simp [DispatchTable.get?,DispatchTable.empty] at found⟩

/-- Install one already certified generic, preserving all other keys and receipts. -/
def Partial.install (prior : Partial model policy cooked) (key : G)
    (generic : Multimethod (Args key) (Method key) (Result key)) (receipt : Certified model policy cooked key generic) :
    Partial model policy cooked where
  table := prior.table.install key generic
  certified := by
    intro query next found
    by_cases same : key = query
    · subst query
      simp [DispatchTable.get?,DispatchTable.install] at found
      cases found
      exact receipt
    · apply prior.certified query next
      simpa [DispatchTable.get?,DispatchTable.install,Std.DHashMap.get?_insert,same,Ne.symm same] using found

/-- Skip an already installed key; otherwise patch an empty-cache seed and check
negative watches before installing it. Return the exact typed refusal on failure. -/
def Partial.build (prior : Partial model policy cooked) (key : G) :
    Except (Failure model) (Partial model policy cooked) :=
  if (prior.table.get? key).isSome then .ok prior else
  match applied : patch (model.seed key policy cooked) (model.methods key policy cooked) with
  | .error error => .error (.registration key error)
  | .ok generic => match check generic (model.watches key) with
    | .error conflict => .error (.negative key generic conflict)
    | .ok negative => .ok (prior.install model policy cooked key generic
        ⟨⟨generic,applied,rfl⟩,negative,patch_sound _ _ _
          ((model.seed key policy cooked).cacheSound_of_empty (model.seedEmpty key policy cooked)) applied⟩)

/-- Construct requested keys in order and certify completeness. Repeated keys
keep their first installation; registration/watch failure aborts the partial build. -/
def build : Except (Failure model) (Family model policy cooked) :=
  let rec go (prior : Partial model policy cooked) : List G → Except (Failure model) (Family model policy cooked)
    | [] => if complete : model.keys.all (fun key => (prior.table.get? key).isSome) = true then
        .ok ⟨prior,by intro key member; exact List.all_eq_true.mp complete key member⟩
      else .error .incomplete
    | key :: rest => match prior.build model policy cooked key with
      | .error error => .error error
      | .ok next => go next rest
  go (Partial.empty model policy cooked) model.keys

/-- Executable service-specific inputs, with exact source congruence. Equal
outputs or user-supplied clean-key flags cannot replace these obligations. -/
structure Projection where
  Context : G → Type
  project : (key : G) → Policy → Cooked → Context key
  seed_eq : ∀ key first before second after,
    project key first before = project key second after → model.seed key first before = model.seed key second after
  methods_eq : ∀ key first before second after,
    project key first before = project key second after → model.methods key first before = model.methods key second after

section sharedExpansion
omit [DecidableEq G] [BEq G] [LawfulBEq G] [Hashable G]

/-- Pure closed expansion shared by the seed and method constructors of one key.
The native mixin is opt-in: immutable value observations are modeled here, not
mutation or pointer identity of freshly allocated reconstruction objects. -/
structure SharedExpansion (Context Environment : G → Type) where
  expand : (key : G) → Context key → Environment key
  seed : (key : G) → Environment key → Multimethod (Args key) (Method key) (Result key)
  methods : (key : G) → Environment key → List (Edit (Args key) (Method key))

/-- Expand the same closed input separately for seed and method construction.
This reference expression exposes two expansion calls in the native protocol. -/
def SharedExpansion.separate (expansion : SharedExpansion (Args := Args) (Method := Method) (Result := Result) Context Environment)
    (key : G) (context : Context key) :=
  (expansion.seed key (expansion.expand key context), expansion.methods key (expansion.expand key context))

/-- Share one pure reconstructed environment between the existing constructors.
No method registration, negative check or later admission is removed. -/
def SharedExpansion.shared (expansion : SharedExpansion (Args := Args) (Method := Method) (Result := Result) Context Environment)
    (key : G) (context : Context key) :=
  let environment := expansion.expand key context
  (expansion.seed key environment, expansion.methods key environment)

/-- Pure sharing preserves both complete constructor inputs, not only sample outputs. -/
theorem SharedExpansion.shared_eq (expansion : SharedExpansion (Args := Args) (Method := Method) (Result := Result) Context Environment)
    (key : G) (context : Context key) : expansion.shared key context = expansion.separate key context := rfl

/-- Actual method patching has the same success or registration failure after sharing. -/
theorem SharedExpansion.patch_eq (expansion : SharedExpansion (Args := Args) (Method := Method) (Result := Result) Context Environment)
    (key : G) (context : Context key) :
    patch (expansion.shared key context).1 (expansion.shared key context).2 =
      patch (expansion.separate key context).1 (expansion.separate key context).2 := rfl

/-- Both paths patch the identical generic before checking identical negative watches.
This exposes the same success/refusal decision; patch_eq also preserves the
complete generic on which dependent certificates and conflict payloads rely. -/
theorem SharedExpansion.negative_eq (expansion : SharedExpansion (Args := Args) (Method := Method) (Result := Result) Context Environment)
    (key : G) (context : Context key) (watches : List (Watch (Args key))) :
    (patch (expansion.shared key context).1 (expansion.shared key context).2).map
      (fun generic => (check generic watches).toOption.isSome) =
    (patch (expansion.separate key context).1 (expansion.separate key context).2).map
      (fun generic => (check generic watches).toOption.isSome) := rfl

end sharedExpansion

/-- Closed construction environments make projection congruence structural.
Builders receive only their service's projected context. -/
structure Source where
  Context : G → Type
  project : (key : G) → Policy → Cooked → Context key
  seed : (key : G) → Context key → Multimethod (Args key) (Method key) (Result key)
  seedEmpty : ∀ key context, (seed key context).cache = {}
  methods : (key : G) → Context key → List (Edit (Args key) (Method key))
  keys : List G
  watches : (key : G) → List (Watch (Args key))

/-- Adapt closed per-key builders to the existing generic model; only project
feeds constructors, giving structural congruence rather than a clean-key hint. -/
def Source.asModel (source : Source (G := G) (Policy := Policy) (Cooked := Cooked)
    (Args := Args) (Method := Method) (Result := Result)) : Model G Policy Cooked Args Method Result where
  keys := source.keys
  seed := fun key policy cooked => source.seed key (source.project key policy cooked)
  seedEmpty := fun key policy cooked => source.seedEmpty key (source.project key policy cooked)
  methods := fun key policy cooked => source.methods key (source.project key policy cooked)
  watches := source.watches

/-- Derive exact seed/method congruence from equality of the closed projected inputs. -/
def Source.projection (source : Source (G := G) (Policy := Policy) (Cooked := Cooked)
    (Args := Args) (Method := Method) (Result := Result)) : Projection source.asModel where
  Context := source.Context
  project := source.project
  seed_eq := by intro key first before second after same; exact congrArg (source.seed key) same
  methods_eq := by intro key first before second after same; exact congrArg (source.methods key) same

variable {oldPolicy : Policy} {oldCooked : Cooked}

/-- Transport source provenance across equal projected inputs; retain the same
generic, warm-cache soundness and negative certificate without rebuilding. -/
def Certified.transport (projection : Projection model) (key : G)
    (generic : Multimethod (Args key) (Method key) (Result key))
    (receipt : Certified model oldPolicy oldCooked key generic)
    (same : projection.project key oldPolicy oldCooked = projection.project key policy cooked) :
    Certified model policy cooked key generic where
  origin := by
    obtain ⟨cold,generated,definition⟩ := receipt.origin
    exact ⟨cold, by rw [← projection.seed_eq key oldPolicy oldCooked policy cooked same,
      ← projection.methods_eq key oldPolicy oldCooked policy cooked same]; exact generated, definition⟩
  negative := receipt.negative
  sound := receipt.sound

/-- A clean branch installs the exact warm generic and transports its source,
negative-watch and cache-soundness receipts; no constructor/checker executes. -/
def Partial.refresh (projection : Projection model) [∀ key, DecidableEq (projection.Context key)]
    (old : Family model oldPolicy oldCooked) (prior : Partial model policy cooked) (key : G) :
    Except (Failure model) (Partial model policy cooked) :=
  if (prior.table.get? key).isSome then .ok prior else
  match found : old.table.get? key with
  | none => prior.build model policy cooked key
  | some generic =>
    if same : projection.project key oldPolicy oldCooked = projection.project key policy cooked then
      .ok (prior.install model policy cooked key generic
        (Certified.transport model policy cooked projection key generic (old.certified key generic found) same))
    else prior.build model policy cooked key

/-- Refresh the complete requested family. Reuse equal projected inputs with
existing certificates; rebuild changed entries and propagate the first refusal. -/
def refresh (projection : Projection model) [∀ key, DecidableEq (projection.Context key)]
    (old : Family model oldPolicy oldCooked) : Except (Failure model) (Family model policy cooked) :=
  let rec go (prior : Partial model policy cooked) : List G → Except (Failure model) (Family model policy cooked)
    | [] => if complete : model.keys.all (fun key => (prior.table.get? key).isSome) = true then
        .ok ⟨prior,by intro key member; exact List.all_eq_true.mp complete key member⟩
      else .error .incomplete
    | key :: rest => match prior.refresh model policy cooked projection old key with
      | .error error => .error error
      | .ok next => go next rest
  go (Partial.empty model policy cooked) model.keys

theorem Partial.refresh_retained (projection : Projection model) [∀ key, DecidableEq (projection.Context key)]
    (old : Family model oldPolicy oldCooked) (prior : Partial model policy cooked) (key : G)
    (generic : Multimethod (Args key) (Method key) (Result key))
    (pending : prior.table.get? key = none) (found : old.table.get? key = some generic)
    (same : projection.project key oldPolicy oldCooked = projection.project key policy cooked) :
    (prior.refresh model policy cooked projection old key).map (fun next => next.table.get? key) = .ok (some generic) := by
  unfold Partial.refresh
  split
  · rename_i occupied
    simp [pending] at occupied
  · split
    · rename_i missing
      rw [found] at missing
      contradiction
    · rename_i actual present
      have equal : actual = generic := Option.some.inj (present.symm.trans found)
      subst actual
      simp [Partial.install, DispatchTable.get?, DispatchTable.install, Except.map]

/-- A call warms one actual table entry. All receipts remain tied to the same
policy/cooked construction; other signatures retain their exact generic. -/
def Family.invoke (family : Family model policy cooked) (key : G) (args : Args key) :
    Except (DispatchTableError G) (Result key × Family model policy cooked) :=
  match found : family.table.get? key with
  | none => .error (.missing key)
  | some generic => match called : generic.call args with
    | .error error => .error (.dispatch error)
    | .ok (result,updated) =>
      let old := family.certified key generic found
      let receipt : Certified model policy cooked key updated := {
        origin := by
          obtain ⟨cold,generated,same⟩ := old.origin
          exact ⟨cold,generated,(GeneralizedMOP.call_definition generic updated args result called).trans same⟩
        negative := old.negative.afterCall args result updated called
        sound := generic.call_preserves old.sound args result updated called }
      let installed :=  family.toPartial.install model policy cooked key updated receipt
      .ok (result,⟨installed,by
        intro query member
        by_cases same : key = query
        · subst query; simp [installed,Partial.install,DispatchTable.get?,DispatchTable.install]
        · simpa [installed,Partial.install,DispatchTable.get?,DispatchTable.install,
            Std.DHashMap.get?_insert,same,Ne.symm same] using family.complete query member⟩)

/-- The wrapper uses the existing heterogeneous table call exactly. -/
theorem Family.invoke_table (family : Family model policy cooked) (key : G) (args : Args key) :
    (family.invoke model policy cooked key args).map (fun (result,next) => (result,next.table)) =
      family.table.call key args := by
  unfold Family.invoke
  split
  · rename_i found
    simp [DispatchTable.call,DispatchTable.lookup,found,bind,Except.bind,Except.map]
  · rename_i generic found
    split
    · rename_i error called
      simp [DispatchTable.call,DispatchTable.lookup,found,called,bind,Except.bind,Except.map,Except.mapError]
    · rename_i result updated called
      simp [DispatchTable.call,DispatchTable.lookup,found,called,bind,Except.bind,
        Except.map,Except.mapError,pure,Except.pure,Partial.install]

theorem Family.invoke_other (family : Family model policy cooked) (key : G) (args : Args key)
    (result : Result key) (next : Family model policy cooked)
    (called : family.invoke model policy cooked key args = .ok (result,next))
    (other : G) (different : key ≠ other) : next.table.get? other = family.table.get? other := by
  unfold Family.invoke at called
  split at called
  · contradiction
  · split at called
    · contradiction
    · cases called
      simp [Partial.install,DispatchTable.get?,DispatchTable.install,Std.DHashMap.get?_insert,
        different]

/-- Every signature keeps its complete dispatch definition during invocation,
including the called signature. This supports stable joint business checks. -/
theorem Family.invoke_definition (family : Family model policy cooked) (key : G) (args : Args key)
    (result : Result key) (next : Family model policy cooked)
    (called : family.invoke model policy cooked key args = .ok (result,next)) (query : G) :
    (next.table.get? query).map GeneralizedMOP.definition =
      (family.table.get? query).map GeneralizedMOP.definition := by
  by_cases same : key = query
  · subst query
    unfold Family.invoke at called
    split at called
    · contradiction
    · rename_i generic found
      split at called
      · contradiction
      · rename_i value updated worked
        cases called
        simp only [Partial.install, DispatchTable.get?, DispatchTable.install,
          Std.DHashMap.get?_insert_self, Option.map_some]
        rw [GeneralizedMOP.call_definition generic updated args result worked]
        simpa [DispatchTable.get?] using congrArg (Option.map GeneralizedMOP.definition) found.symm
  · rw [Family.invoke_other model policy cooked family key args result next called query same]

/-- Cache-free observations of every service are unchanged, including guards
and method combination. Certified `call_correct` connects these to actual calls. -/
theorem Family.invoke_observations (family : Family model policy cooked) (key : G) (args : Args key)
    (result : Result key) (next : Family model policy cooked)
    (called : family.invoke model policy cooked key args = .ok (result,next))
    (query : G) (probe : Args query) :
    (next.table.get? query).map (fun generic => generic.referenceCall probe) =
      (family.table.get? query).map (fun generic => generic.referenceCall probe) := by
  have same := congrArg (fun entry => entry.map (fun generic => generic.referenceCall probe))
    (family.invoke_definition model policy cooked key args result next called query)
  have forget : ∀ generic : Multimethod (Args query) (Method query) (Result query),
      (GeneralizedMOP.definition generic).referenceCall probe = generic.referenceCall probe := by
    intro generic; rfl
  simpa only [Option.map_map, Function.comp_def, forget] using same

/-- A predicate of dispatch definitions can retain its proof across a warm call.
Cache-dependent predicates deliberately do not meet this premise. -/
theorem Family.invoke_stable (property : Family model policy cooked → Prop)
    (stable : ∀ left right : Family model policy cooked,
      (∀ query, (right.table.get? query).map GeneralizedMOP.definition =
        (left.table.get? query).map GeneralizedMOP.definition) → property left → property right)
    (family : Family model policy cooked) (key : G) (args : Args key)
    (result : Result key) (next : Family model policy cooked)
    (called : family.invoke model policy cooked key args = .ok (result,next))
    (approved : property family) : property next :=
  stable family next (family.invoke_definition model policy cooked key args result next called) approved

omit [DecidableEq G] in
theorem Family.call_correct (family : Family model policy cooked) (key : G)
    (generic : Multimethod (Args key) (Method key) (Result key))
    (found : family.table.get? key = some generic) (args : Args key) :
    (generic.call args).map Prod.fst = generic.referenceCall args :=
  generic.call_correct (family.certified key generic found).sound args

end LeanPoo.Functional.GenericFamily
