import LeanPoo.Functional.RecursiveRevision

/-! Named finite catalogs across support edits. Reuse the existing catalog check,
finite collection, all-or-error recursive closure and selective revision. Host
recipes must declare every read, use stable names and supply coherent dependency
invalidation; callback/source/identity correspondence and sequential commit remain
premises. This advances generalized MOP future work. -/
namespace LeanPoo.Functional.RecursiveMigration
open RecursiveValidation RecursiveRevision
variable {Key : Type}

/-- Checked names have no duplicates and at least one publishable node. -/
structure Catalog (Key : Type) where
  names : List Key
  unique : names.Nodup
  nonempty : names ≠ []

/-- Existing named-catalog preflight supplies the actual finite index carrier. -/
def catalog [DecidableEq Key] (limit : Nat) (names references : List Key) : Except CatalogError (Catalog Key) :=
  match good : checkCatalog limit names references with
  | .error cause => .error cause
  | .ok () =>
    let checked := (catalog_success limit names references).mp good
    .ok ⟨names,checked.2.2.1,checked.1⟩

/-- Index positions are representation details; the stable component name owns identity. -/
def Catalog.name (source : Catalog Key) (index : Fin source.names.length) : Key := source.names[index]

/-- Every exposed index names a currently supported component. -/
theorem Catalog.name_mem (source : Catalog Key) (index : Fin source.names.length) :
    source.name index ∈ source.names := List.getElem_mem index.isLt

/-- Duplicate-free catalog lowering cannot merge distinct positions. -/
theorem Catalog.name_injective (source : Catalog Key) : Function.Injective source.name := by
  intro left right same
  apply Fin.ext
  exact source.unique.getElem_inj.mp same

variable [DecidableEq Key]

/-- Resolve a name to its actual current position, refusing removed/unknown names. -/
def Catalog.index (source : Catalog Key) (key : Key) : Option (Fin source.names.length) :=
  if present : key ∈ source.names then
    some ⟨source.names.idxOf key,List.idxOf_lt_length_of_mem present⟩ else none

/-- Reindexing preserves the submitted name rather than the old numeric row. -/
theorem Catalog.index_name (source : Catalog Key) (key : Key) (index : Fin source.names.length)
    (found : source.index key = some index) : source.name index = key := by
  unfold Catalog.index at found
  split at found
  · cases found
    exact List.getElem_idxOf _
  · contradiction

/-- Looking up a supported row recovers that same row despite catalog reordering. -/
theorem Catalog.index_self (source : Catalog Key) (index : Fin source.names.length) :
    source.index (source.name index) = some index := by
  cases found : source.index (source.name index) with
  | none => simp [Catalog.index,source.name_mem index] at found
  | some other =>
    have same := source.name_injective (source.index_name _ other found)
    subst other
    rfl

/-- Lower ordered references, preserving duplicate shared aliases and edge order. -/
def lowerLinks (source : Catalog Key) : List Key → Except CatalogError (List (Fin source.names.length))
  | [] => .ok []
  | key :: rest => match source.index key with
    | none => .error .missingReference
    | some index => (lowerLinks source rest).map (index :: ·)

/-- Every successfully lowered edge denotes precisely its submitted target name. -/
theorem lowerLinks_names (source : Catalog Key) (keys : List Key) (indices : List (Fin source.names.length))
    (good : lowerLinks source keys = .ok indices) : indices.map source.name = keys := by
  induction keys generalizing indices with
  | nil => simp [lowerLinks] at good; subst indices; rfl
  | cons key rest ih =>
    cases lookup : source.index key with
    | none => simp [lowerLinks,lookup] at good
    | some index =>
      cases tail : lowerLinks source rest with
      | error cause => simp [lowerLinks,lookup,tail,Except.map] at good
      | ok remaining =>
        have same : index :: remaining = indices := by simpa [lowerLinks,lookup,tail,Except.map] using good
        subst indices
        simp [source.index_name key index lookup,ih remaining tail]

/-- Resolve every dependency before shape validation or any node rebuilding. -/
def lower (source : Catalog Key) (dependencies : Key → List Key) :=
  collect source.names.length (fun index => lowerLinks source (dependencies (source.name index)))

/-- Whole-directory lowering preserves named sharing through all current positions. -/
theorem lower_names (source : Catalog Key) (dependencies : Key → List Key)
    (edges : Fin source.names.length → List (Fin source.names.length)) (good : lower source dependencies = .ok edges)
    (index : Fin source.names.length) : (edges index).map source.name = dependencies (source.name index) :=
  lowerLinks_names source _ _ (collect_apply _ edges good index)

/-- Ledger entries survive removal. Membership changes and current dirty nodes
advance generations, preventing later same-key additions from reviving old references. -/
def advanceKey (old next : List Key) (dirty : Key → Bool) (generation : Key → Nat) (key : Key) : Nat :=
  if (decide (key ∈ old) != decide (key ∈ next)) || (decide (key ∈ next) && dirty key)
  then generation key + 1 else generation key

/-- No support edit can decrease a name's retained tombstone generation. -/
theorem generation_monotone (old next : List Key) (dirty : Key → Bool) (generation : Key → Nat) (key : Key) :
    generation key ≤ advanceKey old next dirty generation key := by unfold advanceKey; split <;> omega

/-- Removing a component advances its tombstone even though no receiver is published. -/
theorem removed_advance (old next : List Key) (dirty : Key → Bool) (generation : Key → Nat) (key : Key)
    (before : key ∈ old) (after : key ∉ next) : advanceKey old next dirty generation key = generation key + 1 := by
  simp [advanceKey,before,after]

/-- Current references require both membership and the exact named generation. -/
def recognizes (names : List Key) (generation : Key → Nat) (key : Key) (reference : Key × Nat) : Bool :=
  decide (key ∈ names ∧ reference = (key,generation key))

/-- Removed names cannot expose a latent old binding through reference recognition. -/
theorem removed_refused (names : List Key) (generation : Key → Nat) (key : Key) (reference : Key × Nat)
    (removed : key ∉ names) : recognizes names generation key reference = false := by simp [recognizes,removed]

/-- A same-key addition after any gap refuses every reference at or before the
current ledger generation. Equal recipe/payload values do not authorize revival. -/
theorem added_old_refused (old next : List Key) (dirty : Key → Bool) (generation : Key → Nat)
    (key : Key) (older : Nat) (before : key ∉ old) (after : key ∈ next) (age : older ≤ generation key) :
    recognizes next (advanceKey old next dirty generation) key (key,older) = false := by
  have different : older ≠ generation key + 1 := by omega
  simp [recognizes,advanceKey,before,after,different]

/-- Current dirty targets reject references from any earlier ledger generation,
including surviving names whose computed dependency or shared provider changed. -/
theorem dirty_old_refused (old next : List Key) (dirty : Key → Bool) (generation : Key → Nat)
    (key : Key) (older : Nat) (after : key ∈ next) (changed : dirty key = true) (age : older ≤ generation key) :
    recognizes next (advanceKey old next dirty generation) key (key,older) = false := by
  have different : older ≠ generation key + 1 := by omega
  simp [recognizes,advanceKey,after,changed,different]

/-- Removal followed by same-name readdition rejects the original reference even
when every intervening unrelated round retained the same payload and recipe. -/
theorem gap_refused (old middle next : List Key) (first second : Key → Bool) (generation : Key → Nat)
    (key : Key) (before : key ∈ old) (removed : key ∉ middle) (returned : key ∈ next) :
    recognizes next (advanceKey middle next second (advanceKey old middle first generation))
      key (key,generation key) = false := by
  apply added_old_refused middle next second _ key _ removed returned
  rw [removed_advance old middle first generation key before removed]
  omega

/-- A current catalog's identity map uses stable names, never positions alone. -/
def canonical (source : Catalog Key) (generation : Key → Nat) (index : Fin source.names.length) : Key × Nat :=
  (source.name index,generation (source.name index))

/-- Clean survivors retain identity when insertions/removals shift their index. -/
theorem reindex_retained (old next : Catalog Key) (dirty : Key → Bool) (generation : Key → Nat)
    (before : Fin old.names.length) (after : Fin next.names.length)
    (same : old.name before = next.name after) (clean : dirty (next.name after) = false) :
    canonical next (advanceKey old.names next.names dirty generation) after = canonical old generation before := by
  have oldMember : next.name after ∈ old.names := same ▸ old.name_mem before
  simp [canonical,advanceKey,oldMember,next.name_mem after,clean,same]

/-- Additions cannot reuse a latent cached payload from outside prior membership. -/
def needsBuild (old : List Key) (dirty : Key → Bool) (key : Key) : Bool := decide (key ∉ old) || dirty key

/-- A new component's actual builder is required even if the dirty flag was absent. -/
theorem fresh_build (old : List Key) (dirty : Key → Bool) (key : Key) (fresh : key ∉ old) :
    needsBuild old dirty key = true := by simp [needsBuild,fresh]

/-- Named footprint changes seed invalidation even when observed values agree. -/
def seeds (old : List Key) (oldDependencies nextDependencies : Key → List Key)
    (changed : Key → Bool) (key : Key) : Bool :=
  needsBuild old (fun name => changed name || decide (oldDependencies name ≠ nextDependencies name)) key

/-- A computed-read migration cannot be hidden by equal current outputs. -/
theorem footprint_seed (old : List Key) (oldDependencies nextDependencies : Key → List Key)
    (changed : Key → Bool) (key : Key) (different : oldDependencies key ≠ nextDependencies key) :
    seeds old oldDependencies nextDependencies changed key = true := by simp [seeds,needsBuild,different]

/-- Positive read expressions reuse existing finite least closure for SCCs. -/
def reads (targets : List (Fin n)) : PositiveEquations.Expr n :=
  targets.foldr (fun target rest => .either (.read target) rest) (.literal false)

/-- Ordered aliases have ordinary existential invalidation semantics. -/
theorem reads_eval (targets : List (Fin n)) (state : Fin n → Bool) :
    (reads targets).eval state = targets.any state := by
  induction targets with
  | nil => rfl
  | cons target rest ih =>
    change (state target || (reads rest).eval state) = (state target || rest.any state)
    rw [ih]

/-- Reader dirtiness is its own seed OR any dirty dependency, including cycles. -/
def equations (edges : Fin n → List (Fin n)) (seed : Fin n → Bool) : PositiveEquations.Equations n :=
  fun index => .either (.literal (seed index)) (reads (edges index))

/-- No warm dirty bits are retained; compute the existing finite least solution. -/
def invalidate (edges : Fin n → List (Fin n)) (seed : Fin n → Bool) : Fin n → Bool :=
  (PositiveEquations.close (equations edges seed)).value

/-- Complete propagation satisfies every node's declared Boolean dependency equation. -/
theorem invalidate_equation (edges : Fin n → List (Fin n)) (seed : Fin n → Bool) (node : Fin n) :
    (seed node || (edges node).any (invalidate edges seed)) = invalidate edges seed node := by
  have fixed := congrFun (PositiveEquations.close (equations edges seed)).fixed node
  simpa [PositiveEquations.system,PositiveEquations.step,equations,PositiveEquations.Expr.eval,reads_eval,invalidate] using fixed

/-- The selected invalidation set is least among fixed points, so cyclic groups
cannot retain unsupported warm dirty bits after dependencies are removed. -/
theorem invalidate_least (edges : Fin n → List (Fin n)) (seed : Fin n → Bool) (other : Fin n → Bool)
    (fixed : ∀ node, (seed node || (edges node).any other) = other node) :
    PositiveEquations.Below (invalidate edges seed) other := by
  apply (PositiveEquations.close (equations edges seed)).least other
  funext node
  simpa [PositiveEquations.system,PositiveEquations.step,equations,PositiveEquations.Expr.eval,reads_eval] using fixed node

/-- Boolean propagation terminates within the existing finite catalog height. -/
theorem invalidate_bound (edges : Fin n → List (Fin n)) (seed : Fin n → Bool) :
    (PositiveEquations.close (equations edges seed)).depth ≤ n :=
  (PositiveEquations.close (equations edges seed)).bound

/-- Every fresh/body/footprint revision seed is rebuilt. -/
theorem seed_dirty (edges : Fin n → List (Fin n)) (seed : Fin n → Bool) (node : Fin n)
    (changed : seed node = true) : invalidate edges seed node = true := by
  have fixed := invalidate_equation edges seed node
  simpa [changed] using fixed.symm

/-- A shared target's dirty bit propagates to each reader, including SCC partners. -/
theorem reader_dirty (edges : Fin n → List (Fin n)) (seed : Fin n → Bool) (reader target : Fin n)
    (readsTarget : target ∈ edges reader) (changed : invalidate edges seed target = true) :
    invalidate edges seed reader = true := by
  have any : (edges reader).any (invalidate edges seed) = true := List.any_eq_true.mpr ⟨target,readsTarget,changed⟩
  have fixed := invalidate_equation edges seed reader
  simpa [any] using fixed.symm

/-- A retained consumer cannot contain a dirty computed or structural dependency. -/
theorem clean_dependency (edges : Fin n → List (Fin n)) (seed : Fin n → Bool) (reader target : Fin n)
    (readsTarget : target ∈ edges reader) (clean : invalidate edges seed reader = false) :
    invalidate edges seed target = false := by
  cases targetDirty : invalidate edges seed target with
  | false => rfl
  | true => have bad := reader_dirty edges seed reader target readsTarget targetDirty; simp [clean] at bad

/-- Translate the current finite solution back to names without relying on old rows. -/
def dirtyNames (next : Catalog Key) (edges : Fin next.names.length → List (Fin next.names.length))
    (seed : Key → Bool) (key : Key) : Bool :=
  match next.index key with | none => false | some index => invalidate edges (fun index => seed (next.name index)) index

/-- Named and lowered invalidation use exactly the same current node. -/
theorem dirtyNames_at (next : Catalog Key) (edges : Fin next.names.length → List (Fin next.names.length))
    (seed : Key → Bool) (index : Fin next.names.length) :
    dirtyNames next edges seed (next.name index) = invalidate edges (fun index => seed (next.name index)) index := by
  simp [dirtyNames,next.index_self index]

/-- Lower the new directory, retain only clean supported values, then reuse the
existing complete closure and final admission. Old total cache fallbacks are not
observable for removed keys and cannot stand in for newly supported validators. -/
def reclose (old : List Key) (next : Catalog Key) (dirty : Key → Bool) (generation : Key → Nat)
    (cache : Key → Payload) (dependencies : Key → List Key) (shape : Key → Except Error Unit)
    (normalize : Key → Except Error Payload)
    (admit : Graph next.names.length (Key × Nat) Payload → Fin next.names.length → Except Error Unit) :
    Except (Sum CatalogError Error) (Graph next.names.length (Key × Nat) Payload) :=
  ((lower next dependencies).mapError Sum.inl).bind fun edges =>
    (close (canonical next (advanceKey old next.names dirty generation)) edges
      (RecursiveRevision.select (fun index => needsBuild old dirty (next.name index)) (fun _ => ()) (fun index => shape (next.name index)))
      (RecursiveRevision.select (fun index => needsBuild old dirty (next.name index)) (fun index => cache (next.name index))
        (fun index => normalize (next.name index))) admit).mapError Sum.inr

/-- Accepted support migration still checks every current final obligation. -/
theorem admitted (old : List Key) (next : Catalog Key) (dirty : Key → Bool) (generation : Key → Nat)
    (cache : Key → Payload) (dependencies : Key → List Key) (shape : Key → Except Error Unit)
    (normalize : Key → Except Error Payload)
    (admit : Graph next.names.length (Key × Nat) Payload → Fin next.names.length → Except Error Unit)
    (candidate : Graph next.names.length (Key × Nat) Payload)
    (good : reclose old next dirty generation cache dependencies shape normalize admit = .ok candidate) :
    ∀ index, admit candidate index = .ok () := by
  cases lowered : lower next dependencies with
  | error cause => simp [reclose,lowered,Except.mapError,Except.bind] at good
  | ok edges =>
    cases closed : close (canonical next (advanceKey old next.names dirty generation)) edges
      (RecursiveRevision.select (fun index => needsBuild old dirty (next.name index)) (fun _ => ()) (fun index => shape (next.name index)))
      (RecursiveRevision.select (fun index => needsBuild old dirty (next.name index)) (fun index => cache (next.name index))
        (fun index => normalize (next.name index))) admit with
    | error cause => simp [reclose,lowered,closed,Except.mapError,Except.bind] at good
    | ok result =>
      have same : result = candidate := by simpa [reclose,lowered,closed,Except.mapError,Except.bind] using good
      subst candidate
      exact (RecursiveValidation.requirements _ _ _ _ _ result closed).2.2.1

/-- Existing exact evidence binding composes with all-node current admission over
this round's actual named/indexed graph. Refinement remains the supplied current
admission/policy obligation, not a certificate inferred from cached outputs. -/
theorem bound_root [DecidableEq Descriptor] [DecidableEq Context]
    (old : List Key) (next : Catalog Key) (dirty : Key → Bool) (generation : Key → Nat)
    (cache : Key → Payload) (dependencies : Key → List Key) (shape : Key → Except Error Unit)
    (normalize : Key → Except Error Payload)
    (admit : Graph next.names.length (Key × Nat) Payload → Fin next.names.length → Except Error Unit)
    (candidate : Graph next.names.length (Key × Nat) Payload)
    (good : reclose old next dirty generation cache dependencies shape normalize admit = .ok candidate)
    (root : Fin next.names.length) (template : DeclarativeMetadata.Contract Atom (Key × Nat) Result)
    (descriptor : Descriptor) (context : Context) (view : Result → (Key × Nat) × Descriptor × Context)
    (execute : (Key × Nat) → Except Cause (Result × State))
    (receipt : DeclarativeMetadata.Invocation
      (template.bindEvidence (candidate.canonical root) descriptor context view) execute (candidate.canonical root)) :
    (∀ index, admit candidate index = .ok ()) ∧
    view receipt.result = (candidate.canonical root,descriptor,context) := by
  have bound := template.bindEvidence_accepted (candidate.canonical root) descriptor context view
    execute (candidate.canonical root) receipt
  exact ⟨admitted old next dirty generation cache dependencies shape normalize admit candidate good,bound.2.2⟩

end LeanPoo.Functional.RecursiveMigration
