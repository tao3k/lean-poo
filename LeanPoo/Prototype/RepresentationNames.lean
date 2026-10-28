import LeanPoo.Prototype.Representation

/-! Owned structural names and bounded authentication of exposed read spines.
String keys injectively represent symbol identities. Fresh standard list copies,
the existing registered issuer and serialized supported edits are premises.
No allocator, collector, arbitrary raw setters or compiler verification is claimed.
-/
namespace LeanPoo.Prototype.Representation

/-- A presented name spine may end, point at a pair, or contain a foreign tail. -/
inductive NameLink where
  | nil
  | cell (id : Nat)
  | invalid
  deriving DecidableEq

/-- Mutable presented pairs may form cycles; the private saved sequence is finite. -/
structure NameCell where
  name : String
  next : NameLink

/-- Authentication recurses on private names, never on untrusted heap topology. -/
def matchesNameSpine (heap : Nat → NameCell) (link : NameLink) : List String → Bool
  | [] => link == .nil
  | name :: tail => match link with
    | .cell id => (heap id).name == name && matchesNameSpine heap (heap id).next tail
    | _ => false

/-- Count inspected links, including the final proper-list termination check. -/
def nameSpineWork (heap : Nat → NameCell) (link : NameLink) : List String → Nat
  | [] => 1
  | name :: tail => match link with
    | .cell id => if (heap id).name == name then 1 + nameSpineWork heap (heap id).next tail else 1
    | _ => 1

/-- Even a cyclic or improper presentation cannot exceed the finite saved bound. -/
theorem nameSpineWork_bound (heap : Nat → NameCell) (link : NameLink) (saved : List String) :
    nameSpineWork heap link saved ≤ saved.length + 1 := by
  induction saved generalizing link with
  | nil => simp [nameSpineWork]
  | cons name tail ih =>
    cases link with
    | nil => simp [nameSpineWork]
    | invalid => simp [nameSpineWork]
    | cell id =>
      simp only [nameSpineWork]
      split
      · have bound := ih (heap id).next
        simp only [List.length_cons]; omega
      · simp

/-- An unexpected extra cell or improper tail cannot authenticate an empty suffix. -/
theorem matchesNameSpine_end (heap : Nat → NameCell) (link : NameLink) :
    matchesNameSpine heap link [] = true ↔ link = .nil := by simp [matchesNameSpine]

/-- Replacing an identity by another symbol, even with equal printed spelling, refuses. -/
theorem matchesNameSpine_wrong_head (heap : Nat → NameCell) (id : Nat) (name : String)
    (tail : List String) (different : (heap id).name ≠ name) :
    matchesNameSpine heap (.cell id) (name :: tail) = false := by
  simp [matchesNameSpine, different]

/-- Existing issuance authenticates primitive metadata; names add a finite spine. -/
structure NamesEvidence where
  registered : Bool
  revision : Nat
  identity : Nat
  saved : List String
  presented : NameLink

/-- Private canonical names and value layout have separate ownership/lifetimes. -/
structure NamesAuthority (Value : Type) where
  names : List String
  revision : Nat
  live : Nat
  preparation : List Nat
  view : View Value

/-- The saved names belong to issuance, so a later source edit does not forge a birth. -/
def namesIssued (heap : Nat → NameCell) (read : NamesEvidence) : Bool :=
  read.registered && matchesNameSpine heap read.presented read.saved

/-- Currentness additionally checks the receiver generation and retained record identity. -/
def namesCurrent (authority : NamesAuthority Value) (read : NamesEvidence) : Bool :=
  read.revision == authority.revision && read.identity == authority.live

/-- Trusted issuance captures canonical names before exposing a separate spine.
The caller supplies a fresh presentation with equal contents, not private cells. -/
def issueNames (authority : NamesAuthority Value) (presented : NameLink) : NamesEvidence :=
  ⟨true, authority.revision, authority.live, authority.names, presented⟩

/-- A faithfully copied presentation receives the current generation and exact names. -/
theorem issueNames_ready (heap : Nat → NameCell) (authority : NamesAuthority Value)
    (presented : NameLink) (copied : matchesNameSpine heap presented authority.names = true) :
    namesIssued heap (issueNames authority presented) = true ∧
    namesCurrent authority (issueNames authority presented) = true := by
  simp [issueNames, namesIssued, namesCurrent, copied]

/-- A real source revision invalidates old names even when the field set agrees. -/
theorem namesCurrent_revision (authority : NamesAuthority Value) (read : NamesEvidence)
    (changed : read.revision ≠ authority.revision) : namesCurrent authority read = false := by
  simp [namesCurrent, changed]

/-- Preserve unissued-before-stale error order and original consumer failures. -/
def useNamesEvidence (heap : Nat → NameCell) (authority : NamesAuthority Value)
    (read : NamesEvidence) (consume : List String → Except String Result) : Except String Result :=
  if namesIssued heap read then
    if namesCurrent authority read then consume authority.names else .error "stale slot dependency"
  else .error "unissued slot dependency"

/-- Corrupt names cannot enter a consumer or be confused with a business refusal. -/
theorem useNamesEvidence_unissued (heap : Nat → NameCell) (authority : NamesAuthority Value)
    (read : NamesEvidence) (consume : List String → Except String Result)
    (bad : namesIssued heap read = false) :
    useNamesEvidence heap authority read consume = .error "unissued slot dependency" := by
  simp [useNamesEvidence, bad]

/-- A legitimate old-generation record remains issued but fails before consumer work. -/
theorem useNamesEvidence_stale (heap : Nat → NameCell) (authority : NamesAuthority Value)
    (read : NamesEvidence) (consume : List String → Except String Result)
    (issued : namesIssued heap read = true) (stale : namesCurrent authority read = false) :
    useNamesEvidence heap authority read consume = .error "stale slot dependency" := by
  simp [useNamesEvidence, issued, stale]

/-- Admitted observation preserves the exact result, including a refusal or false/Function. -/
theorem useNamesEvidence_ready (heap : Nat → NameCell) (authority : NamesAuthority Value)
    (read : NamesEvidence) (consume : List String → Except String Result)
    (issued : namesIssued heap read = true) (current : namesCurrent authority read = true) :
    useNamesEvidence heap authority read consume = consume authority.names := by
  simp [useNamesEvidence, issued, current]

/-- Targeted metadata repair changes only the names-record identity. -/
def refreshNames (authority : NamesAuthority Value) (fresh : Nat) : NamesAuthority Value :=
  { authority with live := fresh }

/-- Repair retains canonical membership, preparation parents and current value cells. -/
theorem refreshNames_frame (authority : NamesAuthority Value) (fresh : Nat) :
    (refreshNames authority fresh).names = authority.names ∧
    (refreshNames authority fresh).preparation = authority.preparation ∧
    (refreshNames authority fresh).view = authority.view := ⟨rfl, rfl, rfl⟩

/-- Repair does not discard a warmed static access site's current receiver/layout. -/
theorem refreshNames_read (authority : NamesAuthority Value) (fresh : Nat) (site : Site) :
    read site (refreshNames authority fresh).view = read site authority.view := rfl

/-- A replaced record cannot become current merely because source values agree. -/
theorem refreshNames_old (authority : NamesAuthority Value) (fresh : Nat) (old : NamesEvidence)
    (was : old.identity = authority.live) (different : fresh ≠ authority.live) :
    namesCurrent (refreshNames authority fresh) old = false := by
  simp [namesCurrent, refreshNames, was, Ne.symm different]

/-- Use the standard finite list map; the exported list does not own authority. -/
def exposeNames (authority : NamesAuthority Value) : NamesAuthority Value × List String :=
  (authority, authority.names.map id)

/-- Export preserves order/multiplicity with one logical cell per name. -/
theorem exposeNames_value (authority : NamesAuthority Value) :
    (exposeNames authority).2 = authority.names := by
  simp [exposeNames]

/-- Arbitrary replacement of the caller's owned view cannot alter private state. -/
def replaceExposedNames (exported : NamesAuthority Value × List String) (later : List String) :=
  (exported.1, later)

/-- Public mutation leaves both authoritative names and existing value reads unchanged. -/
theorem replaceExposedNames_frame (authority : NamesAuthority Value) (later : List String) (site : Site) :
    (replaceExposedNames (exposeNames authority) later).1.names = authority.names ∧
    read site (replaceExposedNames (exposeNames authority) later).1.view = read site authority.view :=
  ⟨rfl, rfl⟩

/-- Name-copy cells only; record closures, canonical construction, result pairs and GC are extra. -/
def namesCopyCells (fields publicQueries newRecords : Nat) := fields * (publicQueries + newRecords)

/-- Warm private enumeration adds no public snapshot; cold issuance still pays its own copy. -/
theorem namesCopyCells_borrowed (fields newRecords : Nat) :
    namesCopyCells fields 0 newRecords = fields * newRecords := by simp [namesCopyCells]

/-- Select the existing root projection. Reuse the finite spine vocabulary with
String encoding opaque read identities here, not slot labels. A warm exact match
reauthenticates; only a miss enters the host finite-list admission and builder. -/
def obtainRootProjection (heap : Nat → NameCell) (presented : NameLink)
    (cached : Option (List String × Value))
    (admit : Unit → Except String (List String))
    (build : List String → Except String Value)
    (authenticate : Value → Except String Value) : Except String Value :=
  match cached with
  | some (saved, value) =>
      if matchesNameSpine heap presented saved then authenticate value
      else admit () >>= build
  | none => admit () >>= build

/-- An exact finite warm match bypasses a repeated grammar scan, never issuance. -/
theorem obtainRootProjection_hit (heap : Nat → NameCell) (presented : NameLink)
    (saved : List String) (value : Value) (admit : Unit → Except String (List String))
    (build : List String → Except String Value) (authenticate : Value → Except String Value)
    (same : matchesNameSpine heap presented saved = true) :
    obtainRootProjection heap presented (some (saved, value)) admit build authenticate =
      authenticate value := by simp [obtainRootProjection, same]

/-- Failed authentication is not replaced by an earlier successful cache verdict. -/
theorem obtainRootProjection_hit_refused (heap : Nat → NameCell) (presented : NameLink)
    (saved : List String) (value : Value) (admit : Unit → Except String (List String))
    (build : List String → Except String Value) (authenticate : Value → Except String Value)
    (same : matchesNameSpine heap presented saved = true) (cause : String)
    (refused : authenticate value = .error cause) :
    obtainRootProjection heap presented (some (saved, value)) admit build authenticate =
      .error cause := by simp [obtainRootProjection, same, refused]

/-- Cold invalid grammar never reaches entry authentication or graph construction. -/
theorem obtainRootProjection_cold_refused (heap : Nat → NameCell) (presented : NameLink)
    (admit : Unit → Except String (List String)) (build : List String → Except String Value)
    (authenticate : Value → Except String Value) (cause : String)
    (refused : admit () = .error cause) :
    obtainRootProjection heap presented none admit build authenticate = .error cause := by
  simp only [obtainRootProjection, refused]; rfl

/-- Changed, improper or cyclic roots cannot use an old signature to skip admission. -/
theorem obtainRootProjection_changed_refused (heap : Nat → NameCell) (presented : NameLink)
    (saved : List String) (value : Value) (admit : Unit → Except String (List String))
    (build : List String → Except String Value) (authenticate : Value → Except String Value)
    (different : matchesNameSpine heap presented saved = false) (cause : String)
    (refused : admit () = .error cause) :
    obtainRootProjection heap presented (some (saved, value)) admit build authenticate =
      .error cause := by simp only [obtainRootProjection, different, Bool.false_eq_true, ↓reduceIte, refused]; rfl

/-- The saved private length bounds warm comparison even on a cyclic heap. Host
proper-list recognition on a cold miss is a separate standard-library premise. -/
theorem rootProjection_compare_bound (heap : Nat → NameCell) (presented : NameLink)
    (saved : List String) : nameSpineWork heap presented saved ≤ saved.length + 1 :=
  nameSpineWork_bound heap presented saved

/-- Correct finite input can rebuild and propagate the exact builder result. -/
theorem obtainRootProjection_retry (heap : Nat → NameCell) (presented : NameLink)
    (names : List String) (build : List String → Except String Value)
    (authenticate : Value → Except String Value) :
    obtainRootProjection heap presented none (fun _ => .ok names) build authenticate =
      build names := rfl

/-- Refusal frames the complete post-argument source/cache state. This does not
undo caller mutations to the exposed root spine or effects of host arguments. -/
theorem obtainRootProjection_refused_frame (heap : Nat → NameCell) (presented : NameLink)
    (cached : Option (List String × State)) (old : State)
    (admit : Unit → Except String (List String)) (build : List String → Except String State)
    (authenticate : State → Except String State) (cause : String)
    (refused : obtainRootProjection heap presented cached admit build authenticate = .error cause) :
    Object.publishEdit old (obtainRootProjection heap presented cached admit build authenticate) =
      old := by rw [refused]; rfl

/-- Public direct-parent reflection owns the exported spine. Parent identities
are shared, not recursively copied; State includes the private graph and caches.
The host standard list-copy's physical isolation remains an explicit premise. -/
def exposeParents (parents : List Parent) (state : State) : State × List Parent :=
  (state, parents.map id)

/-- Snapshot order, repetitions and actual parent identities are unchanged. -/
theorem exposeParents_value (parents : List Parent) (state : State) :
    (exposeParents parents state).2 = parents := by simp [exposeParents]

/-- Arbitrary edits/replacement of an owned public view leave ALL authoritative
state unchanged, including revisions, layouts, cached values and source edges. -/
theorem exposeParents_frame (parents later : List Parent) (state : State) :
    (Prod.map id (fun _ => later) (exposeParents parents state)).1 = state := rfl

/-- The shared checked parent setter accepts only admitted finite topology.
Admission includes existing C3/cycle validation; old is the post-admission state,
so this is not rollback of validation/getter effects or arbitrary callbacks. -/
def checkedParentEdit (admitted : Except String (List Parent)) (sealed active : Bool)
    (old : State) (install : List Parent → State → State) : Except String State := do
  let parents ← admitted
  Object.guardedEdit sealed active old (install parents)

/-- A refused topology cannot install parents or clear the supplied source/cache state. -/
theorem checkedParentEdit_refused_frame (cause : String) (sealed active : Bool)
    (old : State) (install : List Parent → State → State) :
    Object.publishEdit old (checkedParentEdit (.error cause) sealed active old install) = old := rfl

/-- Stable admitted input keeps the original sealed-source refusal priority. -/
theorem checkedParentEdit_sealed (parents : List Parent) (active : Bool)
    (old : State) (install : List Parent → State → State) :
    checkedParentEdit (.ok parents) true active old install = .error "sealed prototype" := rfl

/-- Active affected receivers still refuse mutation before installing new topology. -/
theorem checkedParentEdit_active (parents : List Parent) (old : State)
    (install : List Parent → State → State) :
    checkedParentEdit (.ok parents) false true old install =
      .error "object mutation during computation" := rfl

/-- Corrected topology retries through the same supported installation operation. -/
theorem checkedParentEdit_retry (parents : List Parent) (old : State)
    (install : List Parent → State → State) :
    checkedParentEdit (.ok parents) false false old install = .ok (install parents old) := rfl

/-- Existing reverse invalidation rejects a prior value guard after parent edits,
even when a replacement restores equal values, shapes or parent identities. -/
theorem parentReplacement_rejectsGuard (graph : C4.Graph) (changed : List String)
    (cache : String → Object.RevisionCache Value) (name : String) (site : Site) (view : View Value)
    (affected : name ∈ Proof.invalidatedNodes graph changed)
    (oldRevision : site.revision = (cache name).revision)
    (newRevision : view.revision = (Object.invalidateCaches graph changed cache name).revision) :
    read site view = none := by
  apply reject_revision
  rw [oldRevision, newRevision]
  exact descendant_revision_rejected graph changed cache name affected

/-- Output list cells only: explicit public snapshots plus constructor flattening.
C3 traversal, metadata capture, callbacks, weak storage and GC are additional costs. -/
def parentSpineCells (parents queries constructions : Nat) : Nat := parents * (queries + constructions)

/-- Borrowing private parents internally removes only a redundant public snapshot;
constructors still pay for their own finite parent-list capture. -/
theorem parentSpineCells_internal (parents constructions : Nat) :
    parentSpineCells parents 0 constructions = parents * constructions := by simp [parentSpineCells]

end LeanPoo.Prototype.Representation
