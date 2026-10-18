import LeanPoo.Object.MethodCombinationSemantics
import LeanPoo.Functional.DeclarativeMetadata
import LeanPoo.Functional.PrototypeTypes
import LeanPoo.Functional.Parameters

/-! Record and qualified method declarations share one fragment stream. This
models source-order collection, inherited assembly and receiver-generic invocation;
Gerbil syntax expansion, policy admission and mutable invalidation have controls. -/
namespace LeanPoo.Object.MethodCombination
variable {Self : Type}
/-- One extensible declaration stream can contribute data and qualified methods. -/
inductive Fragment (Data Receiver : Type) (M : Type → Type) (Result : Type) where
  | slot (name : String) (value : Data)
  | method (name : String) (parts : List (Contribution Receiver M Result))
/-- Resolve only one method name, retaining every contribution in source order. -/
def collectFragments (key : String) : List (Fragment Data Receiver M Result) → List (Contribution Receiver M Result)
  | [] => []
  | .slot _ _ :: rest => collectFragments key rest
  | .method name parts :: rest =>
      if name = key then parts ++ collectFragments key rest else collectFragments key rest
/-- Splitting a declaration source cannot reorder, lose or duplicate its methods. -/
theorem collectFragments_append (key : String) (first second : List (Fragment Data Receiver M Result)) :
    collectFragments key (first ++ second) = collectFragments key first ++ collectFragments key second := by
  induction first with
  | nil => rfl
  | cons head rest ih =>
    cases head with
    | slot => exact ih
    | method name parts =>
      by_cases same : name = key <;> simp [collectFragments, same, ih, List.append_assoc]
/-- Coalescing equal-name fragments preserves every generic's contribution stream,
not just the method that is being normalized. Bodies remain uninterpreted values. -/
theorem collectFragments_coalesce (key name : String) (left right : List (Contribution Receiver M Result))
    (rest : List (Fragment Data Receiver M Result)) :
    collectFragments key (.method name left :: .method name right :: rest) =
      collectFragments key (.method name (left ++ right) :: rest) := by
  by_cases same : name = key <;> simp [collectFragments, same, List.append_assoc]
/-- Local method declarations use the existing delayed inherited SlotSpec. -/
def fragmentSpecification (key : String) (fragments : List (Fragment Data Receiver M Result)) :
    Prototype.SlotSpec Self (Option (Methods Receiver M Result)) := specifications (collectFragments key fragments)
/-- Assembling a child fragment block ahead of an inherited block preserves each
qualifier's order. No contribution body runs during this assembly. -/
theorem fragmentSpecification_append (key : String) (first second : List (Fragment Data Receiver M Result))
    (self : Self) (inherited : Prototype.Next (Option (Methods Receiver M Result))) :
    (fragmentSpecification key (first ++ second)).eval self inherited =
      (fragmentSpecification key first).eval self
        (fun _ => (fragmentSpecification key second).eval self inherited) := by
  simp [fragmentSpecification, specifications, Prototype.SlotSpec.eval, collectFragments_append, List.foldr_append]
/-- Record fragments never become method contributions, even if names coincide.
Declaration publication separately rejects such collisions rather than silently hiding data. -/
theorem collectFragments_slot (key name : String) (value : Data) (rest : List (Fragment Data Receiver M Result)) :
    collectFragments key (.slot name value :: rest) = collectFragments key rest := rfl
/-- A type-selected generic resolves metadata from the class while invoking with
the ORIGINAL complete receiver/argument row. It does not invoke with the class. -/
def declaredGeneric [Monad M] (typeOf : Receiver → Class)
    (lookup : Class → Option (Methods Receiver M Result)) (fallback : Methods Receiver M Result)
    (onMissing : Receiver → M Result) (receiver : Receiver) : M Result :=
  effective ((lookup (typeOf receiver)).getD fallback) onMissing receiver
/-- The generic bridge preserves the established standard qualifier semantics. -/
theorem declaredGeneric_standard [Monad M] (typeOf : Receiver → Class)
    (lookup : Class → Option (Methods Receiver M Result)) (fallback : Methods Receiver M Result)
    (onMissing : Receiver → M Result) (receiver : Receiver) :
    declaredGeneric typeOf lookup fallback onMissing receiver =
      standard ((lookup (typeOf receiver)).getD fallback) onMissing receiver := by
  unfold declaredGeneric
  rw [effective_standard]
/-- Supplied fragment blocks compose all the way through generic invocation. -/
theorem declaredGeneric_fragments [Monad M] (key : String)
    (first second : List (Fragment Data Receiver M Result)) (self : Self)
    (inherited : Prototype.Next (Option (Methods Receiver M Result)))
    (onMissing : Receiver → M Result) (receiver : Receiver) :
    effective (((fragmentSpecification key (first ++ second)).eval self inherited).getD {}) onMissing receiver =
      effective (((fragmentSpecification key first).eval self
        (fun _ => (fragmentSpecification key second).eval self inherited)).getD {}) onMissing receiver := by
  rw [fragmentSpecification_append]
/-- Admission evidence contains immutable qualifier data and both revisions. It
contains neither a receiver nor a callback, matching the weak-table payload. -/
structure ContributionStamp where
  revision : Nat
  typeRevision : Nat
  qualifier : Nat
  deriving DecidableEq, Repr

/-- A finite qualifier policy reuses evidence only at both current revisions.
A miss executes the current checker; its result is never inserted here. -/
def admitRegistered (stamp : Option ContributionStamp) (revision typeRevision : Nat)
    (policy : Nat → Bool) (check : Unit → Bool) : Bool :=
  match stamp with
  | none => check ()
  | some evidence =>
    if evidence.revision = revision ∧ evidence.typeRevision = typeRevision
    then policy evidence.qualifier else check ()

/-- Soundness requires constructor admission and revision discipline: a matching
stamp's qualifier agrees with the current descriptor/Type protocol. This does not
assert that arbitrary effectful Type predicates can be cached. -/
theorem admitRegistered_eq (stamp : Option ContributionStamp) (revision typeRevision : Nat)
    (policy : Nat → Bool) (check : Unit → Bool)
    (stable : ∀ evidence, stamp = some evidence →
      evidence.revision = revision → evidence.typeRevision = typeRevision →
      policy evidence.qualifier = check ()) :
    admitRegistered stamp revision typeRevision policy check = check () := by
  cases stamp with
  | none => rfl
  | some evidence =>
    simp only [admitRegistered]
    split
    · rename_i current
      exact stable evidence rfl current.1 current.2
    · rfl

/-- Admission substitution preserves an arbitrary subsequent effectful program,
including its refusal and multiple-result carrier. No callback is stored in a stamp. -/
theorem admitRegistered_execution {M : Type → Type} {Result : Type} (stamp : Option ContributionStamp) (revision typeRevision : Nat)
    (policy : Nat → Bool) (check : Unit → Bool) (invoke refuse : M Result)
    (stable : ∀ evidence, stamp = some evidence →
      evidence.revision = revision → evidence.typeRevision = typeRevision →
      policy evidence.qualifier = check ()) :
    (if admitRegistered stamp revision typeRevision policy check then invoke else refuse) =
      (if check () then invoke else refuse) := by
  rw [admitRegistered_eq stamp revision typeRevision policy check stable]

/-- Changing either receiver or Type revision forces current validation, even
if a later edit restores an earlier qualifier or function body. -/
theorem admitRegistered_stale (evidence : ContributionStamp) (revision typeRevision : Nat)
    (policy : Nat → Bool) (check : Unit → Bool)
    (changed : evidence.revision ≠ revision ∨ evidence.typeRevision ≠ typeRevision) :
    admitRegistered (some evidence) revision typeRevision policy check = check () := by
  simp only [admitRegistered]
  split
  · rename_i current
    rcases changed with h | h
    · exact False.elim (h current.1)
    · exact False.elim (h current.2)
  · rfl

/-- List admission preserves source order and every current-check result under
per-element stability. Grouping and callback execution remain separate. -/
theorem registered_admissions_eq (parts : List α) (cached current : α → Bool)
    (sound : ∀ part ∈ parts, cached part = current part) :
    parts.map cached = parts.map current := by
  apply List.map_congr_left
  exact sound

/-- Full request accounting includes registration, guard/check work and supplied
collector history. Prices are external inputs, not claims about machine time. -/
def contributionCharge (setup calls guard check gc : Nat) : Nat :=
  setup + calls * (guard + check) + gc

/-- Reuse amortizes only when saved validation covers setup, guards and additional
GC. The theorem deliberately permits a negative cold or complete-workflow result. -/
theorem contributionCharge_threshold (setup calls guard check cachedGC checkedGC : Nat) :
    contributionCharge setup calls guard 0 cachedGC ≤ contributionCharge 0 calls 0 check checkedGC ↔
    setup + calls * guard + cachedGC ≤ calls * check + checkedGC := by
  simp [contributionCharge]

end LeanPoo.Object.MethodCombination

/-! Certified typed declarations reuse the existing edit and negative-watch
semantics. Args is the admitted argument carrier; Gerbil core formal binding,
runtime Type normalization and metadata identity are checked by Scheme tests. -/
namespace LeanPoo.Functional.DeclarativeMetadata
open Object DispatchExtension
variable {Args Method Result : Type}
variable {seed : Multimethod Args Method Result} {watches : List (Watch Args)}
variable {edits : List (Edit Args Method)}

/-- Local and inherited fragments compile once into the existing transaction.
The caller supplies one common certified signature; mismatched signatures never
reach this typed operation. Ancestor edits precede local edits; each batch retains existing edit semantics. -/
def assembleDeclared (seed : Multimethod Args Method Result) (watches : List (Watch Args))
    (certified : Certificate seed watches) (front inherited : List (Declaration Args Method)) :=
  guard seed watches certified ((inherited ++ front).map Declaration.compile)

/-- Acceptance requires both complete registration and every negative assumption
on that exact completed candidate, rather than separate approvals of fragments. -/
theorem assembleDeclared_ok_iff (seed : Multimethod Args Method Result) (watches : List (Watch Args))
    (certified : Certificate seed watches) (front inherited : List (Declaration Args Method)) :
    (∃ revision, assembleDeclared seed watches certified front inherited = .ok revision) ↔
      ∃ candidate, install seed (inherited ++ front) = .ok candidate ∧ AllAbsent candidate watches :=
  guard_ok_iff seed watches certified _

/-- Coalescing local blocks preserves the installed candidate and registration
errors, while keeping ancestor edits ahead of both local blocks. -/
theorem assembleDeclared_coalesce (seed : Multimethod Args Method Result)
    (first second inherited : List (Declaration Args Method)) :
    install seed (inherited ++ (first ++ second)) = install seed ((inherited ++ first) ++ second) := by
  rw [List.append_assoc]

/-- The compiled owner has a sound candidate cache whenever its seed does. -/
theorem assembleDeclared_cacheSound (seed : Multimethod Args Method Result) (watches : List (Watch Args))
    (sound : seed.CacheSound) (revision : Revision seed watches edits) :
    revision.snapshot.CacheSound := revision.cacheSound sound

/-- Invocation uses the actual compiled snapshot and returns its complete cache
successor with the transported absence proof. No declaration is reinstalled here. -/
def invokeDeclared (revision : Revision seed watches edits) (args : Args) :=
  revision.certificate.invoke args

/-- A returned successor certifies every original watch at its own snapshot. -/
theorem invokeDeclared_absent (revision : Revision seed watches edits) (args : Args)
    (invocation : DispatchExtension.Invocation revision.snapshot watches args)
    (_called : invokeDeclared revision args = .ok invocation) :
    AllAbsent invocation.snapshot watches := invocation.certificate.absent

/-- Refused declaration publication leaves the original generic/cache accessible.
This is immutable state preservation, not rollback of arbitrary external effects. -/
theorem declaredPublication_refused (seed : Multimethod Args Method Result) (watches : List (Watch Args))
    (certified : Certificate seed watches) (front inherited : List (Declaration Args Method))
    (failure : DispatchExtension.Failure seed watches ((inherited ++ front).map Declaration.compile))
    (refused : assembleDeclared seed watches certified front inherited = .error failure) :
    publish seed watches certified ((inherited ++ front).map Declaration.compile) = (.error failure, seed) :=
  publish_refused seed watches certified _ failure refused

/-- Only a unique COMPLETE bounded search can call the supplied declaration
builder. Search and builder failures remain distinct, with no partial artifact. -/
def inferDeclared (budget : Nat) (valid : Assignment → Bool) (candidates : List Assignment)
    (build : Assignment → Except Error Artifact) :
    Except (Sum PrototypeTypes.Failure Error) (PrototypeTypes.Inference Assignment × Option Artifact) :=
  match PrototypeTypes.inferBounded budget valid candidates with
  | .error cause => .error (.inl cause)
  | .ok (.unique assignment) =>
    match build assignment with
    | .error cause => .error (.inr cause)
    | .ok artifact => .ok (.unique assignment, some artifact)
  | .ok report => .ok (report, none)

/-- Exhaustion never calls the declaration builder or exposes an accepted prefix. -/
theorem inferDeclared_exhausted (budget : Nat) (valid : Assignment → Bool) (candidates : List Assignment)
    (build : Assignment → Except Error Artifact) (incomplete : budget < candidates.length) :
    inferDeclared budget valid candidates build = .error (.inl .exhausted) := by
  simp [inferDeclared, PrototypeTypes.incomplete_refuses budget valid candidates incomplete]

/-- Ambiguity is preserved as data without mapping an effectful builder over candidates. -/
theorem inferDeclared_ambiguous (budget : Nat) (valid : Assignment → Bool) (candidates : List Assignment)
    (build : Assignment → Except Error Artifact)
    (completed : PrototypeTypes.inferBounded budget valid candidates = .ok (.ambiguous assignments)) :
    inferDeclared budget valid candidates build = .ok (.ambiguous assignments, none) := by
  simp [inferDeclared, completed]

/-- Complete no-solution classification also constructs no declaration artifact. -/
theorem inferDeclared_none (budget : Nat) (valid : Assignment → Bool) (candidates : List Assignment)
    (build : Assignment → Except Error Artifact)
    (completed : PrototypeTypes.inferBounded budget valid candidates = .ok .none) :
    inferDeclared budget valid candidates build = .ok (.none, none) := by
  simp [inferDeclared, completed]

/-- A builder refusal retains its actual cause rather than becoming no-solution. -/
theorem inferDeclared_build_error (budget : Nat) (valid : Assignment → Bool) (candidates : List Assignment)
    (build : Assignment → Except Error Artifact)
    (completed : PrototypeTypes.inferBounded budget valid candidates = .ok (.unique assignment))
    (failed : build assignment = .error cause) :
    inferDeclared budget valid candidates build = .error (.inr cause) := by
  simp [inferDeclared, completed, failed]

/-- Returned artifacts have both an actual uniquely admitted assignment and a
successful builder run. Combining this with assembleDeclared_ok_iff gives the
completed-candidate negative assumptions; no new dispatch semantics is assumed. -/
theorem inferDeclared_unique (budget : Nat) (valid : Assignment → Bool) (candidates : List Assignment)
    (build : Assignment → Except Error Artifact)
    (accepted : inferDeclared budget valid candidates build = .ok (.unique assignment, some artifact)) :
    assignment ∈ candidates ∧ valid assignment = true ∧ build assignment = .ok artifact := by
  unfold inferDeclared at accepted
  cases completed : PrototypeTypes.inferBounded budget valid candidates with
  | error cause => simp [completed] at accepted
  | ok report =>
    cases report with
    | none => simp [completed] at accepted
    | ambiguous assignments => simp [completed] at accepted
    | unique selected =>
      cases built : build selected with
      | error cause => simp [completed, built] at accepted
      | ok result =>
        have same : selected = assignment ∧ result = artifact := by simpa [completed, built] using accepted
        rcases same with ⟨rfl, rfl⟩
        exact ⟨(PrototypeTypes.bounded_unique _ _ _ completed).1,
          (PrototypeTypes.bounded_unique _ _ _ completed).2, built⟩

/-- Positional binding uses the existing validated-name protocol before the
builder. Receiver fields and remaining names follow checkedSpecialize exactly. -/
def specializeDeclared [DecidableEq Name] (reserved : Name) (source : Parameters.Template Name Value)
    (values : List Value) (build : Parameters.Template Name Value → Except Error Artifact) :
    Except (Sum Parameters.Failure Error) Artifact :=
  match Parameters.checkedSpecialize reserved source values with
  | .error cause => .error (.inl cause)
  | .ok bound => (build bound).mapError Sum.inr

/-- Malformed parameter metadata refuses even for an empty prefix, before build. -/
theorem specializeDeclared_invalid [DecidableEq Name] (reserved : Name)
    (source : Parameters.Template Name Value) (values : List Value)
    (build : Parameters.Template Name Value → Except Error Artifact)
    (invalid : Parameters.validNames reserved source.remaining = false) :
    specializeDeclared reserved source values build = .error (.inl .declaration) := by
  simp [specializeDeclared, Parameters.checkedSpecialize, invalid]

/-- Reusing checked positional binding keeps the exact remaining-name frame. -/
theorem specializeDeclared_remaining [DecidableEq Name] (reserved : Name)
    (source bound : Parameters.Template Name Value) (values : List Value)
    (accepted : Parameters.checkedSpecialize reserved source values = .ok bound) :
    bound.remaining = source.remaining.drop values.length := by
  unfold Parameters.checkedSpecialize at accepted
  split at accepted
  · unfold Parameters.specialize at accepted
    split at accepted
    · cases accepted; rfl
    · contradiction
  · contradiction

/-- Final source admission is separate from successful inference/installation.
A revised descriptor cannot borrow an earlier bound-parameter snapshot. -/
def admitDeclaredBindings [DecidableEq Descriptor] (bindings : List (Parameters.BoundParameter Name Descriptor))
    (fields : Name → Option Descriptor) (revision : Descriptor → Nat) (artifact : Artifact) :
    Except PrototypeTypes.Failure Artifact :=
  if Parameters.bindingsCurrent bindings fields revision then .ok artifact else .error .bounds

/-- A returned artifact still has every bound descriptor identity and direct revision. -/
theorem admitDeclaredBindings_stable [DecidableEq Descriptor]
    (bindings : List (Parameters.BoundParameter Name Descriptor))
    (fields : Name → Option Descriptor) (revision : Descriptor → Nat) (artifact result : Artifact)
    (accepted : admitDeclaredBindings bindings fields revision artifact = .ok result)
    (binding : Parameters.BoundParameter Name Descriptor) (member : binding ∈ bindings) :
    fields binding.name = some binding.descriptor ∧ revision binding.descriptor = binding.revision := by
  unfold admitDeclaredBindings at accepted
  split at accepted
  · rename_i current
    exact Parameters.bindingsCurrent_sound bindings fields revision current binding member
  · contradiction


/-- A collected finite call batch enters the SAME inference/declaration driver.
Collection failures keep their phase/cause; all siblings share one assignment and
one complete builder result, never one independently inferred value per method. -/
def inferDeclaredCalls (fuel budget : Nat) (bounds : List (PrototypeTypes.Expr × PrototypeTypes.Expr))
    (collected : Except PrototypeTypes.Failure (List (PrototypeTypes.Expr × PrototypeTypes.Expr)))
    (candidates : List (Nat → PrototypeTypes.Ty))
    (build : (Nat → PrototypeTypes.Ty) → Except Error Artifact) :
    Except (Sum PrototypeTypes.Failure Error) (PrototypeTypes.Inference (Nat → PrototypeTypes.Ty) × Option Artifact) :=
  match collected with
  | .error cause => .error (.inl cause)
  | .ok queries => inferDeclared budget (fun env => PrototypeTypes.satisfies fuel (bounds ++ queries) env) candidates build

/-- No collection refusal can call the builder or expose a successful prefix. -/
theorem inferDeclaredCalls_refused (fuel budget bounds candidates)
    (build : (Nat → PrototypeTypes.Ty) → Except Error Artifact) (cause : PrototypeTypes.Failure) :
    inferDeclaredCalls fuel budget bounds (.error cause) candidates build = .error (.inl cause) := rfl

/-- Complete unique inference retains candidate and successful WHOLE builder provenance. -/
theorem inferDeclaredCalls_provenance (fuel budget bounds queries candidates)
    (build : (Nat → PrototypeTypes.Ty) → Except Error Artifact) (env artifact)
    (accepted : inferDeclaredCalls fuel budget bounds (.ok queries) candidates build = .ok (.unique env, some artifact)) :
    env ∈ candidates ∧ build env = .ok artifact := by
  obtain ⟨member, _, built⟩ := inferDeclared_unique _ _ _ _ accepted
  exact ⟨member, built⟩

/-- Every original bound and every call-derived input/output obligation holds
under the SAME admitted environment, including variables on either side. -/
theorem inferDeclaredCalls_constraints (fuel budget bounds queries candidates)
    (build : (Nat → PrototypeTypes.Ty) → Except Error Artifact) (env artifact)
    (accepted : inferDeclaredCalls fuel budget bounds (.ok queries) candidates build = .ok (.unique env, some artifact))
    (query : PrototypeTypes.Expr × PrototypeTypes.Expr) (member : query ∈ bounds ++ queries) :
    PrototypeTypes.Subtype (PrototypeTypes.substitute env query.1) (PrototypeTypes.substitute env query.2) := by
  obtain ⟨_, valid, _⟩ := inferDeclared_unique _ _ _ _ accepted
  exact PrototypeTypes.satisfies_sound fuel (bounds ++ queries) env valid member

/-- A shared environment cannot satisfy contradictory sibling obligations. -/
theorem inferDeclaredCalls_inconsistent (fuel budget bounds queries candidates)
    (build : (Nat → PrototypeTypes.Ty) → Except Error Artifact)
    (refused : ∀ env ∈ candidates, PrototypeTypes.satisfies fuel (bounds ++ queries) env = false) :
    inferDeclaredCalls fuel budget bounds (.ok queries) candidates build ≠ .ok (.unique selected, some artifact) := by
  intro accepted
  obtain ⟨member, valid, _⟩ := inferDeclared_unique _ _ _ _ accepted
  have invalid := refused selected member
  rw [invalid] at valid
  contradiction

/-- Even after collection succeeds, incomplete enumeration refuses all artifacts. -/
theorem inferDeclaredCalls_exhausted (fuel budget bounds queries candidates)
    (build : (Nat → PrototypeTypes.Ty) → Except Error Artifact) (incomplete : budget < candidates.length) :
    inferDeclaredCalls fuel budget bounds (.ok queries) candidates build = .error (.inl .exhausted) :=
  inferDeclared_exhausted _ _ _ _ incomplete


/-- Every named method requirement must resolve to a source stamp with the SAME
path/expression, exact Function descriptor identity and direct revision. Reuse the
existing bound-parameter snapshot predicate rather than a second revision engine. -/
def catalogCurrent [DecidableEq Path] [DecidableEq Expression] [DecidableEq Descriptor]
    (requirements : List (Path × Expression))
    (origin : Path → Option (Parameters.BoundParameter (Path × Expression) Descriptor))
    (actual : Path → Option Descriptor) (revision : Descriptor → Nat) : Bool :=
  requirements.all fun required =>
    match origin required.1 with
    | none => false
    | some source => decide (source.name = required) &&
        Parameters.bindingsCurrent [source] (fun _ => actual required.1) revision

/-- A completed named catalog has a matching, current source for EVERY required
method, including siblings that supplied no inference observation. -/
theorem catalogCurrent_sound [DecidableEq Path] [DecidableEq Expression] [DecidableEq Descriptor]
    (requirements : List (Path × Expression))
    (origin : Path → Option (Parameters.BoundParameter (Path × Expression) Descriptor))
    (actual : Path → Option Descriptor) (revision : Descriptor → Nat)
    (accepted : catalogCurrent requirements origin actual revision = true)
    (required : Path × Expression) (member : required ∈ requirements) :
    ∃ source : Parameters.BoundParameter (Path × Expression) Descriptor,
      origin required.1 = some source ∧ source.name = required ∧
      actual required.1 = some source.descriptor ∧ revision source.descriptor = source.revision := by
  have checked := List.all_eq_true.mp accepted required member
  cases found : origin required.1 with
  | none => simp [found] at checked
  | some source =>
    have both : source.name = required ∧
        Parameters.bindingsCurrent [source] (fun _ => actual required.1) revision = true := by
      simpa [found, Bool.and_eq_true] using checked
    have stable := Parameters.bindingsCurrent_sound [source] (fun _ => actual required.1) revision
      both.2 source (by simp)
    exact ⟨source, rfl, both.1, stable⟩

/-- Missing or mismatched provenance rejects the complete artifact, even if all
observed calls were individually satisfiable. External effects are not undone. -/
def admitDeclaredCatalog [DecidableEq Path] [DecidableEq Expression] [DecidableEq Descriptor]
    (requirements : List (Path × Expression))
    (origin : Path → Option (Parameters.BoundParameter (Path × Expression) Descriptor))
    (actual : Path → Option Descriptor) (revision : Descriptor → Nat) (artifact : Artifact) :
    Except PrototypeTypes.Failure Artifact :=
  if catalogCurrent requirements origin actual revision then .ok artifact else .error .bounds

/-- Returning an artifact requires complete named coverage, not a validated subset. -/
theorem admitDeclaredCatalog_sound [DecidableEq Path] [DecidableEq Expression] [DecidableEq Descriptor]
    (requirements : List (Path × Expression))
    (origin : Path → Option (Parameters.BoundParameter (Path × Expression) Descriptor))
    (actual : Path → Option Descriptor) (revision : Descriptor → Nat) (artifact result : Artifact)
    (accepted : admitDeclaredCatalog requirements origin actual revision artifact = .ok result) :
    catalogCurrent requirements origin actual revision = true := by
  unfold admitDeclaredCatalog at accepted
  split at accepted
  · assumption
  · contradiction

/-- Capture and compare the declaration source separately from field revision
checks. The host supplies finite AST/snapshot equality after bounded admission. -/
def admitDeclaredSource [DecidableEq Source] (captured observed : Source) (artifact : Artifact) :
    Except PrototypeTypes.Failure Artifact :=
  if captured = observed then .ok artifact else .error .bounds

/-- Callback-side source changes cannot silently redefine the inferred contract. -/
theorem admitDeclaredSource_stable [DecidableEq Source] (captured observed : Source) (artifact result : Artifact)
    (accepted : admitDeclaredSource captured observed artifact = .ok result) : captured = observed := by
  unfold admitDeclaredSource at accepted
  split at accepted
  · assumption
  · contradiction


/-- Source preservation and full catalog coverage form one publication admission,
with the same all-or-error boundary as the Scheme declaration constructor. -/
def admitDeclaredInterface [DecidableEq Source] [DecidableEq Path] [DecidableEq Expression] [DecidableEq Descriptor]
    (captured observed : Source) (requirements : List (Path × Expression))
    (origin : Path → Option (Parameters.BoundParameter (Path × Expression) Descriptor))
    (actual : Path → Option Descriptor) (revision : Descriptor → Nat) (artifact : Artifact) :
    Except PrototypeTypes.Failure Artifact :=
  match admitDeclaredSource captured observed artifact with
  | .error cause => .error cause
  | .ok checked => admitDeclaredCatalog requirements origin actual revision checked

/-- A returned interface has BOTH its original source and all current required
signatures. Successful inference or one successfully checked sibling is insufficient. -/
theorem admitDeclaredInterface_sound [DecidableEq Source] [DecidableEq Path]
    [DecidableEq Expression] [DecidableEq Descriptor]
    (captured observed : Source) (requirements : List (Path × Expression))
    (origin : Path → Option (Parameters.BoundParameter (Path × Expression) Descriptor))
    (actual : Path → Option Descriptor) (revision : Descriptor → Nat)
    (artifact result : Artifact)
    (accepted : admitDeclaredInterface captured observed requirements origin actual revision artifact = .ok result) :
    captured = observed ∧ catalogCurrent requirements origin actual revision = true := by
  unfold admitDeclaredInterface at accepted
  cases stage : admitDeclaredSource captured observed artifact with
  | error cause => simp [stage] at accepted
  | ok checked =>
    simp only [stage] at accepted
    exact ⟨admitDeclaredSource_stable _ _ _ _ stage, admitDeclaredCatalog_sound _ _ _ _ _ _ accepted⟩


/-- Factory-owned signatures compare their direct revision before any invocation
and again after successful output/cache completion. A source exception keeps its
cause; source effects and unsynchronized writes beyond these observations are not
rolled back or globally linearized by this finite model. -/
def invokeDeclaredSource (captured before : Nat)
    (execute : Unit → Except Error (Result × Owner × Nat)) :
    Except (Sum PrototypeTypes.Failure Error) (Result × Owner) :=
  if captured = before then
    match execute () with
    | .error cause => .error (.inr cause)
    | .ok (result, owner, after) =>
      if captured = after then .ok (result, owner) else .error (.inl .bounds)
  else .error (.inl .bounds)

/-- A directly stale signature cannot enter the callback at all. -/
theorem invokeDeclaredSource_stale (captured before : Nat)
    (execute : Unit → Except Error (Result × Owner × Nat)) (different : captured ≠ before) :
    invokeDeclaredSource captured before execute = .error (.inl .bounds) := by
  simp [invokeDeclaredSource, different]

/-- Original callback/validator errors have priority and keep the exact cause. -/
theorem invokeDeclaredSource_error (captured : Nat)
    (execute : Unit → Except Error (Result × Owner × Nat)) (cause : Error)
    (failed : execute () = .error cause) :
    invokeDeclaredSource captured captured execute = .error (.inr cause) := by
  simp [invokeDeclaredSource, failed]

/-- A revision observed after successful work discards ALL returned values/owner. -/
theorem invokeDeclaredSource_changed (captured after : Nat)
    (execute : Unit → Except Error (Result × Owner × Nat)) (result owner)
    (returned : execute () = .ok (result, owner, after)) (different : captured ≠ after) :
    invokeDeclaredSource captured captured execute = .error (.inl .bounds) := by
  simp [invokeDeclaredSource, returned, different]

/-- A returned owner comes from actual successful work between matching revision
observations. This is not a proof of atomic concurrent metadata revocation. -/
theorem invokeDeclaredSource_sound (captured before : Nat)
    (execute : Unit → Except Error (Result × Owner × Nat)) (result owner)
    (accepted : invokeDeclaredSource captured before execute = .ok (result, owner)) :
    captured = before ∧ execute () = .ok (result, owner, captured) := by
  unfold invokeDeclaredSource at accepted
  split at accepted
  · rename_i initial
    cases run : execute () with
    | error cause => simp [run] at accepted
    | ok response =>
      rcases response with ⟨value, next, after⟩
      simp only [run] at accepted
      split at accepted
      · rename_i final
        cases accepted
        subst after
        exact ⟨initial, rfl⟩
      · contradiction
  · contradiction

end LeanPoo.Functional.DeclarativeMetadata
