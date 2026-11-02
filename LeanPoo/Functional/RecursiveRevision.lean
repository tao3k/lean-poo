import LeanPoo.Functional.RecursiveValidation
import LeanPoo.Functional.StrongComponents

/-! Selective reclosure of finite recursive object catalogs. Existing certified
reachability propagates invalidation, and existing all-or-error closure performs
whole admission. Host dependency completeness, stable recipe/source stamps,
canonical allocation and sequential installation remain correspondence premises.
This advances generalized MOP future work; no arbitrary callback termination,
Scheme GC behavior, concurrent atomicity or retained-function revocation is proved. -/
namespace LeanPoo.Functional.RecursiveRevision
open RecursiveValidation StrongComponents

/-- References carry a node-local generation. A clean target retains its identity;
invalidating it advances the generation even if its payload happens to be equal. -/
def advance (dirty : Fin n → Bool) (generation : Fin n → Nat) (node : Fin n) : Nat :=
  if dirty node then generation node + 1 else generation node

/-- Current named-reference recognition models exact node/generation identity. -/
def recognizes (generation : Fin n → Nat) (node : Fin n) (reference : Fin n × Nat) : Bool :=
  decide (reference = (node,generation node))

/-- Reuse chooses the existing value without evaluating the rebuilding callback.
For Functions this preserves the actual cached closure, without function equality. -/
def select (dirty : Fin n → Bool) (old : Fin n → Value)
    (rebuild : Fin n → Except Error Value) (node : Fin n) : Except Error Value :=
  if dirty node then rebuild node else .ok (old node)

/-- Shape only changed nodes, rebuild only changed payloads, then admit EVERY node
in the complete assembled graph. Reused shape results require unchanged sources
and descriptors; dependency declarations include computed captures and obligations. -/
def reclose (dirty : Fin n → Bool) (generation : Fin n → Nat)
    (old : Fin n → Payload) (edges : Fin n → List (Fin n))
    (shape : Fin n → Except Error Unit) (normalize : Fin n → Except Error Payload)
    (admit : Graph n (Fin n × Nat) Payload → Fin n → Except Error Unit) :=
  close (fun node => (node,advance dirty generation node)) edges
    (select dirty (fun _ => ()) shape) (select dirty old normalize) admit

/-- An unaffected node retains its cached receiver payload and skips rebuilding. -/
theorem clean_select (dirty : Fin n → Bool) (old : Fin n → Value)
    (rebuild : Fin n → Except Error Value) (node : Fin n) (clean : dirty node = false) :
    select dirty old rebuild node = .ok (old node) := by simp [select,clean]

/-- A dirty node runs the actual normalizer; an old equal-valued payload cannot
stand in for its current validation, construction or final-self rebinding. -/
theorem dirty_select (dirty : Fin n → Bool) (old : Fin n → Value)
    (rebuild : Fin n → Except Error Value) (node : Fin n) (changed : dirty node = true) :
    select dirty old rebuild node = rebuild node := by simp [select,changed]

/-- A clean consumer cannot retain an edge or computed capture to a dirty target.
This follows from exact reachability rather than comparing observed outputs. -/
theorem clean_dependency {edge : Fin n → Fin n → Bool} (graph : Checked edge) (seed : Fin n → Bool) (reader target : Fin n)
    (clean : graph.dirty seed reader = false) (reads : Reach edge reader target) :
    graph.dirty seed target = false := by
  cases found : graph.dirty seed target with
  | false => rfl
  | true =>
    have bad := graph.reader_dirty seed reader target ((graph.exact reader target).mpr reads) found
    simp [clean] at bad

/-- Shared inputs invalidate both consumers, including readers in a cyclic group. -/
theorem shared_dirty {edge : Fin n → Fin n → Bool} (graph : Checked edge) (seed : Fin n → Bool)
    (left right shared : Fin n) (leftReads : Reach edge left shared)
    (rightReads : Reach edge right shared) (changed : graph.dirty seed shared = true) :
    graph.dirty seed left = true ∧ graph.dirty seed right = true :=
  ⟨graph.reader_dirty seed left shared ((graph.exact left shared).mpr leftReads) changed,
   graph.reader_dirty seed right shared ((graph.exact right shared).mpr rightReads) changed⟩

/-- Unaffected generations remain valid across a successful unrelated revision. -/
theorem retained_reference (dirty : Fin n → Bool) (generation : Fin n → Nat)
    (node : Fin n) (clean : dirty node = false) :
    recognizes (advance dirty generation) node (node,generation node) = true := by
  simp [recognizes,advance,clean]

/-- A replaced node's old reference is refused, even when its computed result is
unchanged. Host revocation of an old Reference descriptor is a separate guard. -/
theorem old_reference_refused (dirty : Fin n → Bool) (generation : Fin n → Nat)
    (node : Fin n) (changed : dirty node = true) :
    recognizes (advance dirty generation) node (node,generation node) = false := by
  simp [recognizes,advance,changed]

/-- A retained reference from an earlier round is still refused when a later
round changes that target; generation monotonicity prevents accidental ABA reuse. -/
theorem generation_monotone (dirty : Fin n → Bool) (generation : Fin n → Nat) (node : Fin n) :
    generation node ≤ advance dirty generation node := by
  unfold advance; split <;> omega

/-- A reference predating several retained rounds cannot become current again
when its node finally changes, even if earlier generations differed elsewhere. -/
theorem older_reference_refused (dirty : Fin n → Bool) (generation : Fin n → Nat)
    (node : Fin n) (older : Nat) (before : older ≤ generation node) (changed : dirty node = true) :
    recognizes (advance dirty generation) node (node,older) = false := by
  have different : older ≠ generation node + 1 := by omega
  simp [recognizes,advance,changed,different]

/-- Every successful reclosure contains the selected actual payloads and satisfies
all current final obligations. There is no clean-node final-approval shortcut. -/
theorem requirements (dirty : Fin n → Bool) (generation : Fin n → Nat)
    (old : Fin n → Payload) (edges : Fin n → List (Fin n))
    (shape : Fin n → Except Error Unit) (normalize : Fin n → Except Error Payload)
    (admit : Graph n (Fin n × Nat) Payload → Fin n → Except Error Unit)
    (graph : Graph n (Fin n × Nat) Payload)
    (success : reclose dirty generation old edges shape normalize admit = .ok graph) :
    (∀ node, select dirty old normalize node = .ok (graph.payload node)) ∧
    (∀ node, admit graph node = .ok ()) := by
  have complete := RecursiveValidation.requirements _ _ _ _ _ graph success
  exact ⟨complete.2.1,complete.2.2.1⟩

/-- Failed reclosure leaves the caller's previous graph as its returned state.
Callbacks with external effects are outside this pure rollback statement. -/
def commit (old : State) (candidate : Except Error State) : Except Error State × State :=
  match candidate with
  | .error cause => (.error cause,old)
  | .ok next => (.ok next,next)

/-- A refused candidate never becomes the installed snapshot. -/
theorem failed_commit (old : State) (cause : Error) :
    commit old (.error cause : Except Error State) = (.error cause,old) := rfl

/-- Reclosure composes with the existing refinement and exact bind-evidence law;
only the completely admitted current canonical root may be the evidence subject. -/
theorem bound_root [DecidableEq Descriptor] [DecidableEq Context]
    (dirty : Fin n → Bool) (generation : Fin n → Nat)
    (old : Fin n → Payload) (edges : Fin n → List (Fin n))
    (shape : Fin n → Except Error Unit) (normalize : Fin n → Except Error Payload)
    (admit : Graph n (Fin n × Nat) Payload → Fin n → Except Error Unit)
    (graph : Graph n (Fin n × Nat) Payload)
    (success : reclose dirty generation old edges shape normalize admit = .ok graph) (root : Fin n)
    (template : DeclarativeMetadata.Contract Atom (Fin n × Nat) Result)
    (descriptor : Descriptor) (context : Context) (view : Result → (Fin n × Nat) × Descriptor × Context)
    (execute : (Fin n × Nat) → Except Cause (Result × State))
    (receipt : DeclarativeMetadata.Invocation
      (template.bindEvidence (graph.canonical root) descriptor context view) execute (graph.canonical root)) :
    (∀ node, admit graph node = .ok ()) ∧ view receipt.result = (graph.canonical root,descriptor,context) :=
  RecursiveValidation.bound_root _ _ _ _ _ graph success root template descriptor context view execute receipt

end LeanPoo.Functional.RecursiveRevision
