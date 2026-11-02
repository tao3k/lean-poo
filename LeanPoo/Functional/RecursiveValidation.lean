import LeanPoo.Functional.ValidationRebinding
import LeanPoo.Functional.ContainerValidation
import LeanPoo.Functional.PositiveEquations

/-! Controlled finite object graphs, with references interpreted by a supplied
canonical receiver map. Reference edges do not recursively unfold Type checking:
every registered node is normalized and finally admitted. Computed evaluation
uses the existing request/memo semantics; productive delayed edges are distinct
from eager request cycles. This advances generalized MOP future work. Host identity,
getters, mutation guards and callback termination require a separate correspondence. -/
namespace LeanPoo.Functional.RecursiveValidation

/-- Catalog failure stays distinct from recursive evaluation or Type refusal. -/
inductive CatalogError where
  | catalog | duplicate | missingReference
  deriving Repr, BEq

/-- Lower named declarations to a finite reference catalog only after checking
nonempty size, distinct names and every declared Reference target. -/
def checkCatalog [DecidableEq Key] (limit : Nat) (names references : List Key) : Except CatalogError Unit :=
  if names = [] ∨ limit < names.length then .error .catalog
  else if names.Nodup then
    if references.all (fun key => decide (key ∈ names)) then .ok () else .error .missingReference
  else .error .duplicate

/-- Successful preflight has no duplicate or unresolved named target. The
correspondence from these names to Fin indices remains a supplied lowering. -/
theorem catalog_success [DecidableEq Key] (limit : Nat) (names references : List Key) :
    checkCatalog limit names references = .ok () ↔
      names ≠ [] ∧ names.length ≤ limit ∧ names.Nodup ∧ ∀ key ∈ references, key ∈ names := by
  by_cases bounded : names = [] ∨ limit < names.length
  · simp [checkCatalog, bounded]
    rcases bounded with empty | big
    · simp [empty]
    · omega
  · have nonempty : names ≠ [] := fun empty => bounded (Or.inl empty)
    have size : names.length ≤ limit := by omega
    by_cases unique : names.Nodup <;>
      by_cases complete : ∀ key ∈ references, key ∈ names <;>
      simp [checkCatalog, nonempty, Nat.not_lt.mpr size, size, unique, List.all_eq_true, complete]

/-- A finite total catalog collected all-or-error. No active reference is inserted
as a successful validation result; canonical identities are supplied separately. -/
def collect : (n : Nat) → (Fin n → Except Error Value) → Except Error (Fin n → Value)
  | 0, _ => .ok (fun index => Fin.elim0 index)
  | n+1, check => (check 0).bind fun head =>
      (collect n (fun index => check index.succ)).map (Fin.cases head)

/-- Every collected catalog position completed its own validator. -/
theorem collect_apply (check : Fin n → Except Error Value) (values : Fin n → Value)
    (good : collect n check = .ok values) : ∀ index, check index = .ok (values index) := by
  induction n with
  | zero => intro index; exact Fin.elim0 index
  | succ n ih =>
    cases first : check 0 with
    | error cause => simp [collect, first, Except.bind] at good
    | ok head =>
      cases rest : collect n (fun index => check index.succ) with
      | error cause => simp [collect, first, rest, Except.bind, Except.map] at good
      | ok tail =>
        have same : Fin.cases head tail = values := by
          simpa [collect, first, rest, Except.bind, Except.map] using good
        subst values
        intro index
        exact Fin.cases first (fun index => ih _ _ rest index) index

/-- Local completion suffices for finite catalog completion. It does not prove
termination of host callbacks or that arbitrary recursive equations have values. -/
theorem collect_complete (check : Fin n → Except Error Value) (values : Fin n → Value)
    (good : ∀ index, check index = .ok (values index)) : collect n check = .ok values := by
  induction n with
  | zero =>
    change Except.ok (fun index : Fin 0 => Fin.elim0 index) = Except.ok values
    congr 1
    funext index
    exact Fin.elim0 index
  | succ n ih =>
    have tail := ih (fun index => check index.succ) (fun index => values index.succ) (fun index => good index.succ)
    simp only [collect, good 0, Except.bind, tail, Except.map]
    congr 1
    funext index
    exact Fin.cases rfl (fun _ => rfl) index

/-- Payloads may contain opaque checked Functions. Links are finite canonical
identities; cycles and sharing require no infinite value or function equality. -/
structure Graph (n : Nat) (Reference Payload : Type) where
  canonical : Fin n → Reference
  payload : Fin n → Payload
  links : Fin n → List Reference

/-- Install every reference through the one preallocated receiver map. The input
Fin indices encode an already checked finite catalog, including all link targets. -/
def assemble (canonical : Fin n → Reference) (payload : Fin n → Payload)
    (edges : Fin n → List (Fin n)) : Graph n Reference Payload :=
  ⟨canonical, payload, fun index => (edges index).map canonical⟩

/-- Shape all nodes first, normalize all nodes second, admit the complete graph
last. No intermediate receiver graph is returned by this pure publication API. -/
def close (canonical : Fin n → Reference) (edges : Fin n → List (Fin n))
    (shape : Fin n → Except Error Unit) (normalize : Fin n → Except Error Payload)
    (admit : Graph n Reference Payload → Fin n → Except Error Unit) : Except Error (Graph n Reference Payload) :=
  (collect n shape).bind fun _ => (collect n normalize).bind fun values =>
    let graph := assemble canonical values edges
    (collect n (admit graph)).map fun _ => graph

/-- Whole-catalog structural refusal suppresses every node normalizer. -/
theorem shape_error (canonical : Fin n → Reference) (edges : Fin n → List (Fin n))
    (shape : Fin n → Except Error Unit) (normalize : Fin n → Except Error Payload)
    (admit : Graph n Reference Payload → Fin n → Except Error Unit) (cause : Error)
    (failed : collect n shape = .error cause) : close canonical edges shape normalize admit = .error cause := by
  simp [close, failed, Except.bind]

/-- A node-batch error cannot expose a partly normalized cyclic graph. -/
theorem normalization_error (canonical : Fin n → Reference) (edges : Fin n → List (Fin n))
    (shape : Fin n → Except Error Unit) (normalize : Fin n → Except Error Payload)
    (admit : Graph n Reference Payload → Fin n → Except Error Unit) (shapes : Fin n → Unit) (cause : Error)
    (structural : collect n shape = .ok shapes) (failed : collect n normalize = .error cause) :
    close canonical edges shape normalize admit = .error cause := by
  simp [close, structural, failed, Except.bind]

/-- A remote whole-graph obligation still rejects after all local nodes normalize. -/
theorem admission_error (canonical : Fin n → Reference) (edges : Fin n → List (Fin n))
    (shape : Fin n → Except Error Unit) (normalize : Fin n → Except Error Payload)
    (admit : Graph n Reference Payload → Fin n → Except Error Unit)
    (shapes : Fin n → Unit) (values : Fin n → Payload) (cause : Error)
    (structural : collect n shape = .ok shapes) (normalized : collect n normalize = .ok values)
    (failed : collect n (admit (assemble canonical values edges)) = .error cause) :
    close canonical edges shape normalize admit = .error cause := by
  simp [close, structural, normalized, failed, Except.bind, Except.map]

/-- Successful closure has every shape, actual normalized payload and final node
obligation. None of the references grants permission to skip target validation. -/
theorem requirements (canonical : Fin n → Reference) (edges : Fin n → List (Fin n))
    (shape : Fin n → Except Error Unit) (normalize : Fin n → Except Error Payload)
    (admit : Graph n Reference Payload → Fin n → Except Error Unit) (graph : Graph n Reference Payload)
    (success : close canonical edges shape normalize admit = .ok graph) :
    (∀ index, shape index = .ok ()) ∧ (∀ index, normalize index = .ok (graph.payload index)) ∧
    (∀ index, admit graph index = .ok ()) ∧ graph.canonical = canonical ∧
    graph.links = (fun index => (edges index).map canonical) := by
  cases first : collect n shape with
  | error cause => simp [close, first, Except.bind] at success
  | ok shapes =>
    cases second : collect n normalize with
    | error cause => simp [close, first, second, Except.bind] at success
    | ok values =>
      cases last : collect n (admit (assemble canonical values edges)) with
      | error cause => simp [close, first, second, last, Except.bind, Except.map] at success
      | ok admitted =>
        have same : assemble canonical values edges = graph := by
          simpa [close, first, second, last, Except.bind, Except.map] using success
        subst graph
        refine ⟨?_, collect_apply normalize values second, ?_, rfl, rfl⟩
        · intro index; simpa using collect_apply shape shapes first index
        · intro index; simpa using collect_apply _ admitted last index

/-- A checked backedge names the same canonical target, without unfolding it. -/
theorem edge_preserved (canonical : Fin n → Reference) (edges : Fin n → List (Fin n))
    (payload : Fin n → Payload) (source target : Fin n) (edge : target ∈ edges source) :
    canonical target ∈ (assemble canonical payload edges).links source := by
  exact List.mem_map.mpr ⟨target, edge, rfl⟩

/-- Two paths ending at the same named target retain one receiver identity. -/
theorem shared_target (canonical : Fin n → Reference) (left right : Fin n) (same : left = right) :
    canonical left = canonical right := congrArg canonical same

/-- Supplied allocation injectivity prevents accidental merging of distinct nodes. -/
theorem distinct_targets (canonical : Fin n → Reference) (unique : Function.Injective canonical)
    (left right : Fin n) (different : left ≠ right) : canonical left ≠ canonical right := by
  exact fun same => different (unique same)

/-- Bind publication to the actual canonical root of a completely admitted graph.
The caller supplies reference/context correspondence and immutable source scope. -/
theorem bound_root [DecidableEq Reference] [DecidableEq Descriptor] [DecidableEq Context]
    (canonical : Fin n → Reference) (edges : Fin n → List (Fin n))
    (shape : Fin n → Except Error Unit) (normalize : Fin n → Except Error Payload)
    (admit : Graph n Reference Payload → Fin n → Except Error Unit) (graph : Graph n Reference Payload)
    (success : close canonical edges shape normalize admit = .ok graph) (root : Fin n)
    (template : DeclarativeMetadata.Contract Atom Reference Result) (descriptor : Descriptor) (context : Context)
    (view : Result → Reference × Descriptor × Context) (execute : Reference → Except Cause (Result × State))
    (receipt : DeclarativeMetadata.Invocation
      (template.bindEvidence (graph.canonical root) descriptor context view) execute (graph.canonical root)) :
    (∀ index, admit graph index = .ok ()) ∧
    view receipt.result = (graph.canonical root,descriptor,context) := by
  have valid := requirements canonical edges shape normalize admit graph success
  have bound := template.bindEvidence_accepted (graph.canonical root) descriptor context view
    execute (graph.canonical root) receipt
  exact ⟨valid.2.2.1, bound.2.2⟩

end LeanPoo.Functional.RecursiveValidation
