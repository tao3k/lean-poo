import LeanPoo.C4.OrdinaryNode
import LeanPoo.C4.VerifiedOrder

namespace LeanPoo.C4.LinearizeState

/-- Resolve parents first, computing each fresh node in ordinary mode once and
retaining acceptance through its audit. Cache hits and fuel match `resolveNode`. -/
def resolveAuditedNode (index : Std.HashMap String Node) (root name : String)
    (table : Table) : Nat → Except Error Table
  | 0 => if (lookup table name).isSome then .ok table else .error (.cycle root)
  | fuel + 1 => do
      if (lookup table name).isSome then return table
      let some node := index.get? name | throw (.unknownNode name)
      let ready ← resolveParents (fun parent before => resolveAuditedNode index root parent before fuel)
        (parents node) table
      let receipt ← computeAuditedNode ready node
      return ready.insert name receipt.result

private theorem resolveParents_transfer (valid : MetadataInvariant graph table)
    (step : ∀ parent ∈ names, ∀ before after, MetadataInvariant graph before →
      action parent before = .ok after → target parent before = .ok after ∧ MetadataInvariant graph after)
    (success : resolveParents action names table = .ok ready) :
    resolveParents target names table = .ok ready ∧ MetadataInvariant graph ready := by
  induction names generalizing table with
  | nil =>
    have same : table = ready := Except.ok.inj success
    subst ready; exact ⟨rfl, valid⟩
  | cons parent rest ih =>
    cases first : action parent table with
    | error error => simp [resolveParents, List.forIn_cons, first, bind, Except.bind] at success
    | ok middle =>
      have remaining : resolveParents action rest middle = .ok ready := by
        simpa only [resolveParents, List.forIn_cons, first, bind, Except.bind, pure, Except.pure] using success
      obtain ⟨targetFirst, validMiddle⟩ := step parent (by simp) table middle valid first
      obtain ⟨targetRest, validReady⟩ := ih validMiddle
        (fun name member => step name (by simp [member])) remaining
      exact ⟨by simpa only [resolveParents, List.forIn_cons, targetFirst, bind, Except.bind,
        pure, Except.pure] using targetRest, validReady⟩

/-- A successful audited recursion agrees with both existing modes and carries
canonical metadata forward. No caller-supplied root trace is needed. -/
theorem resolveAuditedNode_acceptance (valid : MetadataInvariant graph table)
    (success : resolveAuditedNode (nodeIndex graph) root name table fuel = .ok ready) :
    resolveNode (nodeIndex graph) root name table true fuel = .ok ready ∧
    resolveNode (nodeIndex graph) root name table false fuel = .ok ready ∧
    MetadataInvariant graph ready := by
  induction fuel generalizing name table ready with
  | zero =>
    cases cached : lookup table name with
    | none => simp [resolveAuditedNode, cached] at success
    | some entry =>
      have same : table = ready := by simpa [resolveAuditedNode, cached] using success
      subst ready
      exact ⟨resolveNode_cached cached, resolveNode_cached cached, valid⟩
  | succ fuel ih =>
    cases cached : lookup table name with
    | some entry =>
      have same : table = ready := by simpa [resolveAuditedNode, cached, pure, Except.pure] using success
      subst ready
      exact ⟨resolveNode_cached cached, resolveNode_cached cached, valid⟩
    | none =>
      cases indexed : (nodeIndex graph)[name]? with
      | none => simp [resolveAuditedNode, cached, Std.HashMap.get?_eq_getElem?, indexed] at success
      | some node =>
        have execution : (do
          let next ← resolveParents (fun parent before =>
            resolveAuditedNode (nodeIndex graph) root parent before fuel) (parents node) table
          let receipt ← computeAuditedNode next node
          pure (next.insert name receipt.result)) = .ok ready := by
          simpa only [resolveAuditedNode, cached, Option.isSome_none, Bool.false_eq_true,
            ↓reduceIte, Std.HashMap.get?_eq_getElem?, indexed] using success
        cases parentsDone : resolveParents (fun parent before =>
            resolveAuditedNode (nodeIndex graph) root parent before fuel) (parents node) table with
        | error error => simp [parentsDone, bind, Except.bind] at execution
        | ok next =>
          have checkedParents := resolveParents_transfer valid
            (target := fun parent before => resolveNode (nodeIndex graph) root parent before true fuel)
            (fun _ _ _ _ validBefore done => by
              obtain ⟨checked, _, validAfter⟩ := ih validBefore done
              exact ⟨checked, validAfter⟩) parentsDone
          have ordinaryParents := resolveParents_transfer valid
            (target := fun parent before => resolveNode (nodeIndex graph) root parent before false fuel)
            (fun _ _ _ _ validBefore done => by
              obtain ⟨_, ordinary, validAfter⟩ := ih validBefore done
              exact ⟨ordinary, validAfter⟩) parentsDone
          cases computed : computeAuditedNode next node with
          | error error => simp [parentsDone, computed, bind, Except.bind] at execution
          | ok receipt =>
            have same : next.insert name receipt.result = ready := by
              simpa [parentsDone, computed, bind, Except.bind, pure, Except.pure] using execution
            have checkedNode := receipt.checked checkedParents.2
            have checked : resolveNode (nodeIndex graph) root name table true (fuel + 1) = .ok ready := by
              simp only [resolveNode, cached, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
                Std.HashMap.get?_eq_getElem?, indexed]
              change (do
                let next ← resolveParents (fun parent before =>
                  resolveNode (nodeIndex graph) root parent before true fuel) (parents node) table
                let result ← computeNode next node true
                pure (next.insert name result)) = .ok ready
              simpa only [checkedParents.1, checkedNode, bind, Except.bind, pure, Except.pure]
                using congrArg Except.ok same
            have ordinary : resolveNode (nodeIndex graph) root name table false (fuel + 1) = .ok ready := by
              simp only [resolveNode, cached, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
                Std.HashMap.get?_eq_getElem?, indexed]
              change (do
                let next ← resolveParents (fun parent before =>
                  resolveNode (nodeIndex graph) root parent before false fuel) (parents node) table
                let result ← computeNode next node false
                pure (next.insert name result)) = .ok ready
              simpa only [ordinaryParents.1, receipt.ordinary, bind, Except.bind, pure, Except.pure]
                using congrArg Except.ok same
            exact ⟨checked, ordinary, (resolveNode_checked_sound valid checked).1⟩

/-- Auditing loses no successful checked recursion on canonical caches,
including cache hits at zero fuel and shared parent executions. -/
theorem resolveAuditedNode_checked_complete (valid : MetadataInvariant graph table)
    (success : resolveNode (nodeIndex graph) root name table true fuel = .ok ready) :
    resolveAuditedNode (nodeIndex graph) root name table fuel = .ok ready := by
  induction fuel generalizing name table ready with
  | zero =>
    cases cached : lookup table name with
    | none => simp [resolveNode, cached] at success
    | some entry => simpa [resolveNode, resolveAuditedNode, cached] using success
  | succ fuel ih =>
    cases cached : lookup table name with
    | some entry => simpa [resolveNode, resolveAuditedNode, cached, pure, Except.pure] using success
    | none =>
      cases indexed : (nodeIndex graph)[name]? with
      | none => simp [resolveNode, cached, Std.HashMap.get?_eq_getElem?, indexed] at success
      | some node =>
        have execution : (do
          let next ← resolveParents (fun parent before =>
            resolveNode (nodeIndex graph) root parent before true fuel) (parents node) table
          let result ← computeNode next node true
          pure (next.insert name result)) = .ok ready := by
          simp only [resolveNode, cached, Option.isSome_none, Bool.false_eq_true,
            ↓reduceIte, Std.HashMap.get?_eq_getElem?, indexed] at success
          exact success
        cases parentsDone : resolveParents (fun parent before =>
            resolveNode (nodeIndex graph) root parent before true fuel) (parents node) table with
        | error error => simp [parentsDone, bind, Except.bind] at execution
        | ok next =>
          have auditedParents := resolveParents_transfer valid
            (target := fun parent before => resolveAuditedNode (nodeIndex graph) root parent before fuel)
            (fun _ _ _ _ validBefore done =>
              ⟨ih validBefore done, (resolveNode_checked_sound validBefore done).1⟩) parentsDone
          cases computed : computeNode next node true with
          | error error => simp [parentsDone, computed, bind, Except.bind] at execution
          | ok result =>
            obtain ⟨receipt, auditedNode, resultSame⟩ :=
              computeAuditedNode_checked_complete auditedParents.2 computed
            have same : next.insert name result = ready := by
              simpa [parentsDone, computed, bind, Except.bind, pure, Except.pure] using execution
            simp only [resolveAuditedNode, cached, Option.isSome_none, Bool.false_eq_true,
              ↓reduceIte, Std.HashMap.get?_eq_getElem?, indexed, auditedParents.1,
              auditedNode, bind, Except.bind, pure, Except.pure, resultSame, same]

/-- Exact success equivalence of audited and checked recursion. The initial
cache must be canonical; failure payloads need not coincide. -/
theorem resolveAuditedNode_success_iff (valid : MetadataInvariant graph table) :
    resolveAuditedNode (nodeIndex graph) root name table fuel = .ok ready ↔
      resolveNode (nodeIndex graph) root name table true fuel = .ok ready :=
  ⟨fun success => (resolveAuditedNode_acceptance valid success).1,
    resolveAuditedNode_checked_complete valid⟩

/-- Recover the original graph contract for the actual result of an audited
recursive execution, including executions that start from a canonical cache. -/
theorem resolveAuditedNode_graph_sound (valid : MetadataInvariant graph table)
    (success : resolveAuditedNode (nodeIndex graph) root name table fuel = .ok ready) :
    ∃ entry, lookup ready name = some entry ∧
      GraphTrace graph name entry.precedence (selectedTail ready entry.mostSpecificSuffix) :=
  resolveNode_checked_graph_sound valid (resolveAuditedNode_acceptance valid success).1

end LeanPoo.C4.LinearizeState

namespace LeanPoo.C4

/-- Compile a finite graph with ordinary computation plus a per-node audit.
Validation and reachability follow the existing compilers. An audit rejection
is a diagnostic of this API, not an equality claim about checked error payloads. -/
def linearizeAudited (graph : Graph) (root : String) : Except Error (List String) := do
  let index := LinearizeState.nodeIndex graph
  if (index.get? root).isNone then throw (.unknownNode root)
  let names := LinearizeState.reachable graph index root
  let namesSet := names.foldl (fun seen name => seen.insert name) ({} : Std.HashSet String)
  let nodes := graph.nodes.filter (fun node => namesSet.contains node.name)
  ({ nodes } : Graph).validate
  let table ← LinearizeState.resolveAuditedNode index root root {} nodes.length
  let some result := LinearizeState.lookup table root | throw (.cycle root)
  return result.precedence

/-- Successful auditing returns the exact result of each existing compiler. -/
theorem linearizeAudited_accepts_mode (success : linearizeAudited graph root = .ok output)
    (checked : Bool) : LinearizeState.linearizeWith graph root checked = .ok output := by
  unfold linearizeAudited LinearizeState.linearizeWith at *
  cases indexed : (LinearizeState.nodeIndex graph)[root]? with
  | none => simp [Std.HashMap.get?_eq_getElem?, indexed, bind, Except.bind] at success
  | some node =>
    simp only [Std.HashMap.get?_eq_getElem?, indexed, Option.isNone_some,
      Bool.false_eq_true, ↓reduceIte] at success ⊢
    generalize declarations : graph.nodes.filter (fun node =>
      ((LinearizeState.reachable graph (LinearizeState.nodeIndex graph) root).foldl
        (fun seen name => seen.insert name) ({} : Std.HashSet String)).contains node.name) = nodes at success ⊢
    cases validated : (Graph.mk nodes).validate with
    | error error => simp [validated, bind, Except.bind] at success
    | ok acceptedUnit =>
      cases computed : LinearizeState.resolveAuditedNode (LinearizeState.nodeIndex graph)
          root root {} nodes.length with
      | error error => simp [validated, computed, bind, Except.bind] at success
      | ok table =>
        obtain ⟨checkedDone, ordinaryDone, _⟩ := LinearizeState.resolveAuditedNode_acceptance
          (LinearizeState.MetadataInvariant.empty graph) computed
        have done : LinearizeState.resolveNode (LinearizeState.nodeIndex graph)
            root root {} checked nodes.length = .ok table := by
          cases checked
          · exact ordinaryDone
          · exact checkedDone
        obtain ⟨entry, cached, _⟩ := LinearizeState.resolveNode_checked_graph_sound
          (LinearizeState.MetadataInvariant.empty graph) checkedDone
        simpa [validated, computed, done, bind, Except.bind, cached, pure, Except.pure] using success

/-- Every successful checked graph compilation is accepted by the audited
compiler with the same output, starting from its own empty cache. -/
theorem linearizeAudited_checked_complete (success : linearizeChecked graph root = .ok output) :
    linearizeAudited graph root = .ok output := by
  unfold linearizeChecked LinearizeState.linearizeWith at success
  unfold linearizeAudited
  cases indexed : (LinearizeState.nodeIndex graph)[root]? with
  | none => simp [Std.HashMap.get?_eq_getElem?, indexed, bind, Except.bind] at success
  | some node =>
    simp only [Std.HashMap.get?_eq_getElem?, indexed, Option.isNone_some,
      Bool.false_eq_true, ↓reduceIte] at success ⊢
    generalize declarations : graph.nodes.filter (fun node =>
      ((LinearizeState.reachable graph (LinearizeState.nodeIndex graph) root).foldl
        (fun seen name => seen.insert name) ({} : Std.HashSet String)).contains node.name) = nodes at success ⊢
    cases validated : (Graph.mk nodes).validate with
    | error error => simp [validated, bind, Except.bind] at success
    | ok acceptedUnit =>
      cases computed : LinearizeState.resolveNode (LinearizeState.nodeIndex graph)
          root root {} true nodes.length with
      | error error => simp [validated, computed, bind, Except.bind] at success
      | ok table =>
        have audited := LinearizeState.resolveAuditedNode_checked_complete
          (LinearizeState.MetadataInvariant.empty graph) computed
        obtain ⟨entry, cached, _⟩ := LinearizeState.resolveNode_checked_graph_sound
          (LinearizeState.MetadataInvariant.empty graph) computed
        simpa [validated, computed, audited, bind, Except.bind, cached, pure, Except.pure] using success

/-- Audited and checked graph compilers have exactly the same successful
outputs for every graph and root; there are no caller validity premises. -/
theorem linearizeAudited_success_iff :
    linearizeAudited graph root = .ok output ↔ linearizeChecked graph root = .ok output :=
  ⟨fun success => linearizeAudited_accepts_mode success true, linearizeAudited_checked_complete⟩

/-- Both compilers return the same optional successful result. This allows
clients to interchange them when diagnostics are intentionally discarded. -/
theorem linearizeAudited_toOption :
    (linearizeAudited graph root).toOption = (linearizeChecked graph root).toOption := by
  cases audited : linearizeAudited graph root with
  | error error =>
    cases checked : linearizeChecked graph root with
    | error other => rfl
    | ok output =>
      have impossible := linearizeAudited_checked_complete checked
      rw [audited] at impossible
      cases impossible
  | ok output => rw [(linearizeAudited_success_iff).mp audited]

/-- End-to-end graph soundness of a successful audited compiler execution.
There are no caller trace, node compatibility, or cache invariant premises. -/
theorem linearizeAudited_graph_sound (success : linearizeAudited graph root = .ok output) :
    ∃ tail, GraphTrace graph root output tail :=
  linearizeChecked_graph_sound (linearizeAudited_accepts_mode success true)

/-- Ordinary success alone remains insufficient: this transfer starts from a
successful audited execution and returns the same output. -/
theorem linearizeAudited_ordinary (success : linearizeAudited graph root = .ok output) :
    linearize graph root = .ok output := linearizeAudited_accepts_mode success false

/-- Retain all existing verified-order query and proof APIs after ordinary
computation plus audits. This wrapper does not execute the checked compiler. -/
def linearizeAuditedVerified (graph : Graph) (root : String) : Except Error (VerifiedOrder graph root) :=
  match success : linearizeAudited graph root with
  | .error error => .error error
  | .ok output => .ok ⟨output, linearizeAudited_accepts_mode success true,
      linearizeAudited_graph_sound success⟩

/-- The retained wrapper preserves the audited compiler's outputs and errors. -/
theorem linearizeAuditedVerified_projection :
    (linearizeAuditedVerified graph root).map (·.output) = linearizeAudited graph root := by
  unfold linearizeAuditedVerified
  split <;> simp_all [Except.map]

/-- Retaining the audited verified-order interface loses no checked successful
output. Errors retain audited diagnostics and are discarded by this projection. -/
theorem linearizeAuditedVerified_toOption :
    ((linearizeAuditedVerified graph root).map (·.output)).toOption =
      (linearizeChecked graph root).toOption := by
  rw [linearizeAuditedVerified_projection, linearizeAudited_toOption]

end LeanPoo.C4
