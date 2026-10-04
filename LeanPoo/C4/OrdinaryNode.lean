import LeanPoo.C4.NodeSoundness

namespace LeanPoo.C4.LinearizeState

/-- Every actual collected parent precedence is compatible with the actual
selected shared tail. Ordinary execution checks only local declarations. -/
def ParentCompatible (table : Table) (node : Node) : Prop :=
  ∀ entries chosen, collectParents table (parents node) = .ok entries →
    selectSuffix table (entries.map (·.mostSpecificSuffix)) none = .ok chosen →
    ∀ entry ∈ entries, SuffixCompatible entry.precedence (selectedTail table chosen)

/-- Successful ordinary execution exposes the merge trace and exact runtime
inputs. It does not itself establish compatibility of complete parent orders. -/
theorem computeNode_ordinary_evidence (success : computeNode table node false = .ok result) :
    ∃ entries chosen front,
      collectParents table (parents node) = .ok entries ∧
      selectSuffix table (entries.map (·.mostSpecificSuffix)) none = .ok chosen ∧
      (∀ order ∈ MergeState.pending node.parentOrders,
        SuffixCompatible order (selectedTail table chosen)) ∧
      Precedence.Trace ((entries.map (·.precedence) ++ MergeState.pending node.parentOrders).map
        (fun order => withoutTail order (selectedTail table chosen))) front ∧
      result = {
        precedence := node.name :: (front ++ selectedTail table chosen)
        inheritedSuffix := chosen
        mostSpecificSuffix := if node.suffix then some node.name else chosen } := by
  unfold computeNode at success
  cases collected : collectParents table (parents node) with
  | error error => simp [collected, bind, Except.bind] at success
  | ok entries =>
    cases selected : selectSuffix table (entries.map (·.mostSpecificSuffix)) none with
    | error error => simp [collected, selected, bind, Except.bind] at success
    | ok chosen =>
      cases read : readSuffix table chosen with
      | error error => simp [collected, selected, read, bind, Except.bind] at success
      | ok tail =>
        have same := readSuffix_sound read
        simp only [collected, selected, read, bind, Except.bind] at success
        split at success
        · simp at success
        · rename_i accepted
          have localAccepted : (MergeState.pending node.parentOrders).all
              (fun order => respectsSuffixTail order tail) = true := by
            change (node.parentOrders.filter (fun order => !order.isEmpty)).all
              (fun order => respectsSuffixTail order tail) = true
            cases outcome : (node.parentOrders.filter (fun order => !order.isEmpty)).all
                (fun order => respectsSuffixTail order tail) with
            | false => simp [outcome] at accepted
            | true => rfl
          simp only [show node.parentOrders.filter (fun order => !order.isEmpty) =
            MergeState.pending node.parentOrders from rfl, Bool.false_eq_true, ↓reduceIte,
            pure, Except.pure] at success
          cases merged : merge (entries.map (fun entry => withoutTail entry.precedence tail) ++
              (MergeState.pending node.parentOrders).map (fun order => withoutTail order tail)) with
          | error error => simp [merged] at success
          | ok front =>
            refine ⟨entries, chosen, front, rfl, selected, ?_, ?_, ?_⟩
            · intro order member
              rw [← same]
              exact respectsSuffixTail_sound (List.all_eq_true.mp localAccepted order member)
            · simpa only [same, List.map_append, List.map_map, Function.comp_def] using
                MergeState.merge_sound merged
            · simp only [merged, Except.ok.injEq] at success
              simpa only [same] using success.symm

/-- Complete parent compatibility and duplicate-free ordinary output suffice
for checked acceptance of the exact same result, under canonical metadata.
No root GraphTrace or caller-supplied node certificate is assumed. -/
theorem computeNode_ordinary_checked (valid : MetadataInvariant graph table)
    (compatible : ParentCompatible table node) (unique : result.precedence.Nodup)
    (success : computeNode table node false = .ok result) :
    computeNode table node true = .ok result := by
  obtain ⟨entries, chosen, front, collected, selected, localCompatible, trace, same⟩ :=
    computeNode_ordinary_evidence success
  obtain ⟨selection, tailSame⟩ := collected_suffix_selection_certified valid collected selected
  let ancestry : SuffixCertified
      (entries.map (·.precedence) ++ MergeState.pending node.parentOrders) selection.output := {
    front := front
    trace := by simpa only [tailSame] using trace
    compatible := by
      intro order member
      rw [tailSame]
      rcases List.mem_append.mp member with parent | declared
      · obtain ⟨entry, present, same⟩ := List.mem_map.mp parent
        subst order
        exact compatible entries chosen collected selected entry present
      · exact localCompatible order declared }
  have noDuplicates : (node.name :: (front ++ selection.output)).Nodup := by
    simpa only [same, tailSame] using unique
  have fresh : node.name ∉ ancestry.output := (List.nodup_cons.mp noDuplicates).1
  have tailUnique : selection.output.Nodup :=
    (List.nodup_append.mp (List.nodup_cons.mp noDuplicates).2).2.1
  let certificate : NodeCertified node.name
      (entries.map (·.precedence) ++ MergeState.pending node.parentOrders)
      (suffixTails table (entries.map (·.mostSpecificSuffix))) :=
    ⟨selection, ancestry, tailUnique, fresh⟩
  have checked := computeNode_complete collected selected
    (collected_suffix_available valid collected) certificate tailSame true
  simpa only [certificate, NodeCertified.output, ancestry, SuffixCertified.output, tailSame, same] using checked

/-- Checked success implies the additional complete-parent compatibility
which ordinary execution does not check. No metadata invariant is needed. -/
theorem computeNode_checked_parentCompatible (success : computeNode table node true = .ok result) :
    ParentCompatible table node := by
  obtain ⟨entries, chosen, _, certificate, collected, selected, _, claimed, _⟩ :=
    computeNode_checked_evidence success
  intro actual selectedName collectedActual selectedActual entry member
  have entriesSame := Except.ok.inj (collected.symm.trans collectedActual)
  subst actual
  have chosenSame := Except.ok.inj (selected.symm.trans selectedActual)
  subst selectedName
  rw [← claimed]
  exact certificate.ancestry.compatible entry.precedence
    (List.mem_append_left _ (List.mem_map.mpr ⟨entry, member, rfl⟩))

/-- Exact single-node acceptance characterization on canonical cached parents.
This is a conditional mode equivalence, not an unconditional graph theorem. -/
theorem computeNode_checked_iff (valid : MetadataInvariant graph table) :
    computeNode table node true = .ok result ↔
      computeNode table node false = .ok result ∧ result.precedence.Nodup ∧ ParentCompatible table node := by
  constructor
  · intro checked
    exact ⟨computeNode_checked_ordinary checked, (computeNode_checked_laws checked).1,
      computeNode_checked_parentCompatible checked⟩
  · rintro ⟨ordinary, unique, compatible⟩
    exact computeNode_ordinary_checked valid compatible unique ordinary

/-- The conditional ordinary result also has the original graph contract. -/
theorem computeNode_ordinary_graph_sound (valid : MetadataInvariant graph table)
    (found : graph.findNode? node.name = some node)
    (compatible : ParentCompatible table node) (unique : result.precedence.Nodup)
    (success : computeNode table node false = .ok result) :
    GraphTrace graph node.name result.precedence
      (if node.suffix then result.precedence else selectedTail table result.inheritedSuffix) :=
  computeNode_checked_graph_sound valid found (computeNode_ordinary_checked valid compatible unique success)

/-- Audit an already obtained ordinary result without invoking a merger.
Errors describe this audit, not complete checked-mode error equivalence. -/
def auditNode (table : Table) (node : Node) (result : Linearization) : Except Error Unit := do
  let entries ← collectParents table (parents node)
  let chosen ← selectSuffix table (entries.map (·.mostSpecificSuffix)) none
  let tail ← readSuffix table chosen
  if !entries.all (fun entry => respectsSuffixTail entry.precedence tail) then
    throw .suffixOrderViolation
  if result.precedence.Nodup then pure () else throw .inconsistentOrder

/-- Successful audit supplies both extra conditions; it does not claim that
an arbitrary supplied result was produced by ordinary execution. -/
theorem auditNode_sound (audited : auditNode table node result = .ok ()) :
    ParentCompatible table node ∧ result.precedence.Nodup := by
  unfold auditNode at audited
  cases collected : collectParents table (parents node) with
  | error error => simp [collected, bind, Except.bind] at audited
  | ok entries =>
    cases selected : selectSuffix table (entries.map (·.mostSpecificSuffix)) none with
    | error error => simp [collected, selected, bind, Except.bind] at audited
    | ok chosen =>
      cases read : readSuffix table chosen with
      | error error => simp [collected, selected, read, bind, Except.bind] at audited
      | ok tail =>
        simp only [collected, selected, read, bind, Except.bind] at audited
        split at audited
        · simp at audited
        · rename_i accepted
          have allAccepted : entries.all (fun entry => respectsSuffixTail entry.precedence tail) = true := by
            cases outcome : entries.all (fun entry => respectsSuffixTail entry.precedence tail) with
            | false => simp [outcome] at accepted
            | true => rfl
          split at audited
          · rename_i unique
            refine ⟨?_, unique⟩
            intro actual selectedName collectedActual selectedActual entry member
            have entriesSame := Except.ok.inj (collected.symm.trans collectedActual)
            subst actual
            have chosenSame := Except.ok.inj (selected.symm.trans selectedActual)
            subst selectedName
            rw [← readSuffix_sound read]
            exact respectsSuffixTail_sound (List.all_eq_true.mp allAccepted entry member)
          · simp at audited

/-- On actual ordinary success, the additional conditions pass the executable
checks. Output uniqueness supplies the selected tail's uniqueness. -/
theorem auditNode_complete (valid : MetadataInvariant graph table)
    (compatible : ParentCompatible table node) (unique : result.precedence.Nodup)
    (ordinary : computeNode table node false = .ok result) :
    auditNode table node result = .ok () := by
  obtain ⟨entries, chosen, front, collected, selected, _, _, same⟩ :=
    computeNode_ordinary_evidence ordinary
  have noDuplicates : (node.name :: (front ++ selectedTail table chosen)).Nodup := by
    simpa only [same] using unique
  have tailUnique : (selectedTail table chosen).Nodup :=
    (List.nodup_append.mp (List.nodup_cons.mp noDuplicates).2).2.1
  have available := collected_suffix_available valid collected
  have read : readSuffix table chosen = .ok (selectedTail table chosen) := by
    apply readSuffix_complete
    intro name chosenName
    rw [chosenName] at selected
    rcases (selectSuffix_sound selected).1 with impossible | member
    · cases impossible
    · exact available name member
  have accepted : entries.all (fun entry => respectsSuffixTail entry.precedence (selectedTail table chosen)) = true :=
    List.all_eq_true.mpr (fun entry member => respectsSuffixTail_complete
      (compatible entries chosen collected selected entry member) tailUnique)
  simp [auditNode, collected, selected, read, accepted, unique, bind, Except.bind, pure, Except.pure]

/-- Promote the exact ordinary result using an audit receipt and canonical
metadata. This proves checked acceptance without executing checked again. -/
theorem computeNode_audited_checked (valid : MetadataInvariant graph table)
    (ordinary : computeNode table node false = .ok result)
    (audited : auditNode table node result = .ok ()) : computeNode table node true = .ok result :=
  computeNode_ordinary_checked valid (auditNode_sound audited).1 (auditNode_sound audited).2 ordinary

/-- Exact executable audit acceptance at the single-node boundary. Actual
ordinary execution and canonical metadata are explicit premises. -/
theorem auditNode_acceptance_iff (valid : MetadataInvariant graph table)
    (ordinary : computeNode table node false = .ok result) :
    auditNode table node result = .ok () ↔ computeNode table node true = .ok result := by
  constructor
  · exact computeNode_audited_checked valid ordinary
  · intro checked
    exact auditNode_complete valid (computeNode_checked_parentCompatible checked)
      (computeNode_checked_laws checked).1 ordinary

/-- The promoted ordinary result has the original graph contract. The actual
execution receipt remains required; auditing an invented result is insufficient. -/
theorem computeNode_audited_graph_sound (valid : MetadataInvariant graph table)
    (found : graph.findNode? node.name = some node)
    (ordinary : computeNode table node false = .ok result)
    (audited : auditNode table node result = .ok ()) :
    GraphTrace graph node.name result.precedence
      (if node.suffix then result.precedence else selectedTail table result.inheritedSuffix) :=
  computeNode_checked_graph_sound valid found (computeNode_audited_checked valid ordinary audited)

/-- Retain exact ordinary execution and audit receipts. Proof fields erase;
the result remains bound to this table and node. -/
structure AuditedNode (table : Table) (node : Node) where
  result : Linearization
  ordinary : computeNode table node false = .ok result
  audited : auditNode table node result = .ok ()

/-- Compute one ordinary node and audit it. The audit contains no merge and
this wrapper does not execute the checked compiler. -/
def computeAuditedNode (table : Table) (node : Node) : Except Error (AuditedNode table node) :=
  match ordinary : computeNode table node false with
  | .error error => .error error
  | .ok result =>
    match audited : auditNode table node result with
    | .error error => .error error
    | .ok _ => .ok ⟨result, ordinary, audited⟩

/-- Every checked node success has a retained ordinary execution and audit
receipt on canonical metadata. No extra node certificate is supplied. -/
theorem computeAuditedNode_checked_complete (valid : MetadataInvariant graph table)
    (checked : computeNode table node true = .ok result) :
    ∃ receipt, computeAuditedNode table node = .ok receipt ∧ receipt.result = result := by
  have ordinary := computeNode_checked_ordinary checked
  have audited := (auditNode_acceptance_iff valid ordinary).mpr checked
  unfold computeAuditedNode
  split
  next error failed => rw [ordinary] at failed; cases failed
  next actual computed =>
    have same : actual = result := Except.ok.inj (computed.symm.trans ordinary)
    subst actual
    split
    next error rejected => rw [audited] at rejected; cases rejected
    next acceptedUnit passed => exact ⟨_, rfl, rfl⟩

/-- Retained receipts establish exact checked acceptance under canonical
metadata, without rerunning the node merger. -/
theorem AuditedNode.checked (receipt : AuditedNode table node)
    (valid : MetadataInvariant graph table) : computeNode table node true = .ok receipt.result :=
  computeNode_audited_checked valid receipt.ordinary receipt.audited

/-- A consumer recovers the original graph contract from a retained result. -/
theorem AuditedNode.graphSound (receipt : AuditedNode table node)
    (valid : MetadataInvariant graph table) (found : graph.findNode? node.name = some node) :
    GraphTrace graph node.name receipt.result.precedence
      (if node.suffix then receipt.result.precedence else selectedTail table receipt.result.inheritedSuffix) :=
  computeNode_checked_graph_sound valid found (receipt.checked valid)

/-- Fresh insertion of a retained result preserves canonical graph metadata. -/
theorem AuditedNode.insertSound (receipt : AuditedNode table node)
    (valid : MetadataInvariant graph table) (found : graph.findNode? node.name = some node)
    (fresh : lookup table node.name = none) :
    MetadataInvariant graph (table.insert node.name receipt.result) :=
  computeNode_checked_insert_sound valid found fresh (receipt.checked valid)

end LeanPoo.C4.LinearizeState
