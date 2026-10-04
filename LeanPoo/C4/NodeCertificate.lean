import LeanPoo.C4.Suffix

namespace LeanPoo.C4

/-- A selected inherited tail comes from the supplied parent tails (or is
empty when none are supplied) and containsTail every one as a literal suffix. -/
structure TailCertified (tails : List (List String)) where
  output : List String
  chosen : (tails = [] ∧ output = []) ∨ output ∈ tails
  containsTail : ∀ tail ∈ tails, tail.IsSuffix output

theorem TailCertified.longest (certificate : TailCertified tails)
    (member : tail ∈ tails) : tail.length ≤ certificate.output.length :=
  (certificate.containsTail tail member).length_le

theorem TailCertified.comparable (certificate : TailCertified tails)
    (first : left ∈ tails) (second : right ∈ tails) :
    left.IsSuffix right ∨ right.IsSuffix left :=
  List.suffix_or_suffix_of_suffix (certificate.containsTail left first)
    (certificate.containsTail right second)

theorem TailCertified.unique (first second : TailCertified tails) :
    first.output = second.output := by
  rcases first.chosen with ⟨empty, same⟩ | member
  · rcases second.chosen with ⟨_, other⟩ | impossible
    · exact same.trans other.symm
    · simp [empty] at impossible
  · rcases second.chosen with ⟨empty, _⟩ | other
    · simp [empty] at member
    · exact (second.containsTail first.output member).eq_of_length_le
        (first.containsTail second.output other).length_le

/-- Independently check a traversal's claimed choice; no suffix-chain cache
or name-level reachability decision is trusted by this checker. -/
def certifyTail (tails : List (List String)) (claimed : List String) :
    Except Error (TailCertified tails) :=
  if chosen : (tails = [] ∧ claimed = []) ∨ claimed ∈ tails then
    if containsTail : ∀ tail ∈ tails, tail.IsSuffix claimed then
      .ok ⟨claimed, chosen, containsTail⟩
    else .error .incompatibleSuffixes
  else .error .incompatibleSuffixes

theorem certifyTail_complete (certificate : TailCertified tails) :
    certifyTail tails certificate.output = .ok certificate := by
  simp only [certifyTail, dite_eq_left certificate.chosen, dite_eq_left certificate.containsTail]

/-- Evidence for one complete node, binding the selected tail, reconstructed
ancestry, and fresh node name to the returned precedence. -/
structure NodeCertified (name : String) (orders tails : List (List String)) where
  selection : TailCertified tails
  ancestry : SuffixCertified orders selection.output
  tailUnique : selection.output.Nodup
  fresh : name ∉ ancestry.output

def NodeCertified.output (certificate : NodeCertified name orders tails) : List String :=
  name :: certificate.ancestry.output

theorem NodeCertified.preserves (certificate : NodeCertified name orders tails)
    (member : order ∈ orders) : order.Sublist certificate.output :=
  (certificate.ancestry.preserves member).cons name

theorem NodeCertified.inherited_suffix (certificate : NodeCertified name orders tails) :
    certificate.selection.output.IsSuffix certificate.output :=
  certificate.ancestry.suffix.trans (List.suffix_cons name _)

theorem NodeCertified.parent_suffix (certificate : NodeCertified name orders tails)
    (member : tail ∈ tails) : tail.IsSuffix certificate.output :=
  (certificate.selection.containsTail tail member).trans
    certificate.inherited_suffix

theorem NodeCertified.nodup (certificate : NodeCertified name orders tails) :
    certificate.output.Nodup :=
  List.nodup_cons.mpr ⟨certificate.fresh, certificate.ancestry.nodup certificate.tailUnique⟩

theorem NodeCertified.head (certificate : NodeCertified name orders tails) :
    certificate.output.head? = some name := rfl

theorem NodeCertified.covers (certificate : NodeCertified name orders tails) :
    item ∈ certificate.output ↔ item = name ∨
      (∃ order ∈ orders, item ∈ order) ∨ item ∈ certificate.selection.output := by
  simp only [output, List.mem_cons, certificate.ancestry.covers]

private def certifyNodeUsing
    (merger : (orders : List (List String)) → (tail : List String) → Except Error (SuffixCertified orders tail))
    (name : String) (orders tails : List (List String)) (claimedTail : List String) :
    Except Error (NodeCertified name orders tails) := do
  let selection ← certifyTail tails claimedTail
  let ancestry ← merger orders selection.output
  if unique : selection.output.Nodup then
    if fresh : name ∉ ancestry.output then
      return ⟨selection, ancestry, unique, fresh⟩
    else throw (.cycle name)
  else throw .inconsistentOrder

def certifyNode (name : String) (orders tails : List (List String)) (claimedTail : List String) :
    Except Error (NodeCertified name orders tails) :=
  certifyNodeUsing mergeWithSuffixCertified name orders tails claimedTail

def certifyNodeReference (name : String) (orders tails : List (List String)) (claimedTail : List String) :
    Except Error (NodeCertified name orders tails) :=
  certifyNodeUsing mergeWithSuffixReference name orders tails claimedTail

/-- Reference reconstruction reproduces every well-formed node certificate. -/
theorem certifyNodeReference_complete (certificate : NodeCertified name orders tails) :
    ∃ result, certifyNodeReference name orders tails certificate.selection.output = .ok result ∧
      result.output = certificate.output ∧ result.selection.output = certificate.selection.output := by
  obtain ⟨ancestry, success, same⟩ :=
    mergeWithSuffixReference_complete certificate.ancestry certificate.tailUnique
  have fresh : name ∉ ancestry.output := by rw [same]; exact certificate.fresh
  refine ⟨⟨certificate.selection, ancestry, certificate.tailUnique, fresh⟩, ?_, ?_, rfl⟩
  · simp [certifyNodeReference, certifyNodeUsing, certifyTail_complete certificate.selection,
      success, certificate.tailUnique, fresh, bind, Except.bind, pure, Except.pure]
  · simp [NodeCertified.output, same]

/-- The runtime node checker reproduces every well-formed node certificate. -/
theorem certifyNode_complete (certificate : NodeCertified name orders tails) :
    ∃ result, certifyNode name orders tails certificate.selection.output = .ok result ∧
      result.output = certificate.output ∧ result.selection.output = certificate.selection.output := by
  obtain ⟨ancestry, success, same⟩ :=
    mergeWithSuffixCertified_complete certificate.ancestry certificate.tailUnique
  have fresh : name ∉ ancestry.output := by rw [same]; exact certificate.fresh
  refine ⟨⟨certificate.selection, ancestry, certificate.tailUnique, fresh⟩, ?_, ?_, rfl⟩
  · simp [certifyNode, certifyNodeUsing, certifyTail_complete certificate.selection,
      success, certificate.tailUnique, fresh, bind, Except.bind, pure, Except.pure]
  · simp [NodeCertified.output, same]

/-- The checker result retains the exact claimed inherited tail. -/
theorem certifyNode_claimed (success : certifyNode name orders tails claimed = .ok certificate) :
    certificate.selection.output = claimed := by
  unfold certifyNode certifyNodeUsing at success
  cases selected : certifyTail tails claimed with
  | error error => simp [selected, bind, Except.bind] at success
  | ok selection =>
    have same : selection.output = claimed := by
      unfold certifyTail at selected
      split at selected
      · split at selected
        · have equal := Except.ok.inj selected
          rw [← equal]
        · simp_all
      · simp_all
    cases merged : mergeWithSuffixCertified orders selection.output with
    | error error => simp [selected, merged, bind, Except.bind] at success
    | ok ancestry =>
      simp only [selected, merged, bind, Except.bind] at success
      split at success
      · split at success
        · simp only [pure, Except.pure, Except.ok.injEq] at success
          rw [← success]; exact same
        · simp_all
      · simp_all

end LeanPoo.C4
