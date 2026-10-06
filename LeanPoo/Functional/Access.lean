import LeanPoo.Functional.Requirements

/-! Access a prepared capability by its typed key, so consumer code does not
encode tuple positions. Resolve the access once and retain the returned factory. -/
namespace LeanPoo.Functional.Requirements

universe u v w
variable {Context : Type u} {Key : Type v} {Value : Context → Key → Type w}

/-- Obtain the first requested factory for this key. Membership excludes a
missing key; dependent equality keeps its exact result family. This scans the
checklist, so retain the returned function before repeated context calls. -/
def factoryAt [DecidableEq Key] : {keys : List Key} →
    Factories Context Value keys → (key : Key) → key ∈ keys →
    Factory Context (fun context => Value context key)
  | [], _, _, member => False.elim (List.not_mem_nil member)
  | head :: rest, (factory, tail), key, member =>
    if same : head = key then same ▸ factory
    else factoryAt tail key (by
      rcases List.mem_cons.mp member with equal | included
      · exact False.elim (same equal.symm)
      · exact included)

/-- Named access to a successfully selected tuple returns exactly the provider's
function, including when keys are repeated or the tuple is reordered. -/
theorem factoryAt_selected [DecidableEq Key] (provider : Provider Context Key Value)
    (keys : List Key) (factories : Factories Context Value keys)
    (selected : Selected provider keys factories) (key : Key) (member : key ∈ keys) :
    provider key = some (factoryAt (keys := keys) factories key member) := by
  induction keys with
  | nil => simp at member
  | cons head rest ih =>
    rcases factories with ⟨factory, tail⟩
    rcases selected with ⟨first, remaining⟩
    by_cases same : head = key
    · subst key
      simpa [factoryAt] using first
    · simpa [factoryAt, same] using ih tail remaining
        (by simpa [List.mem_cons, Ne.symm same] using member)

/-- Named access after C4 preparation retains the exact original provider
provenance, not merely availability of some function for this key. -/
theorem factoryAt_origin [DecidableEq Key] (order : C4.VerifiedOrder graph root)
    (providers : String → Provider Context Key Value) (keys : List Key)
    (factories : Factories Context Value keys)
    (ready : prepare (assemble order providers) keys = .ok factories)
    (key : Key) (member : key ∈ keys) :
    ∃ name, C4.Ancestor graph name root ∧
      providers name key = some (factoryAt (keys := keys) factories key member) :=
  assemble_origin (factoryAt_selected _ _ _ ((prepare_ok_iff _ _ _).mp ready) key member)

/-- Two successful checklists for the same provider give identical named
factories. Adding/reordering other requested keys changes no such consumer. -/
theorem factoryAt_stable [DecidableEq Key] (provider : Provider Context Key Value)
    (left : Factories Context Value leftKeys) (right : Factories Context Value rightKeys)
    (leftReady : prepare provider leftKeys = .ok left)
    (rightReady : prepare provider rightKeys = .ok right)
    (key : Key) (leftMember : key ∈ leftKeys) (rightMember : key ∈ rightKeys) :
    factoryAt (keys := leftKeys) left key leftMember =
      factoryAt (keys := rightKeys) right key rightMember := by
  have a := factoryAt_selected provider leftKeys left ((prepare_ok_iff _ _ _).mp leftReady) key leftMember
  have b := factoryAt_selected provider rightKeys right ((prepare_ok_iff _ _ _).mp rightReady) key rightMember
  exact Option.some.inj (a.symm.trans b)

end LeanPoo.Functional.Requirements
