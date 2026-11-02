import LeanPoo.Prototype.GeneralizedPrototype
import LeanPoo.Functional.NonlocalDeclarations

/-! Appendix B lens/wrapper fragments with heterogeneous method/focus types,
common declaration elaboration and an arbitrary raw/cooked representation. This
advances future work; total pure callbacks and lens laws are separate premises. -/
namespace LeanPoo.Prototype.Generalized
universe u
/-- The two existential types allow each fragment to focus a different component
and carry different source data without a closed sum/tag interpreter. -/
structure Fragment (Raw Cooked : Type) where
  Focus : Type
  Method : Type
  focus : MonoLens Raw Focus
  wrap : Method → Thunk Cooked → Thunk Focus → Focus
  method : Method
/-- Compile using the existing Appendix B lens construction, not a new evaluator. -/
def Fragment.compile (fragment : Fragment Raw Cooked) : DelayedProto Cooked Raw Raw :=
  lensCompiler fragment.focus fragment.wrap fragment.method
/-- Any raw/cooked carrier uses the same independently extensible fragment stream. -/
def fragmentProtocol (cook : Raw → Cooked) : Protocol Raw Cooked (Fragment Raw Cooked) :=
  ⟨cook, Fragment.compile⟩
/-- Exact $lens-gen semantics preserve the original inherited raw carrier. -/
theorem Fragment.compile_eq (fragment : Fragment Raw Cooked) (self : Thunk Cooked) (parent : Thunk Raw) :
    fragment.compile self parent = fragment.focus.modify
      (fun _ => fragment.wrap fragment.method self (Thunk.mk fun _ => fragment.focus.view parent.get)) parent.get := rfl
/-- A lens-preserved frame remains unchanged by every admitted fragment. -/
theorem Fragment.compile_frame (fragment : Fragment Raw Cooked) (frame : Raw → Frame)
    (law : ∀ raw value, frame (fragment.focus.modify (fun _ => value) raw) = frame raw)
    (self : Thunk Cooked) (parent : Thunk Raw) :
    frame (fragment.compile self parent) = frame parent.get :=
  lensCompiler_frame fragment.focus fragment.wrap frame (fun value raw => law raw value) fragment.method self parent
/-- A frame law is needed only for the actual admitted descriptors, not for all
possible lenses. Ordered composition preserves that same independent raw frame. -/
theorem fragments_frame (parts : List (Fragment Raw Cooked)) (cook : Raw → Cooked) (frame : Raw → Frame)
    (law : ∀ part ∈ parts, ∀ raw value, frame (part.focus.modify (fun _ => value) raw) = frame raw)
    (self : Thunk Cooked) (parent : Thunk Raw) :
    frame ((fragmentProtocol cook).assemble parts self parent) = frame parent.get := by
  induction parts with
  | nil => rfl
  | cons head rest ih =>
    change frame (head.compile self (Thunk.mk fun _ => (fragmentProtocol cook).assemble rest self parent)) = _
    rw [head.compile_frame frame (law head (by simp))]
    exact ih (fun part member => law part (by simp [member]))
/-- Named expanded entries carry heterogeneous typed fragment descriptors. -/
abbrev FragmentEntry (Raw Cooked : Type) := String × Fragment Raw Cooked
/-- Successful complete elaboration retains both source order and label validity. -/
structure FragmentDeclaration (Raw Cooked : Type) where
  entries : List (FragmentEntry Raw Cooked)
  unique : (entries.map Prod.fst).Nodup
/-- Record and generalized consumers reuse the SAME Reader expansion function. -/
def elaborateFragments {Context : Type u} (forms : List (Context → Except String (List (FragmentEntry Raw Cooked))))
    (context : Context) (finalize : Context → List (FragmentEntry Raw Cooked) →
      Except String (List (FragmentEntry Raw Cooked))) : Except String (FragmentDeclaration Raw Cooked) := do
  let expanded ← Functional.DeclarativeMetadata.expandForms forms context
  let entries ← finalize context expanded
  if valid : (entries.map Prod.fst).Nodup then return ⟨entries,valid⟩
  else throw "duplicate generalized fragment label"
/-- A publication originates from full source expansion and finalization at this
same context. Native shape checks correspond to the descriptor's typed fields. -/
theorem elaborateFragments_source {Context : Type u} (forms : List (Context → Except String (List (FragmentEntry Raw Cooked))))
    (context : Context) (finalize) (result : FragmentDeclaration Raw Cooked)
    (accepted : elaborateFragments forms context finalize = .ok result) :
    ∃ expanded, Functional.DeclarativeMetadata.expandForms forms context = .ok expanded ∧
      finalize context expanded = .ok result.entries := by
  cases expanded : Functional.DeclarativeMetadata.expandForms forms context with
  | error message => simp [elaborateFragments, expanded, bind, Except.bind] at accepted
  | ok front =>
    cases finalized : finalize context front with
    | error message => simp [elaborateFragments, expanded, finalized, bind, Except.bind] at accepted
    | ok entries =>
      by_cases valid : (entries.map Prod.fst).Nodup
      · simp [elaborateFragments, expanded, finalized, valid, bind, Except.bind, pure, Except.pure] at accepted
        subst result
        exact ⟨front,rfl,finalized⟩
      · simp [elaborateFragments, expanded, finalized, valid, bind, Except.bind, throw, throwThe] at accepted
/-- Labels are reflection metadata; only descriptor order enters compilation. -/
def FragmentDeclaration.observe (declaration : FragmentDeclaration Raw Cooked) (cook : Raw → Cooked)
    (base seed : Raw) (depth : Nat) : Cooked :=
  (fragmentProtocol cook).observe (declaration.entries.map Prod.snd) base seed depth
/-- Finite observation always uses the exact admitted full descriptor stream. -/
theorem FragmentDeclaration.observe_eq (declaration : FragmentDeclaration Raw Cooked) (cook : Raw → Cooked)
    (base seed : Raw) (depth : Nat) : declaration.observe cook base seed depth =
    (fragmentProtocol cook).observe (declaration.entries.map Prod.snd) base seed depth := rfl
end LeanPoo.Prototype.Generalized
