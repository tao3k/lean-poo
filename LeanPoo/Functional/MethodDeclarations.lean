import LeanPoo.Object.MethodCombinationSemantics

/-! Record and qualified method declarations share one fragment stream. This
models source-order collection, inherited assembly and receiver-generic invocation;
Gerbil syntax expansion, policy admission and mutable invalidation have controls. -/
namespace LeanPoo.Object.MethodCombination
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
