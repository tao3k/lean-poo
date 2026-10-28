import LeanPoo.Prototype.RepresentationIndex
import LeanPoo.Prototype.RepresentationNames

/-! Effective declaration indexes and guarded visibility preparation.
String keys injectively denote Symbol identities. Private persistent storage,
standard first-entry indexed lookup, registered descriptor/source edges and serial
supported edits are host premises. No physical heap, RBTree balancing, arbitrary
callback purity/termination or machine-time theorem is asserted here. -/
namespace LeanPoo.Prototype.Representation

/-- Keep the first C3 declaration of each name, even when that descriptor is hidden. -/
def selectDeclarations (entries : List (String × Value)) (seen : List String := []) : List (String × Value) :=
  match entries with
  | [] => []
  | entry :: tail => if entry.1 ∈ seen then selectDeclarations tail seen
      else entry :: selectDeclarations tail (entry.1 :: seen)

/-- First-occurrence selection preserves the actual descriptor, including false/functions. -/
theorem first_selectDeclarations (entries : List (String × Value)) (seen : List String)
    (name : String) (fresh : name ∉ seen) :
    first (selectDeclarations entries seen) name = first entries name := by
  induction entries generalizing seen with
  | nil => rfl
  | cons entry tail ih =>
    rcases entry with ⟨key, value⟩
    by_cases present : key ∈ seen
    · have different : key ≠ name := fun same => fresh (same ▸ present)
      simp [selectDeclarations, first, present, different, ih seen fresh]
    · by_cases same : key = name
      · subst key; simp [selectDeclarations, first, fresh]
      · have next : name ∉ key :: seen := by simp [Ne.symm same, fresh]
        simp [selectDeclarations, first, present, same, ih (key :: seen) next]

/-- Seen names never reappear, so a hidden override cannot expose its ancestor. -/
theorem selectDeclarations_excludes (entries : List (String × Value)) (seen : List String)
    (name : String) (present : name ∈ seen) :
    ∀ entry ∈ selectDeclarations entries seen, entry.1 ≠ name := by
  induction entries generalizing seen with
  | nil => simp [selectDeclarations]
  | cons head tail ih =>
    by_cases known : head.1 ∈ seen
    · simpa [selectDeclarations, known] using ih seen present
    · simp only [selectDeclarations, known, ↓reduceIte, List.mem_cons]
      intro entry member
      rcases member with same | rest
      · subst entry; exact fun same => known (same.symm ▸ present)
      · exact ih (head.1 :: seen) (by simp [present]) entry rest

/-- Gerbil foldr checks the rightmost visibility first. Refusal stops before any
remaining earlier descriptor, and returns no partially visible public directory. -/
def checkVisibility (hidden : Value → Except E Bool) :
    List (String × Value) → Except E (List (String × Value))
  | [] => .ok []
  | head :: tail => match checkVisibility hidden tail with
    | .error cause => .error cause
    | .ok rest => match hidden head.2 with
      | .error cause => .error cause
      | .ok true => .ok rest
      | .ok false => .ok (head :: rest)

/-- A right-hand refusal has precedence over the earlier descriptor's callback. -/
theorem checkVisibility_tail_refused (hidden : Value → Except E Bool)
    (head : String × Value) (tail : List (String × Value)) (cause : E)
    (refused : checkVisibility hidden tail = .error cause) :
    checkVisibility hidden (head :: tail) = .error cause := by simp [checkVisibility, refused]

/-- Exact descriptor refusal survives even after successful private tail preparation. -/
theorem checkVisibility_head_refused (hidden : Value → Except E Bool)
    (head : String × Value) (tail rest : List (String × Value)) (cause : E)
    (ready : checkVisibility hidden tail = .ok rest) (refused : hidden head.2 = .error cause) :
    checkVisibility hidden (head :: tail) = .error cause := by simp [checkVisibility, ready, refused]

/-- Observers always execute the current ordered visibility preparation. Only an
unobserved query may reuse a successful private directory of the current revision. -/
def chooseVisible (observed : Bool) (cached : Option (List (String × Value)))
    (prepare : Unit → Except E (List (String × Value))) : Except E (List (String × Value)) :=
  if observed then prepare () else match cached with
    | some entries => .ok entries
    | none => prepare ()

/-- A warm cache never suppresses observed reads, callbacks, dependencies or refusal. -/
theorem chooseVisible_observed (cached : Option (List (String × Value)))
    (prepare : Unit → Except E (List (String × Value))) :
    chooseVisible true cached prepare = prepare () := rfl

/-- Cache fidelity is an explicit source/invalidation premise, never inferred
from a prior successful Type check. Under it, both routes observe the same directory. -/
theorem chooseVisible_faithful (observed : Bool) (cached : Option (List (String × Value)))
    (prepare : Unit → Except E (List (String × Value)))
    (faithful : ∀ saved, cached = some saved → prepare () = .ok saved) :
    chooseVisible observed cached prepare = prepare () := by
  cases observed with
  | true => rfl
  | false =>
    cases cached with
    | none => rfl
    | some saved => simpa [chooseVisible] using (faithful saved rfl).symm

/-- An empty private directory is a successful cache value, distinct from no cache. -/
theorem chooseVisible_empty (prepare : Unit → Except E (List (String × Value))) :
    chooseVisible false (some []) prepare = .ok [] := rfl

/-- The post-callback fence runs after descriptor preparation, before publication.
Its source revision is also bound into the existing owner-names observation. -/
def finishVisibility (before after : Nat) (prepared : Except String (List (String × Value))) :
    Except String (List (String × Value)) :=
  match prepared with
  | .error cause => .error cause
  | .ok entries => if before = after then .ok entries else .error "object changed during declaration reflection"

/-- Original getter refusal has precedence over the post-callback revision fence. -/
theorem finishVisibility_refused (before after : Nat) (cause : String) :
    finishVisibility before after (.error cause : Except String (List (String × Value))) = .error cause := rfl

/-- A revision change cannot publish even a completely prepared public directory. -/
theorem finishVisibility_stale (before after : Nat) (entries : List (String × Value))
    (changed : before ≠ after) :
    finishVisibility before after (.ok entries) = .error "object changed during declaration reflection" := by
  simp [finishVisibility, changed]

/-- A fresh retry with stable current sources preserves the complete prepared directory. -/
theorem finishVisibility_retry (current : Nat) (entries : List (String × Value)) :
    finishVisibility current current (.ok entries) = .ok entries := by simp [finishVisibility]

/-- Logical work for a successfully selected public field; missing/metadata refusal
stops before value admission. Construction/capture, standard tree probes, concrete
value demand/check, owned exports, observers and GC are separate real costs. -/
structure DeclarationWork where
  merges : Nat
  visibilityPasses : Nat
  valueChecks : Nat
  deriving DecidableEq, Repr

/-- Membership and visibility have independent cold state; value admission is per call. -/
def declarationWork (observed fullReady visibleReady : Bool) : DeclarationWork :=
  ⟨if fullReady then 0 else 1, if observed || !visibleReady then 1 else 0, 1⟩

/-- A warm unobserved point query removes preparation, never the concrete Type check. -/
theorem declarationWork_warm : declarationWork false true true = ⟨0, 0, 1⟩ := rfl

/-- Observation still pays visibility preparation; cold queries pay both preparations. -/
theorem declarationWork_observed_cold :
    declarationWork true true true = ⟨0, 1, 1⟩ ∧
    declarationWork false false false = ⟨1, 1, 1⟩ := ⟨rfl, rfl⟩

end LeanPoo.Prototype.Representation
