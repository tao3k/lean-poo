import LeanPoo.Functional.MetadataClosure
import LeanPoo.Functional.DispatchExtension

/-! Publish an immutable factory/dispatch version after checked construction,
negative extension protection and a joint consumer admission. The payload
can carry dependent prepared factories and proofs for the exact new version.
This is an explicit pure publication policy, not a global conflict protocol. -/
namespace LeanPoo.Functional.FactoryDispatchPublication
open Object DispatchExtension
variable {Context Key Args Method Result : Type} {Value : Context → Key → Type}
variable {base : FactoryRecord Context Key Value}
variable {watches : List (Watch Args)}
variable {Approved : MetadataFamily.Construction base → Multimethod Args Method Result → Type}

structure Snapshot (base : FactoryRecord Context Key Value) (watches : List (Watch Args))
    (Approved : MetadataFamily.Construction base → Multimethod Args Method Result → Type) where
  factories : MetadataFamily.Construction base
  generic : Multimethod Args Method Result
  negative : Certificate generic watches
  approval : Approved factories generic

variable {FactoryError AdmissionError : Type}

structure Revision (old : Snapshot base watches Approved)
    (rebuild : Unit → Except FactoryError (MetadataFamily.Construction base))
    (edits : List (Edit Args Method))
    (admit : (factories : MetadataFamily.Construction base) → (generic : Multimethod Args Method Result) →
      Except AdmissionError (Approved factories generic)) where
  snapshot : Snapshot base watches Approved
  rebuilt : rebuild () = .ok snapshot.factories
  applied : patch old.generic edits = .ok snapshot.generic
  admitted : admit snapshot.factories snapshot.generic = .ok snapshot.approval

inductive Failure (old : Snapshot base watches Approved) (edits : List (Edit Args Method)) where
  | construction (error : FactoryError)
  | dispatch (failure : DispatchExtension.Failure old.generic watches edits)
  | admission (factories : MetadataFamily.Construction base)
      (dispatch : DispatchExtension.Revision old.generic watches edits) (error : AdmissionError)

def stage (old : Snapshot base watches Approved)
    (rebuild : Unit → Except FactoryError (MetadataFamily.Construction base))
    (edits : List (Edit Args Method))
    (admit : (factories : MetadataFamily.Construction base) → (generic : Multimethod Args Method Result) →
      Except AdmissionError (Approved factories generic)) :
    Except (Failure (FactoryError := FactoryError) (AdmissionError := AdmissionError) old edits)
      (Revision old rebuild edits admit) :=
  match built : rebuild () with
  | .error error => .error (.construction error)
  | .ok factories => match guard old.generic watches old.negative edits with
    | .error error => .error (.dispatch error)
    | .ok dispatch => match admitted : admit factories dispatch.snapshot with
      | .error error => .error (.admission factories dispatch error)
      | .ok approval => .ok ⟨⟨factories, dispatch.snapshot, dispatch.certificate, approval⟩,
          built, dispatch.applied, admitted⟩

def publish (old : Snapshot base watches Approved)
    (rebuild : Unit → Except FactoryError (MetadataFamily.Construction base))
    (edits : List (Edit Args Method))
    (admit : (factories : MetadataFamily.Construction base) → (generic : Multimethod Args Method Result) →
      Except AdmissionError (Approved factories generic)) :=
  let outcome := stage old rebuild edits admit
  (outcome, match outcome with | .error _ => old | .ok revision => revision.snapshot)

theorem publish_refused (old : Snapshot base watches Approved) (rebuild edits admit)
    (error : Failure (FactoryError := FactoryError) (AdmissionError := AdmissionError) old edits)
    (refused : stage old rebuild edits admit = .error error) :
    (publish old rebuild edits admit).2 = old := by simp [publish, refused]

theorem publish_accepted (old : Snapshot base watches Approved) (rebuild edits admit)
    (revision : Revision (FactoryError := FactoryError) (AdmissionError := AdmissionError) old rebuild edits admit)
    (accepted : stage old rebuild edits admit = .ok revision) :
    (publish old rebuild edits admit).2 = revision.snapshot := by simp [publish, accepted]

theorem Revision.cacheSound (revision : Revision old rebuild edits admit) (sound : old.generic.CacheSound) :
    revision.snapshot.generic.CacheSound := patch_sound _ _ _ sound revision.applied

theorem stage_construction_error (old : Snapshot base watches Approved) (rebuild edits admit)
    (error : FactoryError) (failed : rebuild () = .error error) :
    stage (AdmissionError := AdmissionError) old rebuild edits admit = .error (.construction error) := by
  unfold stage
  split <;> simp_all

theorem Snapshot.closed (snapshot : Snapshot base watches Approved) (key : Key) :
    snapshot.factories.family.production.lookup key = snapshot.factories.family.provider key :=
  snapshot.factories.family.production_lookup key

end LeanPoo.Functional.FactoryDispatchPublication
