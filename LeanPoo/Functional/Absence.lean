import LeanPoo.Functional.Requirements

/-! Explicit negative capability assumptions. Checking availability retains
functions without invoking them, including on proof-bearing refusal paths. -/
namespace LeanPoo.Functional.Requirements

universe u v w
variable {Context : Type u} {Key : Type v} {Value : Context → Key → Type w}
variable {provider : Provider Context Key Value} {keys : List Key}

/-- All listed capabilities are absent from this exact provider snapshot. -/
def Absent (provider : Provider Context Key Value) (keys : List Key) : Prop :=
  ∀ key ∈ keys, provider key = none

structure AbsenceCertificate (provider : Provider Context Key Value) (keys : List Key) : Type where
  absent : Absent provider keys

/-- The first present capability in caller order, with its actual factory.
Earlier keys are absent; repeated keys and heterogeneous results are retained. -/
structure Presence (provider : Provider Context Key Value) (keys : List Key) where
  key : Key
  earlier : List Key
  later : List Key
  split : keys = earlier ++ key :: later
  prior : Absent provider earlier
  factory : Factory Context (fun context => Value context key)
  selected : provider key = some factory

theorem Presence.requested (failure : Presence provider keys) : failure.key ∈ keys := by
  exact Eq.mpr (congrArg (fun list : List Key => failure.key ∈ list) failure.split) (by simp)

theorem Presence.refutes (failure : Presence provider keys) : ¬ Absent provider keys := by
  intro absent
  have impossible := (absent failure.key failure.requested).symm.trans failure.selected
  contradiction

/-- Inspect only provider availability. No context or factory body is evaluated. -/
def checkAbsent (provider : Provider Context Key Value) : (keys : List Key) →
    Except (Presence provider keys) (AbsenceCertificate provider keys)
  | [] => .ok ⟨by intro key member; simp at member⟩
  | key :: rest =>
    match found : provider key with
    | some factory => .error {
        key, earlier := [], later := rest, split := rfl
        prior := by intro query member; simp at member
        factory, selected := found }
    | none =>
      match checkAbsent provider rest with
      | .ok certificate => .ok ⟨by
          intro query member
          rcases List.mem_cons.mp member with same | member
          · subst query; exact found
          · exact certificate.absent query member⟩
      | .error conflict => .error {
          key := conflict.key, earlier := key :: conflict.earlier, later := conflict.later
          split := congrArg (List.cons key) conflict.split
          prior := by
            intro query member
            rcases List.mem_cons.mp member with same | member
            · subst query; exact found
            · exact conflict.prior query member
          factory := conflict.factory, selected := conflict.selected }

/-- Complete negative admission, independent of function equality or execution. -/
theorem checkAbsent_ok_iff (provider : Provider Context Key Value) (keys : List Key) :
    (∃ certificate, checkAbsent provider keys = .ok certificate) ↔ Absent provider keys := by
  constructor
  · rintro ⟨certificate, _⟩; exact certificate.absent
  · intro absent
    cases checked : checkAbsent provider keys with
    | ok certificate => exact ⟨certificate, rfl⟩
    | error failure => exact False.elim (failure.refutes absent)

theorem checkAbsent_error_iff (provider : Provider Context Key Value) (keys : List Key) :
    (∃ failure, checkAbsent provider keys = .error failure) ↔ ¬ Absent provider keys := by
  constructor
  · rintro ⟨failure, _⟩; exact failure.refutes
  · intro present
    cases checked : checkAbsent provider keys with
    | error failure => exact ⟨failure, rfl⟩
    | ok certificate => exact False.elim (present certificate.absent)

/-- Reuse the negative assumption only under exact requested-key agreement. -/
def AbsenceCertificate.rebind (certificate : AbsenceCertificate provider keys)
    (other : Provider Context Key Value)
    (same : ∀ key ∈ keys, other key = provider key) : AbsenceCertificate other keys :=
  ⟨fun key member => (same key member).trans (certificate.absent key member)⟩

/-- A conflicting assembled factory originates at an actual graph ancestor. -/
theorem Presence.origin (order : C4.VerifiedOrder graph root)
    (providers : String → Provider Context Key Value)
    (failure : Presence (assemble order providers) keys) :
    ∃ name, C4.Ancestor graph name root ∧ providers name failure.key = some failure.factory :=
  assemble_origin failure.selected

end LeanPoo.Functional.Requirements
