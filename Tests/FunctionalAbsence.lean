import LeanPoo.Functional.GuardedExtension

namespace LeanPoo.Tests.FunctionalAbsence
open Functional Functional.Requirements

universe u v w
example {Context : Type u} {Key : Type v} {Value : Context → Key → Type w}
    (provider : Provider Context Key Value) (keys : List Key) :
    (∃ certificate, checkAbsent provider keys = .ok certificate) ↔
      ∀ key ∈ keys, provider key = none := checkAbsent_ok_iff provider keys

example {Context : Type u} {Key : Type v} [DecidableEq Key]
    {Value : Context → Key → Type w} (index : C4.AncestryIndex graph root)
    (registry : ProviderRegistry Context Key Value) (keys : List Key)
    (_old : AbsenceCertificate (assemble index.order registry.dictionary) keys)
    (edits : List (RegistryEdit Context Key Value))
    (revision : AbsenceRevision index registry keys edits) :
    ∀ key ∈ keys, assemble index.order revision.snapshot.dictionary key = none :=
  revision.certificate.absent

example {Context : Type u} {Key : Type v} {Value : Context → Key → Type w}
    (provider : Provider Context Key Value) (keys : List Key) (conflict : Presence provider keys) :
    keys = conflict.earlier ++ conflict.key :: conflict.later ∧
      (∀ key ∈ conflict.earlier, provider key = none) ∧
      provider conflict.key = some conflict.factory :=
  ⟨conflict.split, conflict.prior, conflict.selected⟩

private inductive Key where
  | quantity | flag | proof | unforced
  deriving BEq, DecidableEq

private def Value (context : Nat) : Key → Type
  | .quantity => {n : Nat // context ≤ n}
  | .flag => Bool
  | .proof => PLift (context ≤ context + 1)
  | .unforced => Nat

/-- This factory cannot finish if the availability checker invokes it. -/
private partial def neverFinish (context : Nat) : Nat := neverFinish context

private def factory (name : String) : (key : Key) → Factory Nat (fun c => Value c key)
  | .quantity => fun c => ⟨c + name.length, by omega⟩
  | .flag => fun c => c % 2 == 0
  | .proof => Factory.fromProof (fun _ => by omega)
  | .unforced => neverFinish

private def providers (mask : Nat) (name : String) : Provider Nat Key Value :=
  fun key => if name == "A" && mask / (match key with
      | .quantity => 1 | .flag => 2 | .proof => 4 | .unforced => 8) % 2 == 1 then
    some (factory name key) else none

private abbrev Step := String × Key × Bool
private def changes (steps : List Step) : List (RegistryEdit Nat Key Value) :=
  steps.map fun (name, key, add) =>
    (name, [⟨key, if add then some (factory name key) else none⟩])

private def oracle (mask : Nat) (names : List String) (steps : List Step) (keys : List Key) :
    Except String (Option Key) := do
  for (name, _, _) in steps do
    if !(["Root", "A", "B", "Outside"].contains name) then throw name
  return keys.find? fun key => names.any fun name =>
    steps.foldl (fun present step => if step.1 == name && step.2.1 == key then step.2.2 else present)
      ((providers mask name key).isSome)

private def observe {index : C4.AncestryIndex graph root}
    {registry : ProviderRegistry Nat Key Value} {keys : List Key}
    {edits : List (RegistryEdit Nat Key Value)}
    (result : Except (AbsenceExtensionFailure index registry keys edits)
    (AbsenceRevision index registry keys edits)) : Except String (Option Key) :=
  match result with
  | .ok _ => .ok none
  | .error (.unknownProvider name _) => .error name
  | .error (.introduced _ _ conflict) => .ok (some conflict.key)

private def sameOutcome : Except String (Option Key) → Except String (Option Key) → Bool
  | .ok left, .ok right => left == right
  | .error left, .error right => left == right
  | _, _ => false

#eval do
  IO.println "FUNCTIONAL-ABSENCE-START"
  let graph : C4.Graph := {nodes := [{name := "Root", parentOrders := [["A", "B"]]},
    {name := "A"}, {name := "B"}, {name := "Outside"}]}
  let .ok order := C4.linearizeVerified graph "Root" | throw (IO.userError "graph rejected")
  let index := order.indexAncestors
  let watches : List (List Key) := [[], [.quantity], [.flag], [.proof], [.unforced],
    [.quantity, .flag], [.flag, .quantity, .flag], [.quantity, .flag, .proof, .unforced]]
  let plans : List (List Step) := [[], [("A", .flag, true)], [("B", .quantity, true)],
    [("A", .quantity, true), ("B", .flag, true)], [("A", .flag, false)],
    [("A", .flag, true), ("A", .flag, false)], [("Outside", .quantity, true)],
    [("A", .unforced, true)], [("A", .proof, true)],
    [("A", .flag, true), ("Missing", .quantity, true), ("LaterMissing", .proof, true)]]
  let mut cases := 0
  for mask in List.range 16 do
    let registry := ProviderRegistry.ofGraph graph (providers mask)
    for keys in watches do
      match checkAbsent (assemble order registry.dictionary) keys with
      | .error conflict =>
        unless (keys.find? (fun key => order.output.any fun name => (providers mask name key).isSome)) ==
            some conflict.key do throw (IO.userError "first-present admission mismatch")
        let _actualOrigin := conflict.origin order registry.dictionary
      | .ok certificate =>
        for steps in plans do
          let edits := changes steps
          let result := guardAbsenceTransaction index registry keys certificate edits
          unless sameOutcome (observe result) (oracle mask order.output steps keys) do
            throw (IO.userError "guarded extension disagrees with independent state oracle")
          match result with
          | .ok revision =>
            for key in keys do
              unless (assemble order revision.snapshot.dictionary key).isNone do
                throw (IO.userError "accepted stale absence")
          | .error (.introduced candidate _ conflict) =>
            let _firstProof := conflict.prior
            let _sourceProof := absenceConflict_origin index candidate conflict
            unless (assemble order candidate.dictionary conflict.key).isSome do
              throw (IO.userError "conflict lacks actual selected method")
          | .error (.unknownProvider _ _) => pure ()
          -- A failed or accepted pure revision leaves the old assumption usable.
          for key in keys do
            unless (assemble order registry.dictionary key).isNone do
              throw (IO.userError "old registry changed")
          cases := cases + 1
  -- The first ordinary missing key remains missing while a later one appears.
  let registry := ProviderRegistry.ofGraph graph (providers 0)
  let keys := [Key.quantity, .flag]
  let .ok certificate := checkAbsent (assemble order registry.dictionary) keys |
    throw (IO.userError "empty registry rejected")
  let edits := changes [("A", .flag, true)]
  let .error (.introduced candidate applied conflict) :=
    guardAbsenceTransaction index registry keys certificate edits |
    throw (IO.userError "later introduced method was hidden by first missing key")
  unless conflict.key == Key.flag && conflict.earlier == [Key.quantity] do
    throw (IO.userError "first conflicting order incorrect")
  unless (match prepare (assemble order candidate.dictionary) keys with
    | .error missing => missing == Key.quantity | .ok _ => false) do
    throw (IO.userError "ordinary first-error control unexpectedly succeeded")
  let _candidateProof := applied
  -- Presence of the divergent factory is diagnosed without evaluating it.
  let .ok unforced := checkAbsent (assemble order registry.dictionary) [.unforced] |
    throw (IO.userError "cold absence rejected")
  unless sameOutcome (observe (guardAbsenceTransaction index registry [.unforced] unforced
      (changes [("B", .unforced, true)]))) (.ok (some .unforced)) do
    throw (IO.userError "unforced conflict not diagnosed")
  IO.println s!"FUNCTIONAL-ABSENCE-OK cases={cases}"

#print axioms LeanPoo.Functional.Requirements.checkAbsent_ok_iff
#print axioms LeanPoo.Functional.Requirements.checkAbsent_error_iff
#print axioms LeanPoo.Functional.assemble_transaction_stable
#print axioms LeanPoo.Functional.guardAbsenceTransaction_ok_iff
#print axioms LeanPoo.Functional.absenceConflict_origin

end LeanPoo.Tests.FunctionalAbsence
