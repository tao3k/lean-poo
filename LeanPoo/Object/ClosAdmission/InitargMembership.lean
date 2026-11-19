-- SPDX-License-Identifier: Apache-2.0 AND LGPL-2.1-or-later
import Std

namespace LeanPoo.Object.ClosAdmission.InitargMembership

/-- The scan starts after declaration reads and allowance selection.
The tail may have changed during those reads. On a bad spine we retain
the original failure boundary instead of skipping the whole scan. -/
inductive Tail (Key : Type) where
  | done
  | bad
  | entry (key : Key) (rest : Tail Key)

inductive Result (Key : Type) where
  | accepted
  | invalid (key : Key)
  | malformed
  deriving DecidableEq

def firstInvalid (exempt contains : Key → Bool) : Tail Key → Result Key
  | .done => .accepted
  | .bad => .malformed
  | .entry key rest =>
    if exempt key || contains key then firstInvalid exempt contains rest
    else .invalid key

def indexedContains [BEq Key] (keys : List Key) (key : Key) : Bool :=
  keys.contains key

def optionalContains [BEq Key] (keys : List Key) : Key → Bool :=
  match keys with
  | [] => fun _ => false
  | _ :: _ => indexedContains keys

theorem same_membership [BEq Key] (keys : List Key) :
    optionalContains keys = indexedContains keys := by
  cases keys <;> rfl

theorem same_first_invalid [BEq Key] (keys : List Key)
    (exempt : Key → Bool) (tail : Tail Key) :
    firstInvalid exempt (optionalContains keys) tail =
      firstInvalid exempt (indexedContains keys) tail := by
  rw [same_membership]

def admit (allowOther : Bool) : Result Key → Result Key
  | .invalid key => if allowOther then .accepted else .invalid key
  | result => result

theorem same_final_admission [BEq Key] (keys : List Key) (exempt : Key → Bool)
    (tail : Tail Key) (allowOther : Bool) :
    admit allowOther (firstInvalid exempt (optionalContains keys) tail) =
      admit allowOther (firstInvalid exempt (indexedContains keys) tail) := by
  rw [same_first_invalid]

theorem allowance_does_not_hide_bad_spine (exempt : Key → Bool) (key : Key)
    (isControl : exempt key = true) :
    admit true (firstInvalid exempt (fun _ => false) (.entry key .bad)) =
      .malformed := by
  simp [firstInvalid, isControl, admit]

/-- The ordinary indexed path is still taken for every nonempty domain. -/
def indexBuilds (keys : List Key) : Nat :=
  if keys.isEmpty then 0 else 1

theorem empty_domain_builds_no_index : indexBuilds ([] : List Key) = 0 := rfl

theorem nonempty_domain_builds_one_index (key : Key) (rest : List Key) :
    indexBuilds (key :: rest) = 1 := rfl

end LeanPoo.Object.ClosAdmission.InitargMembership
