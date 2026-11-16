-- SPDX-License-Identifier: Apache-2.0 AND LGPL-2.1-or-later
import Std

namespace LeanPoo.Object.ClosQualifiers

/-- Symbol 0 is the Scheme shorthand for an unqualified primary method.
An explicit list containing 0 is a distinct long-form qualifier. -/
inductive Spelling where
  | symbol : Nat → Spelling
  | listed : List Nat → Spelling
  deriving DecidableEq

def meaning : Spelling → List Nat
  | .symbol name => if name = 0 then [] else [name]
  | .listed names => names

def canonical : List Nat → Spelling
  | [] => .symbol 0
  | [name] => if name = 0 then .listed [0] else .symbol name
  | names => .listed names

def normalize (spelling : Spelling) : Spelling := canonical (meaning spelling)

theorem meaning_canonical (names : List Nat) : meaning (canonical names) = names := by
  cases names with
  | nil => rfl
  | cons name rest =>
    cases rest with
    | nil => by_cases zero : name = 0 <;> simp [canonical, meaning, zero]
    | cons next remaining => rfl

theorem normalization_preserves_qualifiers (spelling : Spelling) :
    meaning (normalize spelling) = meaning spelling := meaning_canonical _

theorem normalization_is_idempotent (spelling : Spelling) :
    normalize (normalize spelling) = normalize spelling := by
  unfold normalize
  rw [meaning_canonical]

/-- Grouping and method replacement must compare the same logical lists. -/
theorem normalization_eq_iff (left right : Spelling) :
    normalize left = normalize right ↔ meaning left = meaning right := by
  constructor
  · intro same
    have := congrArg meaning same
    simpa only [normalization_preserves_qualifiers] using this
  · intro same
    exact congrArg canonical same

theorem grouping_matches_replacement (methods : List Spelling) (qualifier : Spelling) :
    methods.filter (fun method => decide (normalize method = normalize qualifier)) =
      methods.filter (fun method => decide (meaning method = meaning qualifier)) := by
  simp only [normalization_eq_iff]

theorem explicit_primary_stays_distinct :
    normalize (.listed [0]) ≠ normalize (.listed []) := by decide

def shortKey (name : Nat) : Spelling := canonical [name]

theorem short_key_means_one_qualifier (name : Nat) : meaning (shortKey name) = [name] :=
  meaning_canonical _

theorem primary_named_short_key_is_not_unqualified :
    shortKey 0 ≠ normalize (.listed []) := by decide

end LeanPoo.Object.ClosQualifiers
