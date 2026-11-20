-- SPDX-License-Identifier: Apache-2.0 AND LGPL-2.1-or-later
import Std

namespace LeanPoo.Proof.Gerbil.SccOrdinalRows

variable {K Row : Type} {n : Nat}

structure Roster (K : Type) (n : Nat) where
  key : Fin n → K
  position : K → Option (Fin n)
  exact : ∀ key' position', position key' = some position' ↔ key position' = key'

abbrev Symbolic (K Row : Type) := K → Option Row
abbrev Cells (n : Nat) (Row : Type) := Fin n → Option Row

def read (roster : Roster K n) (cells : Cells n Row) (key : K) : Option Row :=
  (roster.position key).bind cells

def store [DecidableEq A] (cells : A → Option Row) (key : A) (row : Row) : A → Option Row :=
  fun other => if key = other then some row else cells other

/-- The builder already knows the admitted owner's ordinal when the author
returns its row. Store the same owned row token in that cell. -/
theorem store_commutes [DecidableEq K] (roster : Roster K n)
    (cells : Cells n Row) (owner : Fin n) (row : Row) :
    read roster (store cells owner row) = store (read roster cells) (roster.key owner) row := by
  funext key
  cases atKey : roster.position key with
  | none =>
    have different : roster.key owner ≠ key := fun same => by
      have found := (roster.exact key owner).mpr same
      rw [atKey] at found
      contradiction
    simp [read, store, atKey, different]
  | some ordinal =>
    have same : roster.key owner = key ↔ owner = ordinal := by
      rw [← roster.exact, atKey, Option.some.injEq, eq_comm]
    simp [read, store, atKey, same]

def writeCells (rows : List (Fin n × Row)) (cells : Cells n Row) : Cells n Row :=
  rows.foldl (fun storage (owner, row) => store storage owner row) cells

def writeSymbolic [DecidableEq K] (roster : Roster K n)
    (rows : List (Fin n × Row)) (table : Symbolic K Row) : Symbolic K Row :=
  rows.foldl (fun storage (owner, row) => store storage (roster.key owner) row) table

theorem capture_commutes [DecidableEq K] (roster : Roster K n)
    (rows : List (Fin n × Row)) (cells : Cells n Row) :
    read roster (writeCells rows cells) = writeSymbolic roster rows (read roster cells) := by
  induction rows generalizing cells with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨owner, row⟩
    unfold writeCells writeSymbolic
    simp only [List.foldl_cons]
    change read roster (writeCells rest (store cells owner row)) =
      writeSymbolic roster rest (store (read roster cells) (roster.key owner) row)
    rw [ih, store_commutes]

/-- The same author acquisition gate runs once before either representation
is observable. Keep its event order and first refusal. The result returns
the same original row token on every query, including after repeated capture. -/
theorem publication_same_author_boundary [DecidableEq K] {Error Event A : Type}
    (roster : Roster K n) (cells : Cells n Row)
    (captured : Except Error (List (Fin n × Row)) × List Event)
    (publish : Symbolic K Row → Except Error A) :
    (captured.1 >>= fun rows => publish (read roster (writeCells rows cells)), captured.2) =
      (captured.1 >>= fun rows => publish (writeSymbolic roster rows (read roster cells)), captured.2) := by
  rcases captured with ⟨result, trace⟩
  cases result with
  | error cause => rfl
  | ok rows =>
    simp [Bind.bind, Except.bind, capture_commutes]

theorem unknown_key_remains_absent (roster : Roster K n) (cells : Cells n Row)
    (rows : List (Fin n × Row)) (key : K) (absent : roster.position key = none) :
    read roster (writeCells rows cells) key = none := by simp [read, absent]

/-- The prefix ran only under the stock table route. Restore it with the
stock insertion operation before the first changed-route write. That write
may inspect the whole table, modify state, or refuse the current row. -/
theorem retire_before_effect_exact [DecidableEq K] {Error State Value : Type}
    (roster : Roster K n) (cells : Cells n Row) (prefixRows : List (Fin n × Row))
    (perform : Symbolic K Row → State → Except Error Value × State) (state : State) :
    perform (read roster (writeCells prefixRows cells)) state =
      perform (writeSymbolic roster prefixRows (read roster cells)) state := by
  rw [capture_commutes]

/-- Physical edge packing can stop without changing a row. The symbolic
fallback includes exactly the previous accepted rows and the current write. -/
theorem word_fallback_exact [DecidableEq K] (roster : Roster K n) (cells : Cells n Row)
    (prefixRows : List (Fin n × Row)) (owner : Fin n) (row : Row) :
    read roster (store (writeCells prefixRows cells) owner row) =
      writeSymbolic roster (prefixRows ++ [(owner, row)]) (read roster cells) := by
  rw [store_commutes, capture_commutes]
  simp [writeSymbolic, List.foldl_append]

end LeanPoo.Proof.Gerbil.SccOrdinalRows
