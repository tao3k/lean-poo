-- SPDX-License-Identifier: Apache-2.0 AND LGPL-2.1-or-later
import LeanPoo.Proof.Gerbil.SlotAssembly
import LeanPoo.C4.Precedence

namespace LeanPoo.Proof.Gerbil.PlainSlotPreparation

open SlotAssembly (Store put install)

/-- The receiver is fixed. Compiling a direct constant or a self-bound
thunk constructs a method and does not call it. -/
def compiled (compile : S → V) (raw : Store S) : Store V :=
  fun key => Option.map compile (raw key)

theorem compile_put (compile : S → V) (store : Store S) (key : Nat) (spec : S) :
    compiled compile (put store key spec) = put (compiled compile store) key (compile spec) := by
  funext query
  by_cases same : query = key <;> simp [compiled, put, same]

/-- With defaults, inherited definitions, and author protocols excluded,
both assemblies expose identical methods. Overwrites retain their original
contribution order and the last definition at a repeated name. -/
theorem compile_install (compile : S → V) (rows : List (Nat × S)) (store : Store S) :
    compiled compile (install rows store) =
      install (rows.map (fun (key, spec) => (key, compile spec))) (compiled compile store) := by
  induction rows generalizing store with
  | nil => rfl
  | cons row rest ih =>
    rcases row with ⟨key, spec⟩
    simp only [install, List.map_cons]
    rw [ih, compile_put]

/-- Distinct-key insertions consume one slot. Replacements consume none.
The original enumeration and repeated replacements cannot grow the table
if capacity covers even the worst case of all contributions inserting. -/
theorem free_before_any_write (free width contributions used : Nat)
    (eligible : width / 4 + contributions ≤ free) (soFar : used ≤ contributions) :
    width / 4 ≤ free - used := by omega

/-- Native qualification and allocation are outside the pure interval.
Preserve their failure and consumption of exactly one original seed. -/
theorem ordinary_publication (prepare : St → Except E (St × Store S))
    (initial : St) (rows : List (Nat × S)) (compile : S → V)
    (publish : St → Store V → Except E A) :
    (prepare initial >>= fun (state, base) =>
      publish state (compiled compile (install rows base))) =
    (prepare initial >>= fun (state, base) =>
      publish state
        (install (rows.map (fun (key, spec) => (key, compile spec))) (compiled compile base))) := by
  cases next : prepare initial with
  | error e => rfl
  | ok res =>
    rcases res with ⟨state, base⟩
    simp [Bind.bind, Except.bind, compile_install]

/-- With no parent order and no suffix, C4 has no tail to append to the root. -/
theorem empty_c4_tail :
    ((C4.Precedence.mergePrefix [] [[]] []).map (·.output)).toOption = some [] := by
  decide

/-- For a parentless receiver without a protocol, the stock private active
frame is pushed and removed before the order is published. Feed the same
canonical order and caller frame to any following preparation, including
one which later calls an author or rejects the object. -/
theorem closed_precedence_publication (receiver : String) (active : List String)
    (next : List String → List String → Except E A) (reject : C4.Error → Except E A) :
    (match C4.Precedence.mergePrefix [] [[]] [] with
      | .ok tail => next (receiver :: tail.output) (receiver :: active).tail
      | .error cause => reject cause) =
      next [receiver] active := by
  cases result : C4.Precedence.mergePrefix [] [[]] [] with
  | error cause =>
    have impossible := empty_c4_tail
    simp [result, Except.map, Except.toOption] at impossible
  | ok resultValue =>
    have tail : resultValue.output = [] := by
      simpa [result, Except.map, Except.toOption] using empty_c4_tail
    simp [tail]

end LeanPoo.Proof.Gerbil.PlainSlotPreparation
