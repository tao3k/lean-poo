-- SPDX-License-Identifier: Apache-2.0 AND LGPL-2.1-or-later
/- A runtime class identity does not imply its mutable slot map is unchanged.
   Fixed access is valid only for the admitted current field layout. This
   model specifies reflective-route offset authentication, not the runtime
   class implementation. SignedRecord below has a different authority: the
   final record constructor's physical fields, used by both issuer and walker. -/
namespace LeanPoo.Object.FixedFieldLayout

def checked {Value Error : Type} (cause : Error) (expected current : Nat)
    (access : Nat → Except Error Value) : Except Error Value :=
  if current = expected then access expected else .error cause

theorem admitted_exact {Value Error : Type} (cause : Error) (expected : Nat)
    (access : Nat → Except Error Value) :
    checked cause expected expected access = access expected := by simp [checked]

theorem current_field_exact {Value Error : Type} (cause : Error) (expected current : Nat)
    (same : current = expected) (access : Nat → Except Error Value) :
    checked cause expected current access = access current := by simp [checked, same]

theorem moved_field_refused {Value Error : Type} (cause : Error) (expected current : Nat)
    (moved : current ≠ expected) (access : Nat → Except Error Value) :
    checked cause expected current access = .error cause := by simp [checked, moved]

/-- Layout refusal precedes access and its possible original exception. -/
example : checked "changed metadata ref" 0 1
    (fun _ => (.error "access dispatched" : Except String Nat)) =
    .error "changed metadata ref" := rfl

/-- Once layout is admitted, an access failure retains its exact cause. -/
example : checked true 0 0
    (fun _ => (.error false : Except Bool Nat)) = .error false := rfl

def around {Value Error World : Type} (check : World → Except Error Value)
    (effect : World → Except Error World) (world : World) : Except Error Value := do
  let _ ← check world
  let next ← effect world
  check next

/-- No entry approval can certify a layout changed by the intervening action. -/
example : around (fun offset => checked "layout" 0 offset
      (fun index => (.ok index : Except String Nat)))
    (fun _ => .ok 1) 0 = .error "layout" := rfl

end LeanPoo.Object.FixedFieldLayout

namespace LeanPoo.Object.FixedFieldLayout.SignedRecord

-- Extract only AFTER the exact final record and its original signature were
-- authenticated. Both physical parents and their order are signature fields.
-- A mutable symbolic display/inspection map does not supply this row.
def row {Read Error : Type} (issued : Read → Bool) (parents : Read → List Read)
    (unissued : Error) (read : Read) : Except Error (List Read) :=
  if issued read then .ok (parents read) else .error unissued

theorem rows_exact {Read Error : Type} (issued : Read → Bool)
    (physical signed : Read → List Read) (unissued : Error)
    (authenticated : ∀ read, issued read = true → physical read = signed read) :
    row issued physical unissued = row issued signed unissued := by
  funext read
  cases valid : issued read with
  | false => simp [row, valid]
  | true => simp [row, valid, authenticated read valid]

-- Reuse the existing consumer/DFS algorithm. Equal authenticated row oracles
-- preserve all results, child order and first failures; no replacement walker
-- or second evaluator is specified here.
theorem consumer_exact {Read Error Result : Type} (issued : Read → Bool)
    (physical signed : Read → List Read) (unissued : Error)
    (authenticated : ∀ read, issued read = true → physical read = signed read)
    (consume : (Read → Except Error (List Read)) → Result) :
    consume (row issued physical unissued) = consume (row issued signed unissued) := by
  rw [rows_exact issued physical signed unissued authenticated]

theorem unissued_refused_before_children {Read Error : Type}
    (issued : Read → Bool) (physical : Read → List Read) (unissued : Error)
    (read : Read) (invalid : issued read = false) :
    row issued physical unissued read = .error unissued := by
  simp [row, invalid]

-- A logical field-map redirect to an unrelated payload can give a DIFFERENT
-- graph even with the same record class. Class identity alone is insufficient.
example : row (fun _ : Nat => true) (fun _ => [1]) "unissued" 0 ≠
    row (fun _ : Nat => true) (fun _ => [2]) "unissued" 0 := by simp [row]

end LeanPoo.Object.FixedFieldLayout.SignedRecord
