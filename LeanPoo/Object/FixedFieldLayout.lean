-- SPDX-License-Identifier: Apache-2.0 AND LGPL-2.1-or-later
/- A runtime class identity does not imply its mutable slot map is unchanged.
   Fixed access is valid only for the admitted current field layout. This
   model specifies offset authentication, not the runtime class implementation. -/
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
