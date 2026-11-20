-- SPDX-License-Identifier: Apache-2.0 AND LGPL-2.1-or-later
namespace LeanPoo.Object.AdmittedInterfaceRead

-- Keep the actual runtime body: it owns missing/default/error behavior.
-- Only a proved identity conversion may be omitted. Failed admission takes
-- the complete original conversion path, including any effects it may own.
def checked {Object Value Error : Type} (cast : Object → Except Error Object)
    (body : Object → Except Error Value) (object : Object) : Except Error Value := do
  let receiver ← cast object
  body receiver

def guarded {Object Value Error : Type} (admitted : Object → Bool)
    (cast : Object → Except Error Object) (body : Object → Except Error Value)
    (object : Object) : Except Error Value :=
  if admitted object then body object else checked cast body object

theorem exact {Object Value Error : Type} (admitted : Object → Bool)
    (cast : Object → Except Error Object) (body : Object → Except Error Value)
    (identity : ∀ object, admitted object = true → cast object = .ok object)
    (object : Object) : guarded admitted cast body object = checked cast body object := by
  cases proof : admitted object with
  | false => simp [guarded, proof]
  | true => simp [guarded, checked, proof, identity object proof, Bind.bind, Except.bind]

theorem body_error_retained {Object Value Error : Type}
    (admitted : Object → Bool) (cast : Object → Except Error Object)
    (body : Object → Except Error Value) (object : Object) (cause : Error)
    (yes : admitted object = true) (failed : body object = .error cause) :
    guarded admitted cast body object = .error cause := by simp [guarded, yes, failed]

-- The caller provides fresh conversion facts and bodies in both worlds.
-- Entry admission is never reused after the opaque action or source update.
theorem independent_worlds {World Object Value Error : Type}
    (admitted : World → Object → Bool) (cast : World → Object → Except Error Object)
    (body : World → Object → Except Error Value)
    (identity : ∀ world object, admitted world object = true → cast world object = .ok object)
    (before after : World) (object : Object) :
    (guarded (admitted before) (cast before) (body before) object,
     guarded (admitted after) (cast after) (body after) object) =
    (checked (cast before) (body before) object,
     checked (cast after) (body after) object) := by
  rw [exact _ _ _ (identity before), exact _ _ _ (identity after)]

end LeanPoo.Object.AdmittedInterfaceRead

namespace LeanPoo.Object.AdmittedInterfaceRead.Effects

-- Equality of returned receivers alone is insufficient: interface conversion
-- can reify an interface or run a user method. Preserve state and effect trace.
def checked {World Object Value Error Event : Type}
    (cast : World → Object → Except Error (Object × World × List Event))
    (body : World → Object → Except Error (Value × World × List Event))
    (world : World) (object : Object) : Except Error (Value × World × List Event) := do
  let (receiver, next, initialEvents) ← cast world object
  let (value, final, suffix) ← body next receiver
  pure (value, final, initialEvents ++ suffix)

def guarded {World Object Value Error Event : Type}
    (admitted : World → Object → Bool)
    (cast : World → Object → Except Error (Object × World × List Event))
    (body : World → Object → Except Error (Value × World × List Event))
    (world : World) (object : Object) : Except Error (Value × World × List Event) :=
  if admitted world object then body world object else checked cast body world object

theorem exact {World Object Value Error Event : Type}
    (admitted : World → Object → Bool)
    (cast : World → Object → Except Error (Object × World × List Event))
    (body : World → Object → Except Error (Value × World × List Event))
    (identity : ∀ world object, admitted world object = true →
      cast world object = .ok (object, world, []))
    (world : World) (object : Object) :
    guarded admitted cast body world object = checked cast body world object := by
  cases proof : admitted world object with
  | false => simp [guarded, proof]
  | true =>
    cases outcome : body world object with
    | error cause =>
      simp [guarded, checked, proof, identity world object proof,
        Bind.bind, Except.bind, outcome]
    | ok payload =>
      rcases payload with ⟨value, final, suffix⟩
      simp [guarded, checked, proof, identity world object proof,
        Bind.bind, Except.bind, outcome]
      rfl

-- A once-valid admission cannot cross an opaque callback that changes the
-- descriptor. The fresh guarded operation falls back and returns its error.
def changedCast (changed : Bool) (object : Unit) : Except Unit Unit :=
  if changed then .error () else .ok object

example : guarded (fun _ _ => false)
    (fun changed object => (changedCast changed object).map (fun x => (x, changed, ([] : List Unit))))
    (fun world _ => .ok ((), world, [])) true () = .error () := rfl

end LeanPoo.Object.AdmittedInterfaceRead.Effects
