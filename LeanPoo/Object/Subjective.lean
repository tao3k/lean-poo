import LeanPoo.Object.Multimethod

/-!
Subjective dispatch adds one implicitly supplied context argument to a
multimethod. Lean's ReaderT scopes that argument; StateT threads the generic's
immutable candidate cache through calls. Neither the subject nor the method
table is stored in global mutable state.
-/

namespace LeanPoo.Object.Subjective

/-- In a lexicographic multimethod, the first dispatch argument has the
highest precedence and the last has the lowest. -/
inductive Position where
  | first
  | last
  deriving Repr, BEq

/-- Build the subject as one additional dispatch dimension. The method body
still receives the complete typed pair of subject and explicit arguments. -/
def generic {Subject Args Method Result : Type}
    (position : Position) (explicitArity : Nat)
    (subjectPrecedence : Subject → List String)
    (argumentPrecedence : Args → List (List String))
    (combine : Array Method → (Subject × Args) → Result) :
    Multimethod (Subject × Args) Method Result :=
  { arity := explicitArity + 1
    precedence := fun (subject, args) =>
      match position with
      | .first => subjectPrecedence subject :: argumentPrecedence args
      | .last => argumentPrecedence args ++ [subjectPrecedence subject]
    combine }

/-- A scoped call reads the implicit subject and retains the updated
candidate cache for later calls in the same scope. -/
abbrev Scope (Subject Args Method Result A : Type) :=
  ReaderT Subject
    (StateT (Multimethod (Subject × Args) Method Result)
      (Except MultimethodError)) A

def call {Subject Args Method Result : Type} (args : Args) :
    Scope Subject Args Method Result Result := do
  let subject ← read
  let current ← get
  match current.call (subject, args) with
  | .ok (result, updated) =>
      set updated
      return result
  | .error error => throw error

/-- Rebind the implicit subject for a nested scope. The surrounding subject
is restored after the action; cache changes remain in the threaded state. -/
def withSubject {Subject Args Method Result A : Type}
    (subject : Subject) (action : Scope Subject Args Method Result A) :
    Scope Subject Args Method Result A :=
  fun _ => action.run subject

def run {Subject Args Method Result A : Type}
    (action : Scope Subject Args Method Result A)
    (subject : Subject)
    (initial : Multimethod (Subject × Args) Method Result) :
    Except MultimethodError
      (A × Multimethod (Subject × Args) Method Result) :=
  (action.run subject).run initial

end LeanPoo.Object.Subjective
