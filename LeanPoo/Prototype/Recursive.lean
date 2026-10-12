import LeanPoo.Prototype.Compose

/-! A total executable semantics for the paper's open recursion.
Requests denote reads/calls of the final self. Finite approximations separate
unresolved computation from actual user errors. The depth bounds recursive
self calls, while each interaction tree is structurally terminating. -/
namespace LeanPoo.Prototype.Recursive

inductive Observation (α : Type) where
  | pending
  | error (message : String)
  | value (result : α)
  deriving Repr, BEq, DecidableEq

/-- Information growth; a returned value or error cannot subsequently change. -/
def Observation.Refines (left right : Observation α) : Prop :=
  left = .pending ∨ left = right

theorem Observation.Refines.refl (value : Observation α) : value.Refines value :=
  Or.inr rfl

theorem Observation.Refines.trans {α : Type} {left middle right : Observation α}
    (first : left.Refines middle)
    (second : middle.Refines right) : left.Refines right := by
  rcases first with pending | same
  · exact Or.inl pending
  · subst left
    exact second

theorem Observation.Refines.known {α : Type} {left right : Observation α}
    (grows : left.Refines right)
    (known : left ≠ .pending) : left = right := by
  rcases grows with pending | same
  · exact False.elim (known pending)
  · exact same

/-- A computation can return, fail, or request a recursive result before
continuing. This W-type admits arbitrary well-founded local continuations. -/
inductive Interaction (Input Output α : Type) where
  | value (result : α)
  | error (message : String)
  | call (input : Input) (next : Output → Interaction Input Output α)

def Interaction.bind (first : Interaction Input Output α)
    (next : α → Interaction Input Output β) : Interaction Input Output β :=
  match first with
  | .value result => next result
  | .error message => .error message
  | .call input continuation => .call input (fun value => (continuation value).bind next)

def Interaction.map (transform : α → β) (tree : Interaction Input Output α) :
    Interaction Input Output β := tree.bind (fun value => .value (transform value))

theorem Interaction.bind_value (tree : Interaction Input Output α) :
    tree.bind Interaction.value = tree := by
  induction tree with
  | value => rfl
  | error => rfl
  | call input next ih =>
    simp only [Interaction.bind]
    congr 1
    funext value
    exact ih value

theorem Interaction.bind_assoc (tree : Interaction Input Output α)
    (first : α → Interaction Input Output β) (second : β → Interaction Input Output γ) :
    (tree.bind first).bind second = tree.bind (fun value => (first value).bind second) := by
  induction tree with
  | value => rfl
  | error => rfl
  | call input next ih =>
    simp only [Interaction.bind]
    congr 1
    funext value
    exact ih value

def Interaction.interpret (oracle : Input → Observation Output)
    (tree : Interaction Input Output α) : Observation α :=
  match tree with
  | .value result => .value result
  | .error message => .error message
  | .call input next => match oracle input with
    | .pending => .pending
    | .error message => .error message
    | .value result => (next result).interpret oracle

theorem Interaction.interpret_refines (left right : Input → Observation Output)
    (grows : ∀ input, (left input).Refines (right input))
    (tree : Interaction Input Output α) :
    (tree.interpret left).Refines (tree.interpret right) := by
  induction tree with
  | value => exact .refl _
  | error => exact .refl _
  | call input next ih =>
    rcases grows input with pending | same
    · simp [Interaction.interpret, pending, Observation.Refines]
    · simp only [Interaction.interpret, same]
      cases right input with
      | pending => exact .refl _
      | error message => exact .refl _
      | value result => exact ih result

abbrev Generator (Input Output : Type) := Input → Interaction Input Output Output

/-- Recursive self calls are explicit syntax, so the kernel can reason about
them without assuming properties of an unsafe thunk. -/
def request : Generator Input Output := fun input => .call input .value

def solve (program : Generator Input Output) : Nat → Input → Observation Output
  | 0, _ => .pending
  | depth + 1, input => (program input).interpret (solve program depth)

/-- Close the ordinary POOF prototype using recursive requests as final self. -/
def close (prototype : Proto (Generator Input Output) Parent
    (Generator Input Output)) (base : Parent) : Generator Input Output :=
  prototype request base

def instantiate (prototype : Proto (Generator Input Output) Parent
    (Generator Input Output)) (base : Parent) (depth : Nat) :
    Input → Observation Output := solve (close prototype base) depth

/-- Delayed non-function values use the same recursive semantics, with a
single unit request. The inherited value can have a different carrier. -/
def instantiateValue (prototype : Proto (Interaction Unit α α) (Interaction Unit α β)
    (Interaction Unit α α)) (base : Interaction Unit α β) (depth : Nat) : Observation α :=
  solve (fun _ => prototype (request ()) base) depth ()

/-- Operational `mix` passes the same final-self request function to both
layers, while the parent supplies the child's inherited generator. -/
theorem close_compose (child : Proto (Generator Input Output) Parent (Generator Input Output))
    (parent : Proto (Generator Input Output) Base Parent) (base : Base) :
    close (compose child parent) base = child request (parent request base) := rfl

theorem solve_succ (program : Generator Input Output) (depth : Nat) (input : Input) :
    solve program (depth + 1) input = (program input).interpret (solve program depth) := rfl

theorem solve_step_refines (program : Generator Input Output) (depth : Nat) (input : Input) :
    (solve program depth input).Refines (solve program (depth + 1) input) := by
  induction depth generalizing input with
  | zero => exact Or.inl rfl
  | succ depth ih => exact (program input).interpret_refines _ _ ih

theorem solve_refines (program : Generator Input Output) (lower upper : Nat)
    (bound : lower ≤ upper) (input : Input) :
    (solve program lower input).Refines (solve program upper input) := by
  induction upper generalizing lower with
  | zero =>
    have same : lower = 0 := by omega
    subst lower
    exact .refl _
  | succ upper ih =>
    by_cases same : lower = upper + 1
    · subst lower; exact .refl _
    · have smaller : lower ≤ upper := by omega
      exact (ih lower smaller).trans (solve_step_refines program upper input)

def Returns (program : Generator Input Output) (input : Input) (value : Output) : Prop :=
  ∃ depth, solve program depth input = .value value

def Fails (program : Generator Input Output) (input : Input) (message : String) : Prop :=
  ∃ depth, solve program depth input = .error message

/-- No finite recursive observation finishes. This is a semantic predicate,
not a decidable claim inferred from a single exhausted budget. -/
def Diverges (program : Generator Input Output) (input : Input) : Prop :=
  ∀ depth, solve program depth input = .pending

theorem solve_stable (program : Generator Input Output) (depth : Nat) (input : Input)
    (known : solve program depth input ≠ .pending) (extra : Nat) :
    solve program (depth + extra) input = solve program depth input :=
  ((solve_refines program depth (depth + extra) (by omega) input).known known).symm

theorem returns_unique (program : Generator Input Output) (input : Input)
    (first : Returns program input left) (second : Returns program input right) : left = right := by
  obtain ⟨n, hn⟩ := first
  obtain ⟨m, hm⟩ := second
  have firstStable := (solve_refines program n (max n m) (Nat.le_max_left _ _) input).known
    (by simp [hn])
  have secondStable := (solve_refines program m (max n m) (Nat.le_max_right _ _) input).known
    (by simp [hm])
  rw [hn] at firstStable
  rw [hm] at secondStable
  exact Observation.value.inj (firstStable.trans secondStable.symm)

end LeanPoo.Prototype.Recursive
