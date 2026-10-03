import LeanPoo.C4.Merge

/-! Operational extended precedence: leftmost eligible selection on the C4
prefix candidates. A separate replay certifies the optimized merger's output.
-/
namespace LeanPoo.C4.Precedence

def eligible (lists : List (List String)) (name : String) : Bool :=
  lists.all fun order => !(order.drop 1).contains name

def heads (lists : List (List String)) : List String := lists.filterMap List.head?

def choose (lists : List (List String)) : Option String :=
  if lists.all List.isEmpty then none else (heads lists).find? (eligible lists)

def advance (lists : List (List String)) (name : String) : List (List String) :=
  lists.map fun order => match order with
    | first :: rest => if first == name then rest else order
    | [] => []

def candidates (parents locals : List (List String)) (suffix : List String) : List (List String) :=
  parents.map (fun order => order.filter (fun name => !suffix.contains name)) ++
    locals.map (fun order => order.filter (fun name => !suffix.contains name))

theorem candidates_without_suffix (parents locals : List (List String)) :
    candidates parents locals [] = parents ++ locals := by
  have unchanged (order : List String) : order.filter (fun name => !([] : List String).contains name) = order :=
    List.filter_eq_self.mpr (by intro name member; simp)
  simp only [candidates, unchanged]
  simp

theorem choose_eligible (lists : List (List String)) (name : String)
    (selected : choose lists = some name) : eligible lists name = true := by
  unfold choose at selected
  split at selected
  · cases selected
  · exact List.find?_some selected

/-- Every head to the left of the selected one is blocked by a candidate tail. -/
theorem choose_leftmost (lists : List (List String)) (name : String)
    (selected : choose lists = some name) :
    ∃ before after, heads lists = before ++ name :: after ∧
      ∀ earlier ∈ before, eligible lists earlier = false := by
  unfold choose at selected
  split at selected
  · cases selected
  · obtain ⟨_, before, after, same, blocked⟩ := List.find?_eq_some_iff_append.mp selected
    exact ⟨before, after, same, by simpa using blocked⟩

inductive Trace : List (List String) → List String → Prop where
  | done (empty : lists.all List.isEmpty = true) : Trace lists []
  | step (chosen : choose lists = some name)
      (rest : Trace (advance lists name) output) : Trace lists (name :: output)

theorem Trace.unique (first : Trace lists output₁) (second : Trace lists output₂) : output₁ = output₂ := by
  induction first generalizing output₂ with
  | done empty =>
    cases second with
    | done _ => rfl
    | step chosen _ => simp [choose, empty] at chosen
  | @step lists name output chosen rest ih =>
    cases second with
    | done empty => simp [choose, empty] at chosen
    | @step _ other tail selected next =>
      have same : name = other := Option.some.inj (chosen.symm.trans selected)
      subst other
      exact congrArg (name :: ·) (ih next)

/-- Replay a finite claimed output; an incomplete or differently ordered trace
is rejected. No tail-count state from the optimized merger is trusted. -/
def check (lists : List (List String)) : (output : List String) → Option (PLift (Trace lists output))
  | [] => if empty : lists.all List.isEmpty = true then some ⟨.done empty⟩ else none
  | name :: rest =>
    if chosen : choose lists = some name then
      (check (advance lists name) rest).map (fun trace => ⟨Trace.step chosen trace.down⟩)
    else none

structure Certified (lists : List (List String)) where
  output : List String
  trace : Trace lists output

def mergeCertified (lists : List (List String)) : Except C4.Error (Certified lists) := do
  let output ← C4.merge lists
  let some trace := check lists output | throw .inconsistentOrder
  return ⟨output, trace.down⟩

/-- The C4 suffix-exempt policy certifies only the prefix, then retains the
caller-supplied suffix verbatim. Graph-level suffix selection is separate. -/
def mergePrefix (parents locals : List (List String)) (suffix : List String) :
    Except C4.Error (Certified (candidates parents locals suffix)) :=
  mergeCertified (candidates parents locals suffix)

end LeanPoo.C4.Precedence
