-- SPDX-License-Identifier: Apache-2.0 AND LGPL-2.1-or-later
import LeanPoo.Object.ClosQualifiers
import LeanPoo.Object.MethodCombinationSemantics

namespace LeanPoo.Object.ClosAdmission.StandardRecipe
open LeanPoo.Object.ClosQualifiers
open LeanPoo.Object.MethodCombination

/-- These are names interned in the admitted method generation.
The explicit list containing the primary name has no standard role. -/
inductive Role where
  | around | before | primary | after
  deriving DecidableEq

def spelling : Role → Spelling
  | .primary => .symbol 0
  | .around => .symbol 1
  | .before => .symbol 2
  | .after => .symbol 3

def roleOf (qualifier : Spelling) : Option Role :=
  let names := meaning qualifier
  if names = [] then some .primary
  else if names = [1] then some .around
  else if names = [2] then some .before
  else if names = [3] then some .after
  else none

theorem same_role_as_scheme (qualifier : Spelling) (role : Role) :
    roleOf qualifier = some role ↔ normalize qualifier = normalize (spelling role) := by
  rw [normalization_eq_iff]
  unfold roleOf
  generalize meaning qualifier = words
  cases role <;>
    by_cases a : words = [] <;> by_cases b : words = [1] <;>
    by_cases c : words = [2] <;> by_cases d : words = [3] <;>
    simp_all [spelling, meaning]

structure Groups (Method : Type) where
  around : List Method := []
  before : List Method := []
  primary : List Method := []
  after : List Method := []

def atRole (groups : Groups Method) : Role → List Method
  | .around => groups.around
  | .before => groups.before
  | .primary => groups.primary
  | .after => groups.after

def prepend (groups : Groups Method) (role : Option Role) (method : Method) :
    Groups Method :=
  match role with
  | some .around => { groups with around := method :: groups.around }
  | some .before => { groups with before := method :: groups.before }
  | some .primary => { groups with primary := method :: groups.primary }
  | some .after => { groups with after := method :: groups.after }
  | none => groups

/-- Only admitted qualifier values are consumed here. The four live read
passes in Scheme cannot be replaced by this fold while they are observable. -/
def group (ranked : List (Method × Spelling)) : Groups Method :=
  ranked.foldr (fun row groups => prepend groups (roleOf row.2) row.1) {}

private theorem atRole_prepend (groups : Groups Method) (selected : Option Role)
    (method : Method) (role : Role) :
    atRole (prepend groups selected method) role =
      if selected = some role then method :: atRole groups role else atRole groups role := by
  cases selected with
  | none => cases role <;> rfl
  | some chosen => cases chosen <;> cases role <;> rfl

theorem one_pass_preserves_group_order (ranked : List (Method × Spelling)) (role : Role) :
    atRole (group ranked) role =
      (ranked.filter fun row => decide (normalize row.2 = normalize (spelling role))).map Prod.fst := by
  induction ranked with
  | nil => cases role <;> rfl
  | cons row rest ih =>
    simp only [group, List.foldr_cons, List.filter_cons] at ih ⊢
    rw [atRole_prepend, ih]
    have test :
        decide (normalize row.2 = normalize (spelling role)) =
          decide (roleOf row.2 = some role) := by
      apply Bool.eq_iff_iff.mpr
      simpa only [decide_eq_true_eq] using (same_role_as_scheme row.2 role).symm
    rw [test]
    by_cases present : roleOf row.2 = some role <;> simp [present]

/-- The reflective carrier keeps specificity order. This recipe additionally
stores execution order for after methods and the early no-primary decision. -/
structure Recipe (Method : Type) where
  groups : Groups Method
  afterExecution : List Method
  hasPrimary : Bool

def prepare (groups : Groups Method) : Recipe Method :=
  ⟨groups, groups.after.reverse, !groups.primary.isEmpty⟩

def bindMethods {Receiver : Type} {M : Type → Type} {Result : Type}
    (groups : Groups Method) (body : Method → SubMethod Receiver M Result)
    (side : Method → SideMethod Receiver M) : Methods Receiver M Result :=
  { around := groups.around.map body, before := groups.before.map side,
    primary := groups.primary.map body, after := groups.after.map side }

def execute {Receiver : Type} {M : Type → Type} {Result : Type} [Monad M]
    (recipe : Recipe Method) (receiver : Receiver)
    (body : Method → SubMethod Receiver M Result) (side : Method → SideMethod Receiver M)
    (refuse : Receiver → M Result) : M Result :=
  if !recipe.hasPrimary then refuse receiver
  else
    wrapMethods (recipe.groups.around.map body) (fun current => do
      executeSides (recipe.groups.before.map side) current
      let result ← wrapMethods (recipe.groups.primary.map body) refuse current
      executeSides (recipe.afterExecution.map side) current
      pure result) receiver

/-- Resolving method bodies and issuing checks remains in the supplied live
interpreter. Early rejection, around nesting and side order match cold use. -/
theorem prepared_standard_matches_live {Receiver : Type} {M : Type → Type} {Result : Type}
    [Monad M] (groups : Groups Method) (receiver : Receiver)
    (body : Method → SubMethod Receiver M Result) (side : Method → SideMethod Receiver M)
    (refuse : Receiver → M Result) :
    execute (prepare groups) receiver body side refuse =
      if groups.primary.isEmpty then refuse receiver
      else standard (bindMethods groups body side) refuse receiver := by
  simp [execute, prepare, bindMethods, standard, List.map_reverse]

theorem missing_primary_precedes_wrappers {Receiver : Type} {M : Type → Type} {Result : Type}
    [Monad M] (groups : Groups Method) (receiver : Receiver)
    (body : Method → SubMethod Receiver M Result) (side : Method → SideMethod Receiver M)
    (refuse : Receiver → M Result) (missing : groups.primary = []) :
    execute (prepare groups) receiver body side refuse = refuse receiver := by
  simp [execute, prepare, missing]


def filterGroups (groups : Groups Method) (live : Method → Bool) : Groups Method :=
  ⟨groups.around.filter live, groups.before.filter live, groups.primary.filter live,
   groups.after.filter live⟩

private theorem filter_prepend (groups : Groups Method) (role : Option Role)
    (method : Method) (live : Method → Bool) :
    filterGroups (prepend groups role method) live =
      if live method then prepend (filterGroups groups live) role method
      else filterGroups groups live := by
  cases role with
  | none => simp [prepend]
  | some chosen => cases chosen <;> cases hit : live method <;>
      simp [filterGroups, prepend, hit]

theorem filter_groups_eq_live (rows : List (Method × Spelling)) (live : Method → Bool) :
    filterGroups (group rows) live =
      group (rows.filter fun row => live row.1) := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    simp only [group, List.foldr_cons] at ih ⊢
    rw [filter_prepend, ih]
    cases includes : live row.1 <;> simp [includes]

/-- Selecting from published groups uses only an ordered mask. No qualifier
normalization, regrouping or reversal is needed after the live mask exists. -/
def select (recipe : Recipe Method) (live : Method → Bool) : Recipe Method :=
  let groups := filterGroups recipe.groups live
  ⟨groups, recipe.afterExecution.filter live, !groups.primary.isEmpty⟩

theorem selection_preserves_preparation (rows : List (Method × Spelling)) (live : Method → Bool) :
    select (prepare (group rows)) live = prepare (group (rows.filter fun row => live row.1)) := by
  simp only [select, prepare, List.filter_reverse, ← filter_groups_eq_live]
  rfl

end LeanPoo.Object.ClosAdmission.StandardRecipe
