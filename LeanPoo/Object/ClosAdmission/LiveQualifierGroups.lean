-- SPDX-License-Identifier: Apache-2.0 AND LGPL-2.1-or-later
import LeanPoo.Object.ClosAdmission.StandardRecipe

namespace LeanPoo.Object.ClosAdmission.LiveQualifierGroups

open ClosQualifiers StandardRecipe

structure PublishedKey where
  raw : Spelling
  key : Spelling
  normalized : key = normalize raw

/-- The published key can be used only when the live read returns the
same spelling. The stored key has that spelling's normalization. -/
def checkedKey (published : Option PublishedKey) (live : Spelling) : Spelling :=
  match published with
  | none => normalize live
  | some entry => if entry.raw = live then entry.key else normalize live

theorem checked_key_eq_live (published : Option PublishedKey) (live : Spelling) :
    checkedKey published live = normalize live := by
  cases published with
  | none => rfl
  | some entry =>
    by_cases same : entry.raw = live
    · simp [checkedKey, same, entry.normalized]
    · simp [checkedKey, same]

abbrev Reader (World Error Method : Type) :=
  Method → ExceptT Error (StateM World) Spelling

def select (key : Spelling → Spelling) (role : Role) (method : Method)
    (live : Spelling) : Option Method :=
  if key live = normalize (spelling role) then some method else none

/-- A grouping pass issues every live read in ranked order. Errors keep the
world left by the reads that have already run. -/
def pass (read : Reader World Error Method) (key : Method → Spelling → Spelling)
    (role : Role) : List Method → ExceptT Error (StateM World) (List Method)
  | [] => pure []
  | method :: rest => do
    let live ← read method
    let tail ← pass read key role rest
    pure (match select (key method) role method live with
          | some chosen => chosen :: tail
          | none => tail)

def four (read : Reader World Error Method) (key : Method → Spelling → Spelling)
    (methods : List Method) : ExceptT Error (StateM World) (Groups Method) := do
  let around ← pass read key .around methods
  let before ← pass read key .before methods
  let primary ← pass read key .primary methods
  let after ← pass read key .after methods
  pure ⟨around, before, primary, after⟩

/-- For any publication returned by the lookup, the selected spelling has
the same normalization. Every live read and its effects are preserved. -/
theorem four_without_publication (read : Reader World Error Method)
    (published : Method → Spelling → Option PublishedKey) (methods : List Method) :
    four read (fun method live => checkedKey (published method live) live) methods =
      four read (fun _ => normalize) methods := by
  have keys : (fun method live => checkedKey (published method live) live) =
      (fun _ => normalize) := by
    funext method live
    exact checked_key_eq_live _ _
  rw [keys]

/-- One direct read and at most one result cons. The four calls remain in
role order. In particular, a read callback can change the next qualifier. -/
def one (read : Reader World Error Method) (role : Role) (method : Method) :
    ExceptT Error (StateM World) (List Method) := do
  let live ← read method
  pure (if normalize live = spelling role then [method] else [])

private theorem normalize_role (role : Role) : normalize (spelling role) = spelling role := by
  cases role <;> decide

theorem one_eq_pass (read : Reader World Error Method) (role : Role) (method : Method) :
    one read role method = pass read (fun _ => normalize) role [method] := by
  unfold one
  simp only [pass, pure_bind, select, normalize_role]
  congr 1
  funext live
  split <;> simp_all

def singleton (read : Reader World Error Method) (method : Method) :
    ExceptT Error (StateM World) (Groups Method) := do
  let around ← one read .around method
  let before ← one read .before method
  let primary ← one read .primary method
  let after ← one read .after method
  pure ⟨around, before, primary, after⟩

theorem singleton_eq_four (read : Reader World Error Method)
    (published : Method → Spelling → Option PublishedKey) (method : Method) :
    singleton read method =
      four read (fun m live => checkedKey (published m live) live) [method] := by
  rw [four_without_publication]
  simp only [singleton, four, one_eq_pass]

end LeanPoo.Object.ClosAdmission.LiveQualifierGroups
