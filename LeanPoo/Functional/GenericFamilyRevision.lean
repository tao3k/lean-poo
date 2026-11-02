import LeanPoo.Functional.ContractConstruction

/-! Capacity representation companion to the family cost model. It extends
the existing certified table protocol without changing its audited constructor. -/
namespace LeanPoo.Functional.GenericFamily
open Object DispatchExtension
variable {G Policy Cooked : Type} {Args Method Result : G → Type}
variable [DecidableEq G] [BEq G] [LawfulBEq G] [Hashable G]
variable (model : Model G Policy Cooked Args Method Result) (policy : Policy) (cooked : Cooked)
/-- Reserve physical capacity while keeping an empty owner-bound certified table.
Sizing neither supplies a generic nor authorizes reuse across different owners. -/
def Partial.emptyWithCapacity (capacity : Nat) : Partial model policy cooked :=
  ⟨⟨Std.DHashMap.emptyWithCapacity capacity⟩, by
    intro key generic found
    simp [DispatchTable.get?] at found⟩
omit [DecidableEq G] in
/-- Every requested key is absent regardless of reserved physical capacity. -/
theorem Partial.emptyWithCapacity_lookup (capacity : Nat) (key : G) :
    ((Partial.emptyWithCapacity model policy cooked capacity).table.get? key) = none := by
  simp [emptyWithCapacity, DispatchTable.get?]
/-- Private copied storage is overwritten by freshly constructed generic cells.
Only their domain is visible; old-only cells must be pruned before publication. -/
def overwriteStorage (old : DispatchTable G Args Method Result) :
    List ((key : G) × Multimethod (Args key) (Method key) (Result key)) → DispatchTable G Args Method Result
  | [] => old
  | cell :: rest => overwriteStorage (old.install cell.1 cell.2) rest
omit [DecidableEq G] in
/-- Writing other keys preserves the queried entry, even if it came from a
foreign owner. This intermediate storage is not a certified published family. -/
theorem overwriteStorage_missing (cells) (old : DispatchTable G Args Method Result) (key : G)
    (missing : key ∉ cells.map Sigma.fst) : (overwriteStorage old cells).get? key = old.get? key := by
  induction cells generalizing old with
  | nil => rfl
  | cons cell rest ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at missing
    rw [overwriteStorage, ih _ missing.2]
    simp [DispatchTable.get?, DispatchTable.install, Std.DHashMap.get?_insert, Ne.symm missing.1]
/-- Every current key is overwritten, so its result is independent of copied
foreign cells. Actual constructor/negative receipts belong to these NEW cells. -/
theorem overwriteStorage_current (cells) (first second : DispatchTable G Args Method Result) (key : G)
    (member : key ∈ cells.map Sigma.fst) :
    (overwriteStorage first cells).get? key = (overwriteStorage second cells).get? key := by
  induction cells generalizing first second with
  | nil => simp at member
  | cons cell rest ih =>
    by_cases later : key ∈ rest.map Sigma.fst
    · exact ih _ _ later
    · simp only [List.map_cons, List.mem_cons] at member
      have same : key = cell.1 := member.resolve_right later
      subst key
      rw [overwriteStorage, overwriteStorage_missing _ _ _ later, overwriteStorage,
        overwriteStorage_missing _ _ _ later]
      simp [DispatchTable.get?, DispatchTable.install]
/-- Mask/prune foreign support after all current cells have been reconstructed. -/
def rebuiltLookup (old : DispatchTable G Args Method Result) (cells) (key : G) :=
  if key ∈ cells.map Sigma.fst then (overwriteStorage old cells).get? key else none
/-- Copy, fully overwrite and prune has the same observable lookup as fresh
empty storage. No old certificate or failed partial build can authorize a key. -/
theorem rebuiltLookup_reference (old : DispatchTable G Args Method Result) (cells) (key : G) :
    rebuiltLookup old cells key = rebuiltLookup DispatchTable.empty cells key := by
  by_cases member : key ∈ cells.map Sigma.fst
  · simp only [rebuiltLookup, ite_eq_left member]
    exact overwriteStorage_current cells old DispatchTable.empty key member
  · simp [rebuiltLookup, member]

/-- A copied workspace inherits authority only from the fully reconstructed
reference family, never from the foreign storage it started with. -/
def rebuiltLookup_certified
    (model : Model G Policy Cooked Args Method Result) (policy : Policy) (cooked : Cooked)
    (old : DispatchTable G Args Method Result) (cells)
    (fresh : ∀ key generic, rebuiltLookup DispatchTable.empty cells key = some generic →
      Certified model policy cooked key generic)
    (key : G) (generic) (found : rebuiltLookup old cells key = some generic) :
    Certified model policy cooked key generic := by
  apply fresh key generic
  rw [← rebuiltLookup_reference old cells key]
  exact found
end LeanPoo.Functional.GenericFamily

namespace LeanPoo.Functional.GenericFamily
open Object DispatchExtension
variable {G Policy Cooked : Type} {Args Method Result : G → Type}
variable [DecidableEq G] [BEq G] [LawfulBEq G] [Hashable G]
variable (model : Model G Policy Cooked Args Method Result) (policy : Policy) (cooked : Cooked)
/-- Run the existing checked constructor in order over private empty storage.
Registration and negative failures abort immediately; no partial table is published. -/
def Partial.rebuild (prior : Partial model policy cooked) : List G → Except (Failure model) (Partial model policy cooked)
  | [] => .ok prior
  | key :: rest => do
    let next ← prior.build model policy cooked key
    next.rebuild rest
/-- Equivalent lookups give the same constructor branch, negative refusal and
installed observations. Capacity and empty-storage factory identity are unobserved. -/
theorem Partial.build_lookup_eq (first second : Partial model policy cooked)
    (same : ∀ query, first.table.get? query = second.table.get? query) (key query : G) :
    (first.build model policy cooked key).map (fun next => next.table.get? query) =
      (second.build model policy cooked key).map (fun next => next.table.get? query) := by
  have entriesSame : first.table.entries.get? query = second.table.entries.get? query := same query
  unfold Partial.build
  rw [same key]
  split
  · simp [Except.map, same query]
  · split
    · rfl
    · split
      · rfl
      · simp [Except.map, Partial.install, DispatchTable.get?, DispatchTable.install,
          Std.DHashMap.get?_insert, entriesSame]
/-- Arbitrary ordered reconstruction retains the first exact typed failure and
all successful lookup observations, including duplicate-key first installation. -/
theorem Partial.rebuild_lookup_eq (keys : List G) (first second : Partial model policy cooked)
    (same : ∀ query, first.table.get? query = second.table.get? query) (query : G) :
    (first.rebuild model policy cooked keys).map (fun next => next.table.get? query) =
      (second.rebuild model policy cooked keys).map (fun next => next.table.get? query) := by
  induction keys generalizing first second with
  | nil => simp [rebuild, Except.map, same query]
  | cons key rest ih =>
    have step := Partial.build_lookup_eq model policy cooked first second same key key
    cases left : first.build model policy cooked key with
    | error error =>
      cases right : second.build model policy cooked key with
      | error other =>
        simp [left, right, Except.map] at step
        simp [rebuild, left, right, step, Except.map, bind, Except.bind, pure, Except.pure]
      | ok next => simp [left, right, Except.map] at step
    | ok next =>
      cases right : second.build model policy cooked key with
      | error error => simp [left, right, Except.map] at step
      | ok after =>
        have related : ∀ q, next.table.get? q = after.table.get? q := by
          intro q
          have observation := Partial.build_lookup_eq model policy cooked first second same key q
          simpa [left, right, Except.map] using observation
        simpa [rebuild, left, right, Except.map, bind, Except.bind, pure, Except.pure] using ih next after related
/-- A native same-kind EMPTY factory is modeled by emptyWithCapacity. Its fresh
checked reconstruction agrees with the existing empty reference for every key;
no certificate can come from the factory's source descriptor or old family. -/
theorem Partial.rebuild_empty_reference (capacity : Nat) (keys : List G) (query : G) :
    ((Partial.emptyWithCapacity model policy cooked capacity).rebuild model policy cooked keys).map
        (fun next => next.table.get? query) =
      ((Partial.empty model policy cooked).rebuild model policy cooked keys).map
        (fun next => next.table.get? query) := by
  apply Partial.rebuild_lookup_eq
  intro key
  simp [Partial.emptyWithCapacity, Partial.empty, DispatchTable.get?, DispatchTable.empty]
end LeanPoo.Functional.GenericFamily

