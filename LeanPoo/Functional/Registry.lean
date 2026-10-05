import LeanPoo.Functional.Relabeling
import Std.Data.HashMap.Lemmas

/-! Retain whole provider functions in a hash registry after explicit graph
relabeling. The registry is scoped to one verified source ancestor order. -/
namespace LeanPoo.Functional
universe u v w
variable {Context : Type u} {Key : Type v} {Value : Context → Key → Type w}
variable {graph other : C4.Graph}

/-- Named provider functions retained without invoking their factories. -/
structure ProviderRegistry (Context : Type u) (Key : Type v) (Value : Context → Key → Type w) where
  entries : Std.HashMap String (Provider Context Key Value)

/-- One hash query returns the stored provider function. Unknown names provide
no capabilities. Retain the returned provider or prepare factories for reuse. -/
def ProviderRegistry.dictionary (registry : ProviderRegistry Context Key Value)
    (name : String) : Provider Context Key Value :=
  match registry.entries[name]? with
  | some provider => provider
  | none => fun _ => none

private def register (rename : String → String)
    (providers : String → Provider Context Key Value)
    (table : Std.HashMap String (Provider Context Key Value)) (name : String) :=
  table.insert (rename name) (providers name)

private theorem registered (rename : String → String) (injective : Function.Injective rename)
    (providers : String → Provider Context Key Value) (names : List String)
    (table : Std.HashMap String (Provider Context Key Value)) (name : String) :
    (names.foldl (register rename providers) table)[rename name]? =
      if name ∈ names then some (providers name) else table[rename name]? := by
  induction names generalizing table with
  | nil => simp
  | cons head rest ih =>
    rw [List.foldl_cons, ih]
    by_cases present : name ∈ rest
    · simp [present]
    · by_cases same : head = name
      · subst head
        simp [present, register]
      · have different : rename head ≠ rename name := fun equal => same (injective equal)
        simp [present, Ne.symm same, register, Std.HashMap.getElem?_insert, different]

private theorem registered_absent (rename : String → String)
    (providers : String → Provider Context Key Value) (names : List String)
    (table : Std.HashMap String (Provider Context Key Value)) (target : String)
    (missing : ∀ name ∈ names, rename name ≠ target) :
    (names.foldl (register rename providers) table)[target]? = table[target]? := by
  induction names generalizing table with
  | nil => rfl
  | cons head rest ih =>
    rw [List.foldl_cons, ih _ (fun name member => missing name (by simp [member]))]
    simp [register, Std.HashMap.getElem?_insert, missing head (by simp)]

/-- Retain whole providers over an explicit name scope. Duplicate source names
store the same provider again; lookup preservation requires an injective map. -/
def ProviderRegistry.ofNames (names : List String) (rename : String → String)
    (providers : String → Provider Context Key Value) : ProviderRegistry Context Key Value :=
  ⟨names.foldl (register rename providers) {}⟩

theorem ProviderRegistry.ofNames_lookup (names : List String) (rename : String → String)
    (injective : Function.Injective rename) (providers : String → Provider Context Key Value)
    (member : name ∈ names) :
    (ofNames names rename providers).entries[rename name]? = some (providers name) := by
  rw [ofNames, registered rename injective]
  simp [member]

theorem ProviderRegistry.ofNames_missing (names : List String) (rename : String → String)
    (providers : String → Provider Context Key Value)
    (missing : ∀ name ∈ names, rename name ≠ target) :
    (ofNames names rename providers).dictionary target key = none := by
  have absent := registered_absent rename providers names
    ({} : Std.HashMap String (Provider Context Key Value)) target missing
  simp [ofNames, dictionary, absent]

/-- Build once from all original ancestors, including the root. Each node stores
its whole provider function under the mapped name; no capability enumeration,
context, inverse name map or factory invocation is needed. -/
def ProviderRegistry.relabel (order : C4.VerifiedOrder graph root)
    (change : graph.Relabeling other) (providers : String → Provider Context Key Value) :
    ProviderRegistry Context Key Value :=
  ofNames order.output change.rename providers

/-- Automatic exact provider alignment on every original ancestor. -/
theorem ProviderRegistry.relabel_lookup (order : C4.VerifiedOrder graph root)
    (change : graph.Relabeling other) (providers : String → Provider Context Key Value)
    (ancestor : C4.Ancestor graph name root) :
    (relabel order change providers).entries[change.rename name]? = some (providers name) := by
  exact ofNames_lookup order.output change.rename change.injective providers (order.covers.mpr ancestor)

/-- The public dictionary returns the original entire provider, not only one key. -/
theorem ProviderRegistry.relabel_aligned (order : C4.VerifiedOrder graph root)
    (change : graph.Relabeling other) (providers : String → Provider Context Key Value)
    (ancestor : C4.Ancestor graph name root) :
    (relabel order change providers).dictionary (change.rename name) = providers name := by
  simp [dictionary, relabel_lookup order change providers ancestor]

/-- Names outside the mapped ancestor scope remain absent, even if the original
application dictionary contains other unrelated providers. -/
theorem ProviderRegistry.relabel_missing (order : C4.VerifiedOrder graph root)
    (change : graph.Relabeling other) (providers : String → Provider Context Key Value)
    (missing : ∀ name, C4.Ancestor graph name root → change.rename name ≠ target) :
    (relabel order change providers).dictionary target key = none := by
  exact ofNames_missing order.output change.rename providers
    (fun name member => missing name (order.covers.mp member))

/-- Migrate capability selection with the automatically aligned cached registry. -/
theorem assemble_relabel_registry (order : C4.VerifiedOrder graph root)
    (change : graph.Relabeling other) (unique : (graph.nodes.map C4.Node.name).Nodup)
    (providers : String → Provider Context Key Value) (key : Key) :
    assemble (order.relabel change unique) (ProviderRegistry.relabel order change providers).dictionary key =
      assemble order providers key := by
  apply assemble_relabel
  intro name ancestor
  exact congrFun (ProviderRegistry.relabel_aligned order change providers ancestor) key

/-- One checklist, with no handwritten mapped dictionary or alignment premise.
Success functions and the first missing capability are exactly preserved. -/
theorem Requirements.prepare_relabel_registry (order : C4.VerifiedOrder graph root)
    (change : graph.Relabeling other) (unique : (graph.nodes.map C4.Node.name).Nodup)
    (providers : String → Provider Context Key Value) (keys : List Key) :
    prepare (assemble (order.relabel change unique)
      (ProviderRegistry.relabel order change providers).dictionary) keys =
      prepare (assemble order providers) keys := by
  apply prepare_congr
  intro key _
  exact assemble_relabel_registry order change unique providers key

end LeanPoo.Functional
