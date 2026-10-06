import LeanPoo.Functional.Overlay
import Std.Data.DHashMap.Lemmas

/-! Retained dependent hash overrides. Keep this state between edits so updates
preserve the original base rather than wrapping the last materialized provider. -/
namespace LeanPoo.Functional
universe u v w
variable {Context : Type u} {Key : Type v} {Value : Context → Key → Type w}
variable [BEq Key] [Hashable Key] [LawfulBEq Key] [DecidableEq Key]

/-- Absence delegates to base; a stored `none` explicitly removes a capability.
Key-dependent factories stay typed in the hash table. -/
structure IndexedOverlay (Context : Type u) (Key : Type v) (Value : Context → Key → Type w)
    [BEq Key] [Hashable Key] where
  base : Provider Context Key Value
  overrides : Std.DHashMap Key (fun key => Option (Factory Context (fun c => Value c key)))

def IndexedOverlay.ofProvider (base : Provider Context Key Value) : IndexedOverlay Context Key Value :=
  ⟨base, ∅⟩

def IndexedOverlay.provider (state : IndexedOverlay Context Key Value) : Provider Context Key Value :=
  fun key => match state.overrides.get? key with
    | none => state.base key
    | some replacement => replacement

/-- One dependent hash insertion; neither base nor factory bodies execute. -/
def IndexedOverlay.set (state : IndexedOverlay Context Key Value) (key : Key)
    (replacement : Option (Factory Context (fun c => Value c key))) : IndexedOverlay Context Key Value :=
  ⟨state.base, state.overrides.insert key replacement⟩

omit [DecidableEq Key] in
@[simp] theorem IndexedOverlay.ofProvider_provider (base : Provider Context Key Value) :
    (ofProvider base).provider = base := by
  funext key
  simp [ofProvider, provider]

omit [LawfulBEq Key] [DecidableEq Key] in
@[simp] theorem IndexedOverlay.set_base (state : IndexedOverlay Context Key Value) (key : Key)
    (replacement : Option (Factory Context (fun c => Value c key))) :
    (state.set key replacement).base = state.base := rfl

theorem IndexedOverlay.set_provider (state : IndexedOverlay Context Key Value) (key : Key)
    (replacement : Option (Factory Context (fun c => Value c key))) :
    (state.set key replacement).provider = state.provider.patchKey key replacement := by
  funext query
  by_cases same : query = key
  · subst query
    simp [set, provider, Provider.patchKey]
  · simp [set, provider, Provider.patchKey, Std.DHashMap.get?_insert, same, Ne.symm same]

/-- Extend retained state in caller order. Repeated keys overwrite their stored
cell, while the original base stays fixed across any number of calls. -/
def IndexedOverlay.extend (state : IndexedOverlay Context Key Value)
    (edits : List (CapabilityEdit Context Key Value)) : IndexedOverlay Context Key Value :=
  edits.foldl (fun state edit => state.set edit.1 edit.2) state

omit [LawfulBEq Key] [DecidableEq Key] in
theorem IndexedOverlay.extend_base (state : IndexedOverlay Context Key Value)
    (edits : List (CapabilityEdit Context Key Value)) : (state.extend edits).base = state.base := by
  induction edits generalizing state with
  | nil => rfl
  | cons edit rest ih => exact (ih (state.set edit.1 edit.2)).trans rfl

theorem IndexedOverlay.extend_provider (state : IndexedOverlay Context Key Value)
    (edits : List (CapabilityEdit Context Key Value)) :
    (state.extend edits).provider =
      edits.foldl (fun provider edit => provider.patchKey edit.1 edit.2) state.provider := by
  induction edits generalizing state with
  | nil => rfl
  | cons edit rest ih =>
    simp only [extend, List.foldl_cons] at *
    rw [ih, set_provider]

omit [LawfulBEq Key] [DecidableEq Key] in
/-- Extending twice and extending the concatenation yield the same retained state. -/
theorem IndexedOverlay.extend_append (state : IndexedOverlay Context Key Value)
    (first second : List (CapabilityEdit Context Key Value)) :
    (state.extend first).extend second = state.extend (first ++ second) := by
  simp [extend, List.foldl_append]

def IndexedOverlay.compile (base : Provider Context Key Value)
    (edits : List (CapabilityEdit Context Key Value)) : IndexedOverlay Context Key Value :=
  (ofProvider base).extend edits

/-- Exact function equality with the existing normalized list implementation. -/
theorem IndexedOverlay.compile_provider (base : Provider Context Key Value)
    (edits : List (CapabilityEdit Context Key Value)) :
    (compile base edits).provider = (ProviderOverlay.compile base edits).provider := by
  rw [compile, extend_provider, ofProvider_provider, ProviderOverlay.compile_provider]

theorem Requirements.prepare_indexed_extend (state : IndexedOverlay Context Key Value)
    (edits : List (CapabilityEdit Context Key Value)) (keys : List Key) :
    prepare (state.extend edits).provider keys =
      prepare (edits.foldl (fun provider edit => provider.patchKey edit.1 edit.2) state.provider) keys := by
  rw [IndexedOverlay.extend_provider]

theorem Requirements.prepare_indexed_compile (base : Provider Context Key Value)
    (edits : List (CapabilityEdit Context Key Value)) (keys : List Key) :
    prepare (IndexedOverlay.compile base edits).provider keys =
      prepare (ProviderOverlay.compile base edits).provider keys := by
  rw [IndexedOverlay.compile_provider]

end LeanPoo.Functional
