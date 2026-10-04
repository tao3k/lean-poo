import LeanPoo.Functional.Assembly

/-! Prepare a caller's typed capability list once, then apply the retained
factories at many contexts. Result types retain the same keys and contexts. -/
namespace LeanPoo.Functional.Requirements

universe u v w
variable {Context : Type u} {Key : Type v} {Value : Context → Key → Type w}

/-- A heterogeneous tuple of retained functions, indexed by the requested keys. -/
def Factories (Context : Type u) (Value : Context → Key → Type w) : List Key → Type (max u w)
  | [] => PUnit
  | key :: rest => Factory Context (fun context => Value context key) × Factories Context Value rest

/-- Results at exactly one supplied context and the same requested keys. -/
def Results (Value : Context → Key → Type w) (context : Context) : List Key → Type w
  | [] => PUnit
  | key :: rest => Value context key × Results Value context rest

/-- Request in caller order. Return the first missing key before any factory
is invoked, or a complete tuple of functions. Empty and repeated lists work. -/
def prepare (provider : Provider Context Key Value) :
    (keys : List Key) → Except Key (Factories Context Value keys)
  | [] => .ok PUnit.unit
  | key :: rest =>
    match provider key with
    | none => .error key
    | some factory => match prepare provider rest with
      | .error missing => .error missing
      | .ok tail => .ok (factory, tail)

/-- Apply retained functions directly, adding no graph compilation or provider
lookup of its own. The supplied factory bodies keep their own behavior. -/
def build : {keys : List Key} → Factories Context Value keys →
    Factory Context (fun context => Results Value context keys)
  | [], _, _ => PUnit.unit
  | _ :: _, (factory, tail), context => (factory context, build tail context)

/-- Every retained function is exactly the one selected by the provider. -/
def Selected (provider : Provider Context Key Value) :
    (keys : List Key) → Factories Context Value keys → Prop
  | [], _ => True
  | key :: rest, (factory, tail) => provider key = some factory ∧ Selected provider rest tail

/-- Success is equivalent to selecting the complete requested tuple. This
kernel contract supports arbitrary heterogeneous result families. -/
theorem prepare_ok_iff (provider : Provider Context Key Value) (keys : List Key)
    (factories : Factories Context Value keys) :
    prepare provider keys = .ok factories ↔ Selected provider keys factories := by
  induction keys with
  | nil => cases factories; simp [prepare, Selected]
  | cons key rest ih =>
    rcases factories with ⟨factory, tail⟩
    cases first : provider key with
    | none => simp [prepare, Selected, first]
    | some actual =>
      cases remaining : prepare provider rest with
      | error missing =>
        have absent : ¬ Selected provider rest tail := by
          rw [← ih tail, remaining]
          simp
        simp [prepare, Selected, first, remaining, absent]
      | ok retained =>
        have exactTail : retained = tail ↔ Selected provider rest tail := by
          simpa [remaining] using ih tail
        simp only [prepare, first, remaining, Selected, Option.some.injEq, ← exactTail]
        constructor
        · intro same
          injection same with pair
          exact Prod.mk.inj pair
        · rintro ⟨rfl, rfl⟩
          rfl

/-- Every requested key has a selected factory after successful preparation. -/
theorem Selected.available (provider : Provider Context Key Value) (keys : List Key)
    (factories : Factories Context Value keys) :
    Selected provider keys factories → ∀ key ∈ keys,
      ∃ factory, provider key = some factory := by
  induction keys with
  | nil => simp
  | cons head rest ih =>
    rcases factories with ⟨factory, tail⟩
    rintro ⟨first, remaining⟩ key member
    rcases List.mem_cons.mp member with same | member
    · subst key
      exact ⟨factory, first⟩
    · exact ih tail remaining key member

/-- Prepared requirements selected through C4 retain original-graph provenance
for every requested capability, including repeated requests. -/
theorem prepare_origin (order : C4.VerifiedOrder graph root)
    (providers : String → Provider Context Key Value) (keys : List Key)
    (factories : Factories Context Value keys)
    (ready : prepare (assemble order providers) keys = .ok factories)
    (key : Key) (requested : key ∈ keys) :
    ∃ name, C4.Ancestor graph name root ∧
      ∃ factory, providers name key = some factory := by
  obtain ⟨factory, selected⟩ := Selected.available _ _ _
    ((prepare_ok_iff _ _ _).mp ready) key requested
  obtain ⟨name, ancestor, source⟩ := assemble_origin selected
  exact ⟨name, ancestor, factory, source⟩

/-- A missing first capability is reported without examining the tail. -/
theorem prepare_missing_head (provider : Provider Context Key Value) (key : Key)
    (rest : List Key) (absent : provider key = none) :
    prepare provider (key :: rest) = .error key := by
  simp [prepare, absent]

end LeanPoo.Functional.Requirements
