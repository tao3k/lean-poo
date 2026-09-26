import LeanPoo.Proof.Invalidation

/-!
Independent proof objects can be assembled through disjoint, typed keys.
Each obligation retains its original dependency footprint on its own side.
-/

namespace LeanPoo.Proof

universe u v w

def SumValue {Left : Type u} {Right : Type w}
    (left : Left → Type v) (right : Right → Type v) :
    Sum Left Right → Type v
  | .inl key => left key
  | .inr key => right key

def State.pair {Left : Type u} {Right : Type w}
    {LeftValue : Left → Type v} {RightValue : Right → Type v}
    (left : State Left LeftValue) (right : State Right RightValue) :
    State (Sum Left Right) (SumValue LeftValue RightValue)
  | .inl key => left key
  | .inr key => right key

def Obligation.left {Left : Type u} {Right : Type w}
    {LeftValue : Left → Type v} {RightValue : Right → Type v}
    (obligation : Obligation Left LeftValue) :
    Obligation (Sum Left Right) (SumValue LeftValue RightValue) where
  dependencies := obligation.dependencies.map Sum.inl
  holds := fun state => obligation.holds (fun key => state (.inl key))
  stable := by
    intro before after equal holds
    apply obligation.stable (fun key => before (.inl key))
      (fun key => after (.inl key))
    · intro key dependency
      exact equal (.inl key) (List.mem_map.mpr ⟨key, dependency, rfl⟩)
    · exact holds

def Obligation.right {Left : Type u} {Right : Type w}
    {LeftValue : Left → Type v} {RightValue : Right → Type v}
    (obligation : Obligation Right RightValue) :
    Obligation (Sum Left Right) (SumValue LeftValue RightValue) where
  dependencies := obligation.dependencies.map Sum.inr
  holds := fun state => obligation.holds (fun key => state (.inr key))
  stable := by
    intro before after equal holds
    apply obligation.stable (fun key => before (.inr key))
      (fun key => after (.inr key))
    · intro key dependency
      exact equal (.inr key) (List.mem_map.mpr ⟨key, dependency, rfl⟩)
    · exact holds

def ProofObject.pair {Left : Type u} {Right : Type w}
    {LeftValue : Left → Type v} {RightValue : Right → Type v}
    (left : ProofObject Left LeftValue) (right : ProofObject Right RightValue) :
    ProofObject (Sum Left Right) (SumValue LeftValue RightValue) where
  state := State.pair left.state right.state
  obligations := left.obligations.map Obligation.left ++
    right.obligations.map Obligation.right

theorem Certificate.pair {Left : Type u} {Right : Type w}
    {LeftValue : Left → Type v} {RightValue : Right → Type v}
    (left : ProofObject Left LeftValue) (right : ProofObject Right RightValue)
    (leftCertificate : Certificate left)
    (rightCertificate : Certificate right) :
    Certificate (left.pair right) := by
  intro obligation membership
  rcases List.mem_append.mp membership with fromLeft | fromRight
  · obtain ⟨source, owned, rfl⟩ := List.mem_map.mp fromLeft
    exact leftCertificate source owned
  · obtain ⟨source, owned, rfl⟩ := List.mem_map.mp fromRight
    exact rightCertificate source owned

/-- Lift a patch without touching the independent right-hand component. -/
def Patch.left {Left : Type u} {Right : Type w}
    {LeftValue : Left → Type v} {RightValue : Right → Type v}
    (patch : Patch Left LeftValue) :
    Patch (Sum Left Right) (SumValue LeftValue RightValue) where
  apply := fun state key =>
    match key with
    | .inl left => patch.apply (fun query => state (.inl query)) left
    | .inr right => state (.inr right)
  touched := patch.touched.map Sum.inl
  frame := by
    intro state key untouched
    cases key with
    | inl left =>
        apply patch.frame
        intro touched
        exact untouched (List.mem_map.mpr ⟨left, touched, rfl⟩)
    | inr right => rfl
  obligations := patch.obligations.map Obligation.left

/-- Lift a patch without touching the independent left-hand component. -/
def Patch.right {Left : Type u} {Right : Type w}
    {LeftValue : Left → Type v} {RightValue : Right → Type v}
    (patch : Patch Right RightValue) :
    Patch (Sum Left Right) (SumValue LeftValue RightValue) where
  apply := fun state key =>
    match key with
    | .inl left => state (.inl left)
    | .inr right => patch.apply (fun query => state (.inr query)) right
  touched := patch.touched.map Sum.inr
  frame := by
    intro state key untouched
    cases key with
    | inl left => rfl
    | inr right =>
        apply patch.frame
        intro touched
        exact untouched (List.mem_map.mpr ⟨right, touched, rfl⟩)
  obligations := patch.obligations.map Obligation.right

theorem Obligation.right_unaffected_left
    {Left : Type u} {Right : Type w}
    {LeftValue : Left → Type v} {RightValue : Right → Type v}
    (obligation : Obligation Right RightValue)
    (patch : Patch Left LeftValue) :
    unaffected obligation.right patch.left := by
  intro key dependency touched
  obtain ⟨source, _, rfl⟩ := List.mem_map.mp dependency
  simp [Patch.left] at touched

theorem Obligation.left_unaffected_right
    {Left : Type u} {Right : Type w}
    {LeftValue : Left → Type v} {RightValue : Right → Type v}
    (obligation : Obligation Left LeftValue)
    (patch : Patch Right RightValue) :
    unaffected obligation.left patch.right := by
  intro key dependency touched
  obtain ⟨source, _, rfl⟩ := List.mem_map.mp dependency
  simp [Patch.right] at touched

end LeanPoo.Proof
