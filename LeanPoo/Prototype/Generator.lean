import LeanPoo.Prototype.Compose

/-!
Lean encoding of the generator construction in section 1.2 of POOF.
The generator keeps the final self open; applying a prototype supplies its
inherited computation from another generator.
-/

namespace LeanPoo.Prototype

universe u v w

/-- An open computation from final self to a result. -/
abbrev Generator (Self : Type u) (Result : Type v) := Self → Result

/-- Fix a prototype's inherited input to obtain a generator. -/
def Generator.ofProto (prototype : Proto Self Parent Result)
    (base : Parent) : Generator Self Result :=
  fun self => prototype self base

/-- Apply a prototype to the inherited result computed by a generator. -/
def Generator.applyProto (prototype : Proto Self Middle Result)
    (inherited : Generator Self Middle) : Generator Self Result :=
  fun self => prototype self (inherited self)

/-- Generator application implements the same child-parent composition. -/
theorem Generator.applyProto_ofProto
    (child : Proto Self Middle Result)
    (parent : Proto Self Parent Middle) (base : Parent) :
    Generator.applyProto child (Generator.ofProto parent base) =
      Generator.ofProto (compose child parent) base := by
  rfl

/-- A function-valued generator can tie its own open-recursive knot. -/
unsafe def Generator.instantiate {Input Output : Type}
    (generator : Generator (FixedFunction Input Output)
      (FixedFunction Input Output)) :
    FixedFunction Input Output :=
  Prototype.instantiate (fun self _ => generator self) ()

end LeanPoo.Prototype
