import LeanPoo.Prototype.Compose

/-!
The paper's skew lens separates the context being viewed from the extension
being updated. Lean functions represent both parts directly, including the
case where an update changes types.
-/

namespace LeanPoo.Prototype

universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉

/-- A view `S → R` and a focus for extensions `(I → P) → J → Q`. -/
structure SkewLens (I : Type u₁) (R : Type u₂) (P : Type u₃)
    (J : Type u₄) (S : Type u₅) (Q : Type u₆) where
  view : S → R
  update : (I → P) → J → Q

/-- Identity focus on both the viewed context and the extension. -/
def SkewLens.id (I : Type u₁) (R : Type u₂) (P : Type u₃) :
    SkewLens I R P I R P :=
  ⟨fun context => context, fun extension => extension⟩

/-- Focus an outer skew lens through an inner skew lens. -/
def SkewLens.compose
    (outer : SkewLens J S Q K T U)
    (inner : SkewLens I R P J S Q) :
    SkewLens I R P K T U :=
  ⟨inner.view ∘ outer.view, outer.update ∘ inner.update⟩

/-- The paper's `skew-ext`: move an open extension to a wider context. -/
def SkewLens.focus (lens : SkewLens I R P J S Q)
    (extension : Proto R I P) : Proto S J Q :=
  fun self inherited =>
    lens.update (fun innerInherited =>
      extension (lens.view self) innerInherited) inherited

theorem SkewLens.id_focus (extension : Proto R I P) :
    (SkewLens.id I R P).focus extension = extension := by
  funext self inherited
  rfl

/-- Focusing through composed lenses agrees with successive focusing. -/
theorem SkewLens.focus_compose
    (outer : SkewLens J S Q K T U)
    (inner : SkewLens I R P J S Q)
    (extension : Proto R I P) :
    (outer.compose inner).focus extension =
      outer.focus (inner.focus extension) := by
  funext self inherited
  rfl

theorem SkewLens.compose_id_left (lens : SkewLens I R P J S Q) :
    (SkewLens.id J S Q).compose lens = lens := by
  cases lens
  rfl

theorem SkewLens.compose_id_right (lens : SkewLens I R P J S Q) :
    lens.compose (SkewLens.id I R P) = lens := by
  cases lens
  rfl

theorem SkewLens.compose_assoc
    (outer : SkewLens K T U L V W)
    (middle : SkewLens J S Q K T U)
    (inner : SkewLens I R P J S Q) :
    (outer.compose middle).compose inner =
      outer.compose (middle.compose inner) := by
  cases outer
  cases middle
  cases inner
  rfl

/-- A focus that changes only the extension, retaining the viewed context. -/
def SkewLens.updateOnly (R : Type u₂)
    (update : (I → P) → J → Q) : SkewLens I R P J R Q :=
  ⟨fun context => context, update⟩

/-- Refine the extension focus without changing what the method can read. -/
def SkewLens.refocusUpdate (lens : SkewLens I R P J S Q)
    (update : (II → PP) → I → P) : SkewLens II R PP J S Q :=
  lens.compose (SkewLens.updateOnly R update)

theorem SkewLens.refocusUpdate_view
    (lens : SkewLens I R P J S Q)
    (update : (II → PP) → I → P) :
    (lens.refocusUpdate update).view = lens.view := rfl

/-- The familiar monomorphic lens is a special case of a skew lens. -/
abbrev MonoLens (S : Type u₁) (A : Type u₂) :=
  SkewLens A A A S S S

/-- Build a monomorphic focus from ordinary Lean getter and setter functions. -/
def MonoLens.ofGetSet (get : S → A) (set : A → S → S) : MonoLens S A :=
  ⟨get, fun change source => set (change (get source)) source⟩

/-- Apply a local change to the focused part of a whole value. -/
def MonoLens.modify (lens : MonoLens S A) (change : A → A) (source : S) : S :=
  lens.update change source

end LeanPoo.Prototype
