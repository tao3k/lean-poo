import LeanPoo.Prototype.SkewLens

/-! Universal laws for the native getter/setter lens interface. Finite native
controls are counterexample checks, not imported proofs of these hypotheses. -/
namespace LeanPoo.Prototype
universe u v w
/-- The standard get-put, put-get and put-put laws for arbitrary custom lenses. -/
structure LensLaws {S : Type u} {A : Type v} (get : S → A) (put : A → S → S) : Prop where
  get_put : ∀ source, put (get source) source = source
  put_get : ∀ source value, get (put value source) = value
  put_put : ∀ source first second, put second (put first source) = put second source
/-- Identity getter/setter is lawful for every carrier, including procedures. -/
theorem LensLaws.identity {S : Type u} : LensLaws (id : S → S) (fun value _ => value) := ⟨fun _ => rfl,fun _ _ => rfl,fun _ _ _ => rfl⟩
/-- Custom lawful getters/setters compose in the SAME order as native Lens.compose. -/
theorem LensLaws.compose {S : Type u} {A : Type v} {B : Type w} {getOuter : S → A} {putOuter : A → S → S}
    {getInner : A → B} {putInner : B → A → A}
    (outer : LensLaws getOuter putOuter) (inner : LensLaws getInner putInner) :
    LensLaws (fun source => getInner (getOuter source))
      (fun value source => putOuter (putInner value (getOuter source)) source) := by
  constructor
  · intro source
    rw [inner.get_put, outer.get_put]
  · intro source value
    rw [outer.put_get, inner.put_get]
  · intro source first second
    rw [outer.put_get, inner.put_put, outer.put_put]
/-- Existing MonoLens.ofGetSet preserves the proved custom setter's view law. -/
theorem LensLaws.modify_get {S : Type u} {A : Type v} {get : S → A} {put : A → S → S}
    (laws : LensLaws get put) (source : S) (value : A) :
    (MonoLens.ofGetSet get put).view ((MonoLens.ofGetSet get put).modify (fun _ => value) source) = value :=
  laws.put_get source value
/-- Replacing a focus with its current view cannot destroy an independent frame. -/
theorem LensLaws.noop {S : Type u} {A : Type v} {get : S → A} {put : A → S → S}
    (laws : LensLaws get put) (source : S) :
    (MonoLens.ofGetSet get put).modify (fun _ => get source) source = source := laws.get_put source
/-- Independence is an ADDITIONAL premise: individual lawful lenses may overlap.
The two cross-view laws preserve observations; the last law permits reordering. -/
structure LensIndependent {S : Type u} {A : Type v} {B : Type w} (leftGet : S → A) (leftPut : A → S → S)
    (rightGet : S → B) (rightPut : B → S → S) : Prop where
  left_view : ∀ source value, leftGet (rightPut value source) = leftGet source
  right_view : ∀ source value, rightGet (leftPut value source) = rightGet source
  commute : ∀ source left right, leftPut left (rightPut right source) = rightPut right (leftPut left source)
/-- Independence can be used in either ordering of the same two custom lenses. -/
theorem LensIndependent.symm {S : Type u} {A : Type v} {B : Type w} {lg : S → A} {lp : A → S → S}
    {rg : S → B} {rp : B → S → S} (h : LensIndependent lg lp rg rp) :
    LensIndependent rg rp lg lp := ⟨h.right_view,h.left_view,fun s b a => (h.commute s a b).symm⟩
/-- Independent lawful foci assemble a lawful product focus; no inference from
labels, distinct paths or finite runtime checks is needed by this proof. -/
theorem LensLaws.pair {S : Type u} {A : Type v} {B : Type w} {lg : S → A} {lp : A → S → S}
    {rg : S → B} {rp : B → S → S} (left : LensLaws lg lp) (right : LensLaws rg rp)
    (apart : LensIndependent lg lp rg rp) :
    LensLaws (fun source => (lg source,rg source))
      (fun value source => rp value.2 (lp value.1 source)) := by
  constructor
  · intro source
    rw [left.get_put, right.get_put]
  · intro source value
    simp only [apart.left_view, left.put_get, right.put_get]
  · intro source first second
    rw [apart.commute, right.put_put, left.put_put]
end LeanPoo.Prototype
