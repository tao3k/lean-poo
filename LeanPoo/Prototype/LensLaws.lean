import LeanPoo.Prototype.SkewLens

/-! Universal laws for the native getter/setter lens interface. Finite native
controls are counterexample checks, not imported proofs of these hypotheses. -/
namespace LeanPoo.Prototype
/-- The standard get-put, put-get and put-put laws for arbitrary custom lenses. -/
structure LensLaws {S A : Type} (get : S → A) (put : A → S → S) : Prop where
  get_put : ∀ source, put (get source) source = source
  put_get : ∀ source value, get (put value source) = value
  put_put : ∀ source first second, put second (put first source) = put second source
/-- Identity getter/setter is lawful for every carrier, including procedures. -/
theorem LensLaws.identity : LensLaws (id : S → S) (fun value _ => value) := ⟨fun _ => rfl,fun _ _ => rfl,fun _ _ _ => rfl⟩
/-- Custom lawful getters/setters compose in the SAME order as native Lens.compose. -/
theorem LensLaws.compose {S A B : Type} {getOuter : S → A} {putOuter : A → S → S}
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
theorem LensLaws.modify_get {S A : Type} {get : S → A} {put : A → S → S}
    (laws : LensLaws get put) (source : S) (value : A) :
    (MonoLens.ofGetSet get put).view ((MonoLens.ofGetSet get put).modify (fun _ => value) source) = value :=
  laws.put_get source value
/-- Replacing a focus with its current view cannot destroy an independent frame. -/
theorem LensLaws.noop {S A : Type} {get : S → A} {put : A → S → S}
    (laws : LensLaws get put) (source : S) :
    (MonoLens.ofGetSet get put).modify (fun _ => get source) source = source := laws.get_put source
end LeanPoo.Prototype
