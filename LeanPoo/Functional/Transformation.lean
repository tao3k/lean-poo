/-! Total deterministic witness transport with input-indexed results. -/
namespace LeanPoo.Functional.Transformation


universe u v

structure Problem where
  Input : Type u
  Result : Input → Type v
  Valid : Input → Prop
  Correct : (a : Input) → Result a → Prop

structure CertifiedTransformation (A B : Problem.{u, v}) where
  forward : A.Input → B.Input
  preserves : ∀ a, A.Valid a → B.Valid (forward a)
  extract : (a : A.Input) → B.Result (forward a) → A.Result a
  sound : ∀ a, A.Valid a → ∀ r, B.Correct (forward a) r →
    A.Correct a (extract a r)

def identity (A : Problem) : CertifiedTransformation A A where
  forward := id
  preserves := fun _ valid => valid
  extract := fun _ r => r
  sound := fun _ _ _ correct => correct

def compose {A B C : Problem} (f : CertifiedTransformation A B)
    (g : CertifiedTransformation B C) : CertifiedTransformation A C where
  forward := fun a => g.forward (f.forward a)
  preserves := fun a valid => g.preserves _ (f.preserves a valid)
  extract := fun a r => f.extract a (g.extract (f.forward a) r)
  sound := fun a valid r correct =>
    f.sound a valid _ (g.sound _ (f.preserves a valid) r correct)

theorem compose_sound {A B C : Problem} (f : CertifiedTransformation A B)
    (g : CertifiedTransformation B C) (a : A.Input) (valid : A.Valid a)
    (r : C.Result ((compose f g).forward a))
    (correct : C.Correct ((compose f g).forward a) r) :
    A.Correct a ((compose f g).extract a r) :=
  (compose f g).sound a valid r correct

theorem compose_forward_assoc {A B C D : Problem}
    (f : CertifiedTransformation A B) (g : CertifiedTransformation B C)
    (h : CertifiedTransformation C D) (a : A.Input) :
    (compose (compose f g) h).forward a =
      (compose f (compose g h)).forward a := rfl

theorem compose_extract_assoc {A B C D : Problem}
    (f : CertifiedTransformation A B) (g : CertifiedTransformation B C)
    (h : CertifiedTransformation C D) (a : A.Input)
    (r : D.Result (h.forward (g.forward (f.forward a)))) :
    (compose (compose f g) h).extract a r =
      (compose f (compose g h)).extract a r := rfl

theorem identity_extract {A : Problem} (a : A.Input) (r : A.Result a) :
    (identity A).extract a r = r := rfl


@[simp] theorem identity_left {A B : Problem} (f : CertifiedTransformation A B) :
    compose (identity A) f = f := by cases f; rfl

@[simp] theorem identity_right {A B : Problem} (f : CertifiedTransformation A B) :
    compose f (identity B) = f := by cases f; rfl

theorem compose_assoc {A B C D : Problem} (f : CertifiedTransformation A B)
    (g : CertifiedTransformation B C) (h : CertifiedTransformation C D) :
    compose (compose f g) h = compose f (compose g h) := rfl

end LeanPoo.Functional.Transformation
