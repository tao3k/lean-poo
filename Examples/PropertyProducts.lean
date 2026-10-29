import LeanPoo.Functional.PropertyProducts

/-! Parent-owner, field-refusal and empty-product observation controls. -/
open LeanPoo.Functional.PropertyTesting

example : guardedProduct (fun epoch : Nat => epoch == 0)
    [(fun _ => (.ok (2, 1) : Except String (Nat × Nat))),
     (fun _ => .error "later field must not run")]
    (fun values state => .ok (values.sum, state)) 0 = .error none := rfl

example : guardedProduct (fun epoch : Nat => epoch == 0)
    ([] : List (Nat → Except String (Nat × Nat)))
    (fun _ _ => .error "packing must not run") 1 =
      (.error none : Except (Option String) (Nat × Nat)) := rfl

example : guardedProduct (fun _ : Nat => true)
    [(fun _ => (.ok (2, 0) : Except String (Nat × Nat))), (fun _ => .ok (3, 0))]
    (fun values state => .ok (values.sum, state)) 0 = .ok (5, 0) := rfl

example : guardedProduct (fun _ : Nat => true) ([] : List (Nat → Except String (Nat × Nat)))
    (fun _ _ => .error "original packing cause") 0 =
      (.error (some "original packing cause") : Except (Option String) (Nat × Nat)) := rfl
