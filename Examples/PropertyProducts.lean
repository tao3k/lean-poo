import LeanPoo.Functional.PropertyProducts

/-! Parent-owner, field-refusal and empty-product observation controls. -/
open LeanPoo.Functional.PropertyTesting

-- Two Map entries contribute cardinality two and natural weights two and three.
example : guardedMeasure (fun _ : Nat => true) 2
    [(fun state => (.ok (2, state) : Except String (Nat × Nat))),
     (fun state => .ok (3, state))] 0 = .ok (7, 0) := rfl

-- The second callback and aggregate total are unavailable after the first revision.
example : guardedMeasure (fun epoch : Nat => epoch == 0) 2
    [(fun _ => (.ok (2, 1) : Except String (Nat × Nat))),
     (fun _ => .error "later weight must not run")] 0 = .error none := rfl

-- Empty Maps have zero weight without invoking a scalar measure.
example : guardedMeasure (Cause := String) (fun _ : Nat => true) 0 [] 0 = .ok (0, 0) := rfl

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

-- A later field's stale source refuses before the first draw or packing effect.
example : guardedProduct
    (fun epoch : Nat => (productSources [[0], [1]]).all (fun source => source != 1 || epoch == 0))
    [(fun state => (.ok (8, state + 1) : Except String (Nat × Nat))),
     (fun state => .ok (2, state))]
    (fun values state => .ok (values.sum, state)) 1 = .error none := rfl

-- Shared nested fields retain one source identity without changing stable sums.
example : productSources [[0, 1], productSources [[1], [2]]] = [0, 1, 2] := rfl

-- An empty finite function domain has no result producer to observe.
example : (productSources ([] : List (List Nat))).all (fun _ => false) = true := rfl

-- An ordinary bad input must stay false; the next input cannot replace it by an error.
example : guardedAll (fun _ : Nat => true)
    [(fun state => (.ok (false, state) : Except String (Bool × Nat))),
     (fun _ => .error "later input must not run")] 0 = .ok (false, 0) := rfl

-- A predicate that revises its source cannot publish either normal Boolean result.
example : guardedAll (fun epoch : Nat => epoch == 0)
    [(fun _ => (.ok (false, 1) : Except String (Bool × Nat))),
     (fun _ => .error "later input must not run")] 0 = .error none := rfl
