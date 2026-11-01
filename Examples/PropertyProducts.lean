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

-- The parent seed labels each field; the child seed advances the suffix.
example : drawProductRev (fun seed : Nat => (seed + 10, seed + 1))
    (fun field seed : Nat => field + seed) [1, 2, 3] 0 [] = ([11, 13, 15], 3) := rfl

-- An empty product consumes no split and keeps its continuation seed.
example : drawProductRev (fun _ : Nat => (99, 100))
    (fun field seed : Nat => field + seed) [] 7 [] = ([], 7) := rfl

-- Equal payloads do not erase distinct field positions or replay seeds.
example : drawProductRev (fun seed : Nat => (seed, seed + 1))
    (fun _ _ : Nat => 5) [0, 0, 0] 0 [8] = ([8, 5, 5, 5], 3) := rfl

-- A two-field product cannot silently measure one captured field.
example : prepareProductRow "shape" 2 (some [4])
    (fun values => (.ok values.length : Except (Option String) Nat)) = .error (some "shape") := rfl

-- An empty row is data, while malformed input is refused even at width zero.
example : captureProductRow (Value := Bool) 0 (some []) = some [] := rfl
example : captureProductRow (Value := Bool) 0 none = none := rfl
example : captureProductRow 1 (some [false]) = some [false] := rfl

-- Three heterogeneous labels retain their prefix/suffix through each replacement.
example : productCoordinate ["left"] "replacement" ["flag"] = ["left", "replacement", "flag"] := rfl

-- A malformed child batch skips a packer whose execution would raise another cause.
example : finiteProductCoordinate (fun _ : Nat => true) "shape"
    (fun _ state => (.ok (none, state) : Except String (Option (List Nat) × Nat)))
    (fun _ _ => (.error "forbidden pack" : Except String (Nat × Nat))) [] [6] 4 0 =
      .error (some "shape") := rfl

-- Source retirement still takes precedence before a returned child list is packed.
example : finiteProductCoordinate (fun epoch : Nat => epoch == 0) "shape"
    (fun _ _ => (.ok (some [0], 1) : Except String (Option (List Nat) × Nat)))
    (fun _ _ => (.error "forbidden pack" : Except String (Nat × Nat))) [] [6] 4 0 = .error none := rfl

-- Shrinking either parent regenerates only a child satisfying its own length.
example : dependentCandidates [0, 2] (fun count seed => [List.replicate count seed]) 7 =
    [(0, []), (2, [7, 7])] := rfl

-- The assertion boundary receives exactly the shared declaration's receipt.
example : deliverDeclaration (fun seed : Nat => (.ok (seed, [2, 2]) : Except String (Nat × List Nat)))
    (fun receipt => .ok receipt) 42 = .ok (42, [2, 2]) := rfl

-- An invalid first tuple wins before a later row can throw false.
example : prepareFunctionTable (fun _ : Nat => true) true
    (fun row state => (if row = 0 then .ok (none, state) else .error false :
      Except Bool (Option (List Bool) × Nat))) [0, 1] 0 = .error (some true) := rfl
-- A draw's original false exception remains distinct from malformed tuple data.
example : prepareFunctionTable (fun _ : Nat => true) true
    (fun _ _ => (.error false : Except Bool (Option (List Bool) × Nat))) [0, 1] 0 =
      .error (some false) := rfl
-- Retirement after the draw precedes classification of its malformed result.
example : prepareFunctionTable (fun epoch : Nat => epoch == 0) "tuple"
    (fun _ _ => (.ok (none, 1) : Except String (Option (List Bool) × Nat))) [0, 1] 0 =
      .error none := rfl
-- Later producer state cannot rewrite an already captured false return value.
example : prepareFunctionTable (fun _ : Nat => true) "tuple"
    (fun (_ : Nat) (state : Nat) => (.ok (some [state != 0], state + 1) :
      Except String (Option (List Bool) × Nat))) [10, 20] 0 =
      .ok ([(10, [false]), (20, [true])], 2) := rfl
-- A proper empty result tuple delivers zero values, rather than declining a row.
example : prepareFunctionTable (fun _ : Nat => true) "tuple"
    (fun _ state => (.ok (some [], state + 1) : Except String (Option (List Bool) × Nat))) [10] 0 =
      .ok ([(10, [])], 1) := rfl
