import LeanPoo.Functional.PropertySizes

open LeanPoo.Functional.PropertyTesting

-- A retained value/seed is identical under nested resize and scale delegation.
example : resizeDraw (scaleDraw (scaleDraw (fun seed size : Nat => (size, seed))
    (· + 1)) (· * 2)) 3 17 99 = (7, 17) := rfl

-- A scaler that retires the revision prevents the dependent draw entirely.
example : guardedSize (fun epoch : Nat => epoch == 0)
    (fun _ _ => (.ok (4, 1) : Except String (Nat × Nat)))
    (fun _ _ => (.error "draw must not run" : Except String (Nat × Nat)))
    8 0 = .error none := rfl

-- The same source revision does not mask an original scale exception.
example : guardedSize (fun epoch : Nat => epoch == 0)
    (fun _ _ => (.error "scale cause" : Except String (Nat × Nat)))
    (fun _ _ => (.error "draw cause" : Except String (Nat × Nat)))
    8 0 = .error (some "scale cause") := rfl

-- Size zero still needs the mandatory element; it does not erase that owner.
example : collectionWidth 1 0 = 1 := rfl
example : guardedGeneration
    (fun epoch : Nat => (collectionSources 1 [0]).all (fun _ => epoch == 0))
    (fun _ => (.error "length draw must not run" : Except String (Nat × Nat)))
    1 = .error none := rfl

-- Optional empty selection adds no source authority from an unused element.
example : (collectionSources 0 [0]).all (fun _ => false) = true := rfl
