import LeanPoo.Functional.PropertySequences

open LeanPoo.Functional.PropertyTesting

-- Malformed input cannot authorize a repaired prefix or initialization.
example : finiteSequenceInput "shape" (Value := Nat) none
    (fun _ => (.error (some "initializer") : Except (Option String) (List Nat))) =
      .error (some "shape") := rfl

-- A normal source revision wins before malformed-result admission.
example : finiteShrinkStage (fun epoch : Nat => epoch == 0) "shape"
    (fun _ _ => (.ok (none, 1) : Except String (Option (List Bool) × Nat)))
    () 0 = .error none := rfl

-- An intact callback's malformed spine never publishes its apparent head.
example : finiteShrinkStage (fun _ : Nat => true) "shape"
    (fun _ state => (.ok (none, state) : Except String (Option (List Bool) × Nat)))
    () 0 = .error (some "shape") := rfl

-- Empty and false-containing lists remain valid finite data.
example : finiteShrinkStage (fun _ : Nat => true) "shape"
    (fun _ state => (.ok (some [false, true], state) : Except String (Option (List Bool) × Nat)))
    () 0 = .ok ([false, true], 0) := rfl
