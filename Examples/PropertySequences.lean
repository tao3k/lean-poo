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

-- Different operations can share a payload grammar node without sharing labels.
example : eligibleTaggedBranches [("credit", 0), ("debit", 0), ("empty", 1)]
    (fun node => if node = 0 then some 2 else none) 2 = [("credit", 0), ("debit", 0)] := rfl

-- Reducing an amount never changes debit into credit, including at zero.
example : taggedCandidates "debit" [0, 4, 7] = [("debit", 0), ("debit", 4), ("debit", 7)] := rfl

-- An unknown operation cannot run the payload getter's deliberately failing action.
example : inspectTagged [("credit", 0), ("debit", 0)] "retired"
    (fun _ => (.error "payload must remain unread" : Except String Nat))
    (fun _ _ => (.error "inspector must remain unused" : Except String (Option Nat))) = .ok none := rfl

-- Shared grammar nodes still publish the originally selected operation label.
example : inspectTagged [("credit", 0), ("debit", 0)] "debit"
    (fun _ => (.ok 7 : Except String Nat)) (fun _ n => .ok (some (n + 1))) = .ok (some ("debit", 8)) := rfl

-- A distinct keyword carrier preserves empty and reader-sensitive spellings.
private inductive KeywordSpelling where
  | mk : List Nat → KeywordSpelling
private def spellingOf : KeywordSpelling → List Nat
  | .mk text => text
example : spellingCandidates KeywordSpelling.mk (fun _ => [[], [32, 58]]) spellingOf
    (.mk [0, 1114111]) = [.mk [], .mk [32, 58]] := rfl
example : (spellingCandidates KeywordSpelling.mk (fun _ => []) spellingOf (.mk [])).length = 0 := rfl

-- A callback replaces an entire ambient input, but captured coordinates survive.
example : finiteSequenceParameters (fun _ : List Nat => true) "shape"
    (fun value _ => (.ok (some [value], [99]) : Except String (Option (List Nat) × List Nat)))
    [4, 6] [4, 6] = .ok ([[4], [6]], [99]) := rfl

-- A finite malformed second result discards the first prepared batch entirely.
example : finiteSequenceParameters (fun _ : Nat => true) "shape"
    (fun value state => (.ok (if value = 6 then none else some [value], state + 1) :
      Except String (Option (List Nat) × Nat))) [4, 6] 0 = .error (some "shape") := rfl

-- The false payload is data; it is independent of a false thrown cause.
example : finiteSequenceParameters (fun _ : Nat => true) false
    (fun _ state => (.ok (some [false], state + 1) : Except Bool (Option (List Bool) × Nat)))
    [4, 6] 0 = .ok ([[false], [false]], 2) := rfl
example : finiteSequenceParameters (fun _ : Nat => true) true
    (fun value state => (if value = 6 then .error false else .ok (some [value], state + 1) :
      Except Bool (Option (List Nat) × Nat))) [4, 6] 0 = .error (some false) := rfl

-- A changed source skips every later coordinate even if its result is malformed.
example : finiteSequenceParameters (fun epoch : Nat => epoch == 0) "shape"
    (fun _ _ => (.ok (none, 1) : Except String (Option (List Bool) × Nat))) [4, 6] 0 =
      .error none := rfl
