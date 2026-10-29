import LeanPoo.Functional.PropertyFilters

/-! Finite retry history, exact budgets, acceptance and callback refusal. -/
open LeanPoo.Functional.PropertyTesting

-- The first rejected branch owns source 0; the second draw changes its epoch.
example : filterTrials (fun epoch source : Nat => source != 0 || epoch == 0) "exhausted"
    (fun owned epoch =>
      if owned.isEmpty then .ok ((0, [0]), epoch) else .ok ((4, []), 1))
    (fun value epoch => .ok (value > 0, epoch)) 2 [] 0 =
      (.error none, 2) := rfl

-- Stable rejection spends exactly the two available entries, with no third draw.
example : filterTrials (fun _ _ : Nat => true) "exhausted"
    (fun _ state => .ok ((0, [1]), state))
    (fun _ state => .ok (false, state)) 2 [] 0 =
      (.error (some "exhausted"), 2) := rfl

-- Acceptance preserves the value and state and does not spend unused entries.
example : filterTrials (fun _ _ : Nat => true) "exhausted"
    (fun _ state => .ok ((4, [1]), state))
    (fun _ state => .ok (true, state)) 5 [] 0 =
      (.ok (4, 0), 1) := rfl

-- History inherited by a nested pipeline suppresses its later mapper after revision.
example : guardedStages (fun epoch : Nat => (mergeSources [0] [1]).all
    (fun source => source != 0 || epoch == 0))
    [(fun _ => (.ok (4, 1) : Except String (Nat × Nat))),
     (fun _ => .error "mapper must not run")] 0 = .error none := rfl
