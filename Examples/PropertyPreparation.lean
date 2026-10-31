import LeanPoo.Functional.PropertyPreparation

open LeanPoo.Functional.PropertyTesting

-- Retired metadata cannot invoke a deliberately failing later binder.
example : guardedStages (fun epoch : Nat => epoch == 0)
    [(fun _ => (.ok (true, 1) : Except String (Bool × Nat))),
     (fun _ => .error "must not bind")] 0 = .error none := rfl
-- A declining factory cannot escape retirement by choosing the raw path.
example : prepareBridge (fun epoch : Nat => epoch == 0)
    (fun _ => (.ok (none, 1) : Except String (Option Nat × Nat)))
    (fun _ => .error "must not bind") 0 = .error none := rfl
-- False data is a present owned result, not the opt-out sentinel.
example : prepareBridge (fun _ : Nat => true)
    (fun state => (.ok (some false, state) : Except String (Option Bool × Nat)))
    (fun _ => .error "unused raw binder") 0 = .ok (false, 0) := rfl
-- A stable opt-out performs the raw binding at the factory's actual final state.
example : prepareBridge (fun _ : Nat => true)
    (fun _ => (.ok (none, 2) : Except String (Option Nat × Nat)))
    (fun state => .ok (7, state + 1)) 0 = .ok (7, 3) := rfl
-- Original false causes are not stale refusal or missing trees.
example : prepareBridge (fun _ : Nat => true)
    (fun _ => (.error false : Except Bool (Option Nat × Nat)))
    (fun _ => .error true) 0 = .error (some false) := rfl
-- A fresh attempt can bind while the old snapshot still refuses.
example : prepareBridge (fun epoch : Nat => epoch == 1)
    (fun state => (.ok (some 7, state) : Except String (Option Nat × Nat)))
    (fun _ => .error "unused") 1 = .ok (7, 1) := rfl
