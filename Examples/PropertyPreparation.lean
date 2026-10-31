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

-- A configuration result cannot replace the original epoch authority.
example : prepareConfiguredBridge (fun epoch : Nat => epoch == 0)
    (fun _ => (.ok (99, 1) : Except String (Nat × Nat)))
    (fun _ _ => .error "must not construct")
    (fun _ _ => (.error "must not bind" : Except String (Bool × Nat))) 0 = .error none := rfl
-- Configuration errors retain false as a cause, not an absent option.
example : prepareConfiguredBridge (fun _ : Nat => true)
    (fun _ => (.error false : Except Bool (Nat × Nat)))
    (fun _ _ => .error true) (fun _ _ => (.error true : Except Bool (Nat × Nat)))
    0 = .error (some false) := rfl
-- Read once, pass exact options, and use the current preparation state.
example : prepareConfiguredBridge (fun _ : Nat => true)
    (fun state => (.ok (7, state + 1) : Except String (Nat × Nat)))
    (fun options state => .ok (none, state + options))
    (fun options state => .ok (options * 2, state + 1)) 0 = .ok (14, 9) := rfl
-- Normal factory opt-out does not excuse a newly retired configuration owner.
example : prepareConfiguredBridge (fun epoch : Nat => epoch == 0)
    (fun state => (.ok (false, state) : Except String (Bool × Nat)))
    (fun _ _ => .ok (none, 1))
    (fun _ _ => (.error "must not bind" : Except String (Nat × Nat))) 0 = .error none := rfl
-- Fresh invocation captures a new epoch explicitly; old requests remain refused.
example : prepareConfiguredBridge (fun epoch : Nat => epoch == 1)
    (fun state => (.ok (false, state) : Except String (Bool × Nat)))
    (fun options state => .ok (some options, state))
    (fun _ _ => .error "unused") 1 = .ok (false, 1) := rfl

-- A specification first observed as stale cannot authorize any generator.
example : guardedProduct (scopeCurrent (fun epoch source : Nat => source != 0 || epoch == 0) [])
    [(fun _ => (.ok (7, (1, [0])) : Except String (Nat × (Nat × List Nat))))]
    (fun _ _ => (.error "must not construct" : Except String (Bool × (Nat × List Nat))))
    (0, []) = .error none := rfl
-- A later specification retires a captured predecessor, then supplies another owner.
example : guardedProduct (scopeCurrent (fun epoch source : Nat => source != 0 || epoch == 0) [])
    [(fun _ => (.ok (7, (0, [0])) : Except String (Nat × (Nat × List Nat)))),
     (fun _ => .ok (8, (1, [0, 1])))]
    (fun _ _ => (.error "must not construct" : Except String (Bool × (Nat × List Nat))))
    (0, []) = .error none := rfl
-- Domains arrive in declaration order, with the actual evolving captured directory.
example : guardedProduct (scopeCurrent (fun _ _ : Nat => true) [9])
    [(fun _ => (.ok (7, (1, [0])) : Except String (Nat × (Nat × List Nat)))),
     (fun _ => .ok (8, (2, [1, 0])))]
    (fun domains state => .ok (domains, state)) (0, []) = .ok ([7, 8], (2, [1, 0])) := rfl
-- Original construction causes are separate from source refusal and false data.
example : guardedProduct (scopeCurrent (fun _ _ : Nat => true) [])
    [(fun _ => (.ok (false, (0, [0])) : Except Bool (Bool × (Nat × List Nat))))]
    (fun _ _ => (.error false : Except Bool (Nat × (Nat × List Nat))))
    (0, []) = .error (some false) := rfl
-- Even a zero-argument declaration keeps its inherited preparation authority.
example : guardedProduct (scopeCurrent (fun _ source : Nat => source != 9) [9])
    ([] : List ((Nat × List Nat) → Except String (Nat × (Nat × List Nat))))
    (fun _ _ => (.error "must not construct" : Except String (Nat × (Nat × List Nat))))
    (0, []) = .error none := rfl
