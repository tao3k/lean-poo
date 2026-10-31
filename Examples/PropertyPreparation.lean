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

-- A nested signature getter revises Function identity 0 before publishing input 2.
example : observeFunctionInputs (fun epoch : Nat => fun id : Nat => if id == 0 then epoch else 0)
    [(0, 0), (1, 0)] (fun _ => (.ok ([2], 1) : Except String (List Nat × Nat))) 0 =
    .error none := rfl
-- Stable discovery owns an input before a later metadata getter may revise it.
example : observeFunctionInputs (fun epoch : Nat => fun id : Nat => if id == 2 then epoch else 0)
    [(0, 0), (1, 0)] (fun _ => (.ok ([2, 2], 0) : Except String (List Nat × Nat))) 0 =
    .ok ([2, 2], (0, [(2, 0), (0, 0), (1, 0)])) := rfl
-- Reobserving that same input after retirement cannot renew its stamp.
example : observeFunctionInputs (fun epoch : Nat => fun id : Nat => if id == 2 then epoch else 0)
    [(0, 0), (1, 0), (2, 0)] (fun _ => (.ok ([2], 1) : Except String (List Nat × Nat))) 0 =
    .error none := rfl
-- A stale cached layout refuses before its deliberately failing child factory.
example : guardedGeneration (fun epoch : Nat => revisionsCurrent (fun _ : Nat => epoch) [(2, 0)])
    (fun _ => (.error "child must stay lazy" : Except String (Bool × Nat))) 1 = .error none := rfl
-- False metadata exceptions remain distinct from stale refusal.
example : observeFunctionInputs (fun _ : Nat => fun _ : Nat => 0) [(0, 0)]
    (fun _ => (.error false : Except Bool (List Nat × Nat))) 0 = .error (some false) := rfl
-- Fresh explicit preparation may own the new epoch; old captures stay obsolete.
example : observeFunctionInputs (fun epoch : Nat => fun _ : Nat => epoch) [(0, 1)]
    (fun _ => (.ok ([], 1) : Except String (List Nat × Nat))) 1 = .ok ([], (1, [(0, 1)])) := rfl

-- Zero edge budget skips even an explicitly throwing getter.
example : discoverCarrierEdge (fun _ : Nat => fun _ : Nat => 0) [(0, 0)] "quota" 0
    (fun _ => (.error "must not read" : Except String (Nat × Nat))) 0 = .error (some "quota") := rfl
-- First left-edge observation precedes the right getter's revision of that Type.
example : discoverCarrierEdge (fun epoch : Nat => fun id : Nat => if id == 1 then epoch else 0)
    [(0, 0), (1, 0)] "quota" 1 (fun _ => (.ok (2, 1) : Except String (Nat × Nat))) 0 = .error none := rfl
-- A repeated shared Type still consumes an occurrence without duplicating stamps.
example : discoverCarrierEdge (fun _ : Nat => fun _ : Nat => 0) [(1, 0)] "quota" 2
    (fun state => (.ok (1, state) : Except String (Nat × Nat))) 0 = .ok (1, (0, 1, [(1, 0)])) := rfl
-- A false exception remains an original callback cause, not stale refusal.
example : discoverCarrierEdge (fun _ : Nat => fun _ : Nat => 0) [(0, 0)] true 1
    (fun _ => (.error false : Except Bool (Nat × Nat))) 0 = .error (some false) := rfl
