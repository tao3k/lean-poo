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

-- Source 2 is first observed before availability retires it; both classifications refuse.
example (availability : Bool) : prepareOpaqueLeaf
    (fun epoch : Nat => fun id : Nat => if id == 2 then epoch else 0)
    [(0, 0), (1, 0)] "binding" (fun state => .ok (0, state)) (fun state => .ok (0, state))
    (fun state => .ok ([2], state))
    (fun _ => (.ok (availability, 1) : Except String (Bool × Nat))) 0 = .error none := by
  cases availability <;> rfl
-- False availability is an admitted empty leaf with its original source ledger.
example : prepareOpaqueLeaf (fun _ : Nat => fun _ : Nat => 0) [(0, 0)] "binding"
    (fun state => .ok (0, state)) (fun state => .ok (0, state)) (fun state => .ok ([2], state))
    (fun state => (.ok (false, state) : Except String (Bool × Nat))) 0 =
    .ok (0, false, (0, [(2, 0), (0, 0)])) := rfl
-- Binding mismatch refuses before a deliberately throwing optional getter.
example : prepareOpaqueLeaf (fun _ : Nat => fun _ : Nat => 0) [(0, 0)] "binding"
    (fun state => .ok (0, state)) (fun state => .ok (1, state)) (fun state => .ok ([], state))
    (fun _ => (.error "must not read" : Except String (Bool × Nat))) 0 = .error (some "binding") := rfl
-- A thrown false cause is distinct from empty availability and stale refusal.
example : prepareOpaqueLeaf (fun _ : Nat => fun _ : Nat => 0) [(0, 0)] true
    (fun state => .ok (0, state)) (fun state => .ok (0, state)) (fun state => .ok ([], state))
    (fun _ => (.error false : Except Bool (Bool × Nat))) 0 = .error (some false) := rfl

-- A malformed hook remains an error even when the next participant is true.
example : checkSourceObservers "boolean required" true
    [(fun _ => .ok none), (fun _ => .ok (some true))] = .error "boolean required" := rfl
-- A valid prefix cannot turn a later malformed reply into current authority.
example : checkSourceObservers "boolean required" true
    [(fun _ => .ok (some true)), (fun _ => .ok none)] = .error "boolean required" := rfl
-- A false epoch skips the hook entirely, preserving retirement priority.
example : checkSourceObservers "boolean required" false
    [(fun _ => .error "must not enter")] = .ok false := rfl
-- False callback data short-circuits without entering a later malformed hook.
example : checkSourceObservers "boolean required" true
    [(fun _ => .ok (some false)), (fun _ => .ok none)] = .ok false := rfl
-- A thrown false cause differs from a valid false reply.
example : checkSourceObservers true true [(fun _ => .error false)] = .error false := rfl

-- The observer's false exception cannot erase an original object-like cause.
example : initializationFailure true false (fun _ => .error false)
    (fun _ : Nat => .ok .unsupported) 7 = ((.error, 7), false) := rfl
-- A false primary cause stays present when a different secondary error occurs.
example : initializationFailure true false (fun _ => .error "secondary")
    (fun _ : Bool => .ok .error) false = ((.error, false), false) := rfl
-- A retired epoch suppresses a deliberately failing observer and classifier.
example : initializationFailure false false (fun _ => .error "must not observe")
    (fun _ : Nat => .error "must not classify") 7 = ((.stale, 7), false) := rfl
-- Existing bounded outcomes keep their status while retaining the primary cause.
example : initializationFailure (Secondary := String) true false (fun _ => .ok true)
    (fun _ : Nat => .ok .exhausted) 7 = ((.exhausted, 7), false) := rfl
-- Diagnostic classifier failure never manufactures a property counterexample.
example : initializationFailure true false (fun _ => .ok true)
    (fun _ : Nat => .error "classifier") 7 = ((.error, 7), false) := rfl

-- Invalid count admission wins even over a stale source or throwing metadata.
example : prepareInspection false "invalid controls" (fun _ : Nat => false)
    (fun _ => (.error "must not prepare" : Except String (Bool × Nat))) 0 =
    .error (some "invalid controls") := rfl
-- Inexact/fractional/Boolean controls normalize to none, never an implicit bound.
example : inspectionReady [some 0, none, some 20, some 0, some 0] true true = false := rfl
-- Negative fuel is rejected, while unbounded exact seed magnitude is admitted.
example : inspectionReady [some 1267650600228229401496703205376, some 0, some 0, some 0, some 0]
    true true = true := rfl
example : inspectionReady [some 0, some 4, some 4, some 1, some (-1)] true true = false := rfl
-- A legal zero-draw inspection still cannot renew an old source snapshot.
example : prepareInspection true "invalid controls" (fun epoch : Nat => epoch == 0)
    (fun _ => (.ok (false, 1) : Except String (Bool × Nat))) 0 = .error none := rfl

-- A report getter may replace caller names; rendering still uses the captured row.
example : prepareReportDiagnostics (fun state : Nat => if state == 0 then ["input"] else ["changed"])
    [false] "invalid" (fun _ => .ok (true, 1)) 0 =
    .ok (true, some [("input", false)], 1) := by simp [prepareReportDiagnostics, diagnosticBindings]
-- Static duplicate rejection wins over an otherwise observable metadata failure.
example : prepareReportDiagnostics (fun _ : Nat => ["input", "input"])
    [1, 2] "invalid" (fun _ => .error "getter must not run") 0 = .error "invalid" := by simp [prepareReportDiagnostics]
-- Stale authority remains stale even when the finite row is perfectly named.
example : prepareReportDiagnostics (fun _ : Nat => ["input"])
    [7] "invalid" (fun _ => .ok (false, 2)) 0 =
    .ok (false, some [("input", 7)], 2) := by simp [prepareReportDiagnostics, diagnosticBindings]

-- An invalid run cannot reach the declaration's original callback exception.
example : prepareInspection (propertyRequestReady [some (-1), some 10, some 4] (some 1) none true true)
    "invalid request" (fun _ : Nat => true)
    (fun _ => (.error "must not construct" : Except String (Bool × Nat))) 0 =
    .error (some "invalid request") := rfl
-- A procedure-valued size still requires an explicit finite upper bound.
example : propertyRequestReady [some 42, some 10, none] (some 1) none true true = false := rfl
-- Valid bounded preparation preserves false as the exact original cause.
example : prepareInspection (propertyRequestReady [some 42, some 10, some 4] (some 1) none true true)
    true (fun _ : Nat => true) (fun _ => (.error false : Except Bool (Bool × Nat))) 0 =
    .error (some false) := rfl

-- A malformed present result cannot reach a deliberately failing raw binder.
example : prepareOwnedBridge (fun _ : Nat => true)
    (fun state => (.ok (2, state) : Except String (Nat × Nat)))
    (fun _ => (.error "invalid generator" : Except String (Option Bool)))
    (fun _ => .error "must not bind") 0 = .error (some "invalid generator") := rfl
-- Source retirement remains stale before malformed-result recognition.
example : prepareOwnedBridge (fun state : Nat => state == 0)
    (fun _ => (.ok (2, 1) : Except String (Nat × Nat)))
    (fun _ => (.error "invalid generator" : Except String (Option Bool)))
    (fun _ => .error "must not bind") 0 = .error none := rfl
-- A present generator producing false is not the raw opt-out sentinel.
example : prepareOwnedBridge (fun _ : Nat => true)
    (fun state => (.ok (1, state) : Except String (Nat × Nat)))
    (fun _ => (.ok (some false) : Except String (Option Bool)))
    (fun _ => .error "must not bind") 0 = .ok (false, 0) := rfl

-- Present false is malformed metadata, not the absent-observer path.
example : prepareObserverBinding (Hook := Nat) (fun _ : Nat => true) "not callable"
    (fun _ => .ok (some none, 0)) 0 = .error (some "not callable") := rfl

-- A malformed result cannot invoke a deliberately failing Key getter.
example : (prepareObserverBinding (Hook := Nat) (fun _ : Nat => true) "not callable"
    (fun _ => .ok (some none, 0)) 0).bind
    (fun _ => (.error (some "Key must not run") : Except (Option String) Nat)) =
    .error (some "not callable") := rfl

-- Retirement during metadata wins before malformed-value classification.
example : prepareObserverBinding (Hook := Nat) (fun epoch : Nat => epoch == 0) "not callable"
    (fun _ => .ok (some none, 1)) 0 = .error none := rfl

-- Absence and a callable identity keep distinct, exact binding receipts.
example : prepareObserverBinding (Hook := Nat) (fun _ : Nat => true) "not callable"
    (fun _ => .ok (none, 0)) 0 = .ok (none, 0) := rfl
example : prepareObserverBinding (fun _ : Nat => true) "not callable"
    (fun _ => .ok (some (some 7), 1)) 0 = .ok (some 7, 1) := rfl

-- A known constant overflow wins before source checks or failing metadata.
example : prepareInspection
    (propertyRequestReady [some 0, some 0, some 1] (some 1) (some 2) false true)
    "configuration" (fun _ : Nat => false)
    (fun _ => (.error "must not prepare" : Except String (Nat × Nat))) 0 =
      .error (some "configuration") := rfl
-- A valid zero envelope preserves the exact metadata exception, including false.
example : prepareInspection
    (propertyRequestReady [some 0, some 0, some 0] (some 1) (some 0) false true)
    true (fun _ : Nat => true)
    (fun _ => (.error false : Except Bool (Nat × Nat))) 0 = .error (some false) := rfl


-- A factory that retires its owner cannot invoke even a deliberately bad Iterable.
example : prepareShrinkIterator (fun epoch : Nat => epoch == 0)
    (fun _ => (.ok (false, 1) : Except String (Bool × Nat)))
    (fun _ _ => (.error "must not convert" : Except String (Unit × Nat))) 0 = .error none := rfl
-- Retirement during conversion cannot deliver a cursor to a later pull.
example : (prepareShrinkIterator (fun epoch : Nat => epoch == 0)
    (fun _ => (.ok (false, 0) : Except String (Bool × Nat)))
    (fun _ _ => (.ok ([], 1) : Except String (List Nat × Nat))) 0).bind
      (fun _ => (.error (some "must not pull") : Except (Option String) Nat)) = .error none := rfl
-- A thrown false remains a present original cause rather than a stale sentinel.
example : prepareShrinkIterator (Cursor := Unit) (fun _ : Nat => true)
    (fun state => (.ok (false, state) : Except Bool (Bool × Nat)))
    (fun _ _ => .error false) 0 = .error (some false) := rfl
-- An admitted empty iterator is successful preparation; no proposal is implied.
example : prepareShrinkIterator (Cause := String) (fun _ : Nat => true)
    (fun state => .ok (false, state)) (fun _ state => .ok ([], state)) 0 =
      .ok (([] : List Nat), 0) := rfl
-- Inherited parent authority suppresses a nested child after local retirement.
example : nestedActions (fun epoch : Nat => epoch == 0) (fun _ => true)
    (fun _ => (.ok (false, 1) : Except String (Bool × Nat)))
    (fun _ _ => (.error "must not enter nested draw" : Except String (Unit × Nat))) 0 = .error none := rfl
