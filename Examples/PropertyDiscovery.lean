import LeanPoo.Functional.PropertyDiscovery

open LeanPoo.Functional.PropertyTesting

-- Three occurrences still require three credits even when they share one Type.
example : prepareCarrierDirectory (fun _ : Nat => 0) [] "invalid" "quota" 2 (some [0, 0, 0])
    (fun row owned => .ok (row, owned)) = .error (some "quota") := rfl
-- Exact fuel preserves all edges while capturing the shared identity only once.
example : prepareCarrierDirectory (fun _ : Nat => 0) [] "invalid" "quota" 3 (some [0, 0, 0])
    (fun row owned => .ok (row, owned)) = .ok ([0, 0, 0], [(0, 0)]) := rfl
-- A callback cannot enter a now-revised sibling captured from the initial row.
example : prepareCarrierDirectory (fun _ : Nat => 0) [] "invalid" "quota" 2 (some [0, 1])
    (fun _ owned => discoverCarrierEdge
      (fun (state source : Nat) => if state = 1 ∧ source = 1 then 1 else 0)
      owned "quota" 1 (fun _ => .error "must not read") 1) = .error none := rfl
-- A thrown false remains a cause under an admitted directory, not absence.
example : prepareCarrierDirectory (fun _ : Nat => 0) [] true true 1 (some [0])
    (fun _ owned => discoverCarrierEdge (fun (_state _source : Nat) => 0)
      owned true 1 (fun _ => .error false) 0) = .error (some false) := rfl
-- Empty directories and malformed directories have different zero-fuel outcomes.
example : prepareCarrierDirectory (fun _ : Nat => 0) [] "invalid" "quota" 0 (some [])
    (fun _ _ => .ok false) = .ok false := rfl
example : prepareCarrierDirectory (fun _ : Nat => 0) [] "invalid" "quota" 0 none
    (fun _ _ => (.error (some "must not visit") : Except (Option String) Bool)) =
      .error (some "invalid") := rfl

-- Returning observers cannot revise a freshly owned Sum directory and publish it.
example : observeVariantDirectory (fun _ : Nat => 0)
    (fun (state _source : Nat) => state) [] 0 "invalid" "quota" 2 (some ["primary", "backup"])
    (fun _ => .ok (false, 1)) 0 = .error none := rfl
-- Repeated payload Types do not erase distinct labels or their occurrence cost.
example : observeVariantDirectory (fun _ : Nat => 0)
    (fun (_state _source : Nat) => 0) [] 0 "invalid" "quota" 2 (some ["primary", "backup"])
    (fun state => .ok (false, state)) 0 = .ok (["primary", "backup"], (false, 0), [(0, 0)]) := rfl
-- Width overflow precedes any throwing observer, preserving the quota category.
example : observeVariantDirectory (Value := Bool) (fun _ : Nat => 0)
    (fun (_state _source : Nat) => 0) [] 0 "invalid" "quota" 1 (some ["primary", "backup"])
    (fun _ => .error "observer") 0 = .error (some "quota") := rfl
-- False is an actual callback cause, not the stale sentinel.
example : observeVariantDirectory (Value := Bool) (fun _ : Nat => 0)
    (fun (_state _source : Nat) => 0) [] 0 true true 1 (some ["primary"])
    (fun _ => .error false) 0 = .error (some false) := rfl

-- A returned dependency row retains both occurrences and its first single stamp.
example : observeCapturedSources (fun _ : Nat => 0) (fun (_state _source : Nat) => 0)
    [] "invalid" (some [1, 1]) (fun state => .ok (false, state)) 0 =
    .ok ([1, 1], (false, 0), [(1, 0)]) := rfl
-- A singleton Type declaration is owned before the returning observer revises it.
example : observeCapturedSources (fun _ : Nat => 0) (fun (state _source : Nat) => state)
    [] "invalid" (some [1]) (fun _ => .ok (false, 1)) 0 = .error none := rfl
-- False remains an exact observer exception, distinct from stale publication.
example : observeCapturedSources (Value := Bool) (fun _ : Nat => 0) (fun (_state _source : Nat) => 0)
    [] true (some [1]) (fun _ => .error false) 0 = .error (some false) := rfl
-- Present empty dependencies are permitted; malformed input cannot run a binder.
example : observeCapturedSources (fun _ : Nat => 0) (fun (_state _source : Nat) => 0)
    [] "invalid" (some []) (fun state => .ok (false, state)) 0 = .ok ([], (false, 0), []) := rfl
