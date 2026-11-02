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
