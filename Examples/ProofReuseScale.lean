import LeanPoo.Object.Debug

namespace ProofReuseScaleExample

open LeanPoo.Proof
open LeanPoo.Proof.Debug

def obligation (key : Nat) : Obligation Nat (fun _ => Nat) where
  dependencies := [key]
  holds := fun _ => True
  stable := by intros; trivial

def object (count : Nat) : ProofObject Nat (fun _ => Nat) where
  state := fun _ => 0
  obligations := (List.range count).map obligation

def impactCounts (count changed : Nat) : Nat × Nat := Id.run do
  let impacts := explainPatch (object count) (Patch.set changed 1)
  let repair := impacts.filter (·.needsRepair) |>.length
  return (impacts.length - repair, repair)

-- One touched key must invalidate exactly one of ten thousand obligations.
#guard impactCounts 10000 7 == (9999, 1)
#guard impactCounts 10000 10001 == (10000, 0)
#eval impactCounts 10000 7

end ProofReuseScaleExample
