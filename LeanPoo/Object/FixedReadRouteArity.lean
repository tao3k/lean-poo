-- SPDX-License-Identifier: Apache-2.0 AND LGPL-2.1-or-later
import LeanPoo.Object.ReadRouteRuns

namespace LeanPoo.Object.FixedReadRouteArity
open ReadRouteRuns

/-- The table guards can reject or depend on the current effect window.
A key-only check has no table arguments or table effects. -/
structure Checks where
  key : Except Refusal Unit
  bootstrap : Bool
  reads : Option (Except Refusal Unit)
  instanceTable : Option (Except Refusal Unit)
  writer : Except Refusal Unit

def run (check : Option (Except Refusal Unit)) : Except Refusal Unit :=
  check.getD (.ok ())

def fixed (checks : Checks) (write : Bool) : Except Refusal Unit := do
  checks.key
  if checks.bootstrap then return ()
  run checks.reads
  if write && checks.reads.isSome then checks.writer
  run checks.instanceTable

/-- The old optional entry selects a default for the omitted writer flag. -/
def ordinary (checks : Checks) (write : Option Bool := none) : Except Refusal Unit :=
  fixed checks (write.getD false)

theorem fixed_default (checks : Checks) :
    fixed checks false = ordinary checks := rfl

theorem fixed_explicit (checks : Checks) (write : Bool) :
    fixed checks write = ordinary checks (some write) := rfl

theorem key_only (keyCheck : Except Refusal Unit) (bootstrap write : Bool)
    (writer : Except Refusal Unit) :
    ordinary ⟨keyCheck, bootstrap, none, none, writer⟩ (some write) = keyCheck := by
  cases keyCheck with
  | error refusal => rfl
  | ok value => cases value; cases bootstrap <;> cases write <;> rfl

/-- Each check at a later boundary uses the new tables. Direct arity never
carries an earlier success into another window. -/
theorem independent_windows (before after : Checks) :
    (fixed before false, fixed after false) = (ordinary before, ordinary after) := rfl

-- Invalid keys fail before either reader or writer is used. Reader refusal
-- precedes writer refusal. On bootstrap even the writer is skipped.
#guard match fixed ⟨.error .key, false, some (.error .route), some (.error .route), .error .stale⟩ true with
  | .error .key => true | _ => false
#guard match fixed ⟨.ok (), false, some (.error .route), some (.error .issuance), .error .stale⟩ true with
  | .error .route => true | _ => false
#guard match fixed ⟨.ok (), true, some (.error .route), some (.error .route), .error .stale⟩ true with
  | .ok () => true | _ => false

end LeanPoo.Object.FixedReadRouteArity
