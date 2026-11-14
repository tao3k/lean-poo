-- SPDX-License-Identifier: Apache-2.0 AND LGPL-2.1-or-later
import Std

namespace FallbackReflection

-- The native registration links the delegate's revision to the querying
-- receiver. A delegate edit invalidates that receiver's structural reads.
structure Revisions where
  owner : Nat
  view : Nat

def edit (linked : Bool) (state : Revisions) : Revisions :=
  ⟨state.owner + 1, if linked then state.view + 1 else state.view⟩

def current (issued live : Revisions) : Prop :=
  issued.owner = live.owner ∧ issued.view = live.view

theorem old_read_refused (state : Revisions) : ¬ current state (edit true state) := by
  simp [current, edit]

theorem recapture_is_current (state : Revisions) :
    current (edit true state) (edit true state) := by
  simp [current]

-- Comparing only the querying receiver would wrongly reuse its old signed
-- dependency after an unregistered delegate edit.
theorem unregistered_edit_preserves_stale_query_key (state : Revisions) :
    (edit false state).view = state.view ∧ ¬ current state (edit false state) := by
  simp [current, edit]

end FallbackReflection
