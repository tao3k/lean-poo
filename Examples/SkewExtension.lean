import LeanPoo.Prototype.SkewLens

namespace LeanPoo.Examples.SkewExtension

structure Quota where
  retries : Nat
  burst : Nat
  deriving BEq

structure Config where
  quota : Quota
  enabled : Bool
  deriving BEq

/-- The method reads `enabled` from final self but updates inherited quota. -/
def context : Prototype.SkewLens Quota Bool Quota Config Config Config :=
  { view := Config.enabled
    update := fun change inherited =>
      { inherited with quota := change inherited.quota } }

/-- Refine the extension to one field without narrowing the self context. -/
def retryUpdate (change : Nat → Nat) (quota : Quota) : Quota :=
  { quota with retries := change quota.retries }

def retryFocus : Prototype.SkewLens Nat Bool Nat Config Config Config :=
  context.refocusUpdate retryUpdate

def incrementWhenEnabled : Prototype.Proto Bool Nat Nat :=
  fun enabled inherited => if enabled then inherited + 1 else inherited

def extension : Prototype.Proto Config Config Config :=
  retryFocus.focus incrementWhenEnabled

/-- A focused extension has the same meaning as the two focus steps. -/
example : extension =
    context.focus
      ((Prototype.SkewLens.updateOnly Bool retryUpdate).focus
        incrementWhenEnabled) := by
  exact Prototype.SkewLens.focus_compose context
    (Prototype.SkewLens.updateOnly Bool retryUpdate)
    incrementWhenEnabled

private def inherited : Config :=
  { quota := { retries := 2, burst := 8 }, enabled := false }

#guard extension { inherited with enabled := true } inherited ==
  { inherited with quota := { retries := 3, burst := 8 } }

#guard extension { inherited with enabled := false }
  { inherited with enabled := true } ==
    { quota := { retries := 2, burst := 8 }, enabled := true }

end LeanPoo.Examples.SkewExtension
