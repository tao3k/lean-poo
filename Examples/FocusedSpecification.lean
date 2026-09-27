import LeanPoo.Object.Builder
import LeanPoo.Object.Memo

namespace LeanPoo.Examples.FocusedSpecification

structure Quota where
  retries : Nat
  burst : Nat
  deriving BEq

structure Config where
  quota : Quota
  enabled : Bool
  deriving BEq

def quotaFocus : Prototype.MonoLens Config Quota :=
  .ofGetSet Config.quota (fun quota config => { config with quota })

def retriesFocus : Prototype.MonoLens Quota Nat :=
  .ofGetSet Quota.retries (fun retries quota => { quota with retries })

/-- A reusable, first-class path from a configuration to one nested field. -/
def retryPath : Prototype.MonoLens Config Nat :=
  quotaFocus.compose retriesFocus

example (config : Config) : retryPath.view config = config.quota.retries := rfl

inductive Key where
  | config
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable

def Value : Key → Type
  | .config => Config

open Object.Declaration.Builder

def base : Object.Declaration Key Value := Object.Declaration.build do
  value .config { quota := { retries := 2, burst := 8 }, enabled := true }

/-- Only the nested retry count is changed; other fields are inherited. -/
def layer : Object.Declaration Key Value := Object.Declaration.build do
  focusInherited .config retryPath Nat.succ

def result : Except C4.Error (Option Config) := do
  let empty : Object.Schema Key Value :=
    { graph := { nodes := [] }, declaration := fun _ => none }
  let basePlan ← LeanPoo.mix empty "Base" [] base
  let extended ← LeanPoo.extend basePlan.schema "RetryLayer" "Base" layer
  return extended.memoize.read .config

#guard match result with
  | .ok (some config) =>
      config == { quota := { retries := 3, burst := 8 }, enabled := true }
  | _ => false

end LeanPoo.Examples.FocusedSpecification
