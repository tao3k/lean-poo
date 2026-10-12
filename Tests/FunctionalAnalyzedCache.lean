import LeanPoo.Functional.AnalyzedCache

namespace LeanPoo.Tests.FunctionalAnalyzedCache
open Functional
universe u v w
example {Context : Type u} [DecidableEq Context] {Key : Type v}
    {Value : Context → Key → Type w} {Result : Context → Type w}
    (code : Computation Context Key Value Result) (provider : Provider Context Key Value)
    (Claim : ∀ c, Result c → Prop) (cache : Computation.Cache code provider Claim) (c : Context) :
    (cache.read c).1.val = code.evaluate provider c ∧
      Computation.OutcomeValid Claim c (cache.read c).1.val := (cache.read c).1.property

example {Context : Type u} {Key : Type v} {Value : Context → Key → Type w}
    {Result : Context → Type w} (old _next : Computation Context Key Value Result)
    (provider : Provider Context Key Value) (Claim : ∀ c, Result c → Prop)
    (_cache : Computation.Cache old provider Claim) : True := by
  fail_if_success have _stale : Computation.Cache _next provider Claim := _cache
  trivial

private inductive Key where
  | quantity | proof | noise
  deriving BEq, DecidableEq
private def Value (c : Nat) : Key → Type
  | .quantity => {n : Nat // c ≤ n}
  | .proof => PLift (c ≤ c+1)
  | .noise => Bool
private def provider (mask : Nat) (noise : Bool) : Provider Nat Key Value
  | .quantity => if mask % 2 == 1 then some (fun c => ⟨c+2, by omega⟩) else none
  | .proof => if mask / 2 % 2 == 1 then some (Factory.fromProof (fun _ => by omega)) else none
  | .noise => some (fun _ => noise)
private def code : Computation Nat Key Value (fun _ => Nat) :=
  .both (.need .quantity (fun _ n => n.val)) (.need .proof (fun _ _ => 1)) (fun _ q p => q+p)
private def Claim (c n : Nat) : Prop := c ≤ n
private theorem admit (view : Provider Nat Key Value) (c : Nat) :
    Computation.OutcomeValid Claim c (code.evaluate view c) := by
  cases q : view .quantity with
  | none =>
    simp only [code, Computation.evaluate, q]
    change True
    trivial
  | some factory =>
    cases p : view .proof with
    | none =>
      simp only [code, Computation.evaluate, q, p]
      change True
      trivial
    | some proof =>
      have bound : c ≤ (factory c).val + 1 := by
        have lower := (factory c).property
        omega
      simp only [code, Computation.evaluate, q, p]
      change c ≤ (factory c).val + 1
      exact bound
private theorem noise_stable (mask : Nat) (left right : Bool) (c : Nat) :
    code.evaluate (provider mask left) c = code.evaluate (provider mask right) c := by
  apply code.evaluate_congr _ _ rfl
  · intro key member
    simp only [code, Computation.analyze, DependencyFootprint.merge, List.mem_append, List.mem_singleton] at member
    rcases member with rfl | rfl <;> rfl
  · simp [code, Computation.analyze, DependencyFootprint.merge]
private def scalar (mask c : Nat) : Except (ComputationError Key) Nat :=
  if mask % 2 == 0 then .error (.missing .quantity)
  else if mask / 2 % 2 == 0 then .error (.missing .proof) else .ok (c+3)
private def same : Except (ComputationError Key) Nat → Except (ComputationError Key) Nat → Bool
  | .ok a, .ok b => a == b
  | .error a, .error b => a == b
  | _, _ => false

#eval do
  IO.println "FUNCTIONAL-ANALYZED-CACHE-START"
  let mut reads := 0
  let mut hits := 0
  for mask in List.range 4 do
    let mut cache := Computation.Cache.empty code (provider mask false) Claim (admit _)
    let mut previous : Option Nat := none
    for c in [0,0,7,7,0,23,23] do
      let (result, next, reused) := cache.read c
      unless same result.val (scalar mask c) && reused == (previous == some c) do
        throw (IO.userError "computed slot disagrees with independent context trace")
      let _resultContract := result.property.2
      cache := next
      previous := some c
      reads := reads+1
      if reused then hits := hits+1
    let rebased := cache.rebind (provider mask true) (noise_stable mask false true)
    let (result, _, reused) := rebased.read 23
    unless reused && same result.val (scalar mask 23) do
      throw (IO.userError "proved rebinding lost hot data/error and joint contract")
  let stopped : Computation Nat Key Value (fun _ => Nat) := .failure "cached-source"
  let valid := fun _ => (show Computation.OutcomeValid (fun _ (_ : Nat) => False) _
    (stopped.evaluate (provider 0 false) _) from True.intro)
  let cache := Computation.Cache.empty stopped (provider 0 false) (fun _ (_ : Nat) => False) valid
  let (_, first, reused) := cache.read 7
  let (error, _, hot) := first.read 7
  unless !reused && hot && same error.val (.error (.source "cached-source")) do
    throw (IO.userError "source-error cache lifetime")
  unless reads == 28 && hits == 12 do throw (IO.userError "cache trace coverage changed")
  IO.println s!"FUNCTIONAL-ANALYZED-CACHE-OK reads={reads} hits={hits} rebounds=4 source-errors=2"

#print axioms LeanPoo.Functional.Computation.Cache.read_result
#print axioms LeanPoo.Functional.Computation.Cache.rebind_read_result
#print axioms LeanPoo.Functional.Computation.Cache.rebind_read_reused
end LeanPoo.Tests.FunctionalAnalyzedCache
