import LeanPoo.Functional.TransactionCheck
namespace LeanPoo.Tests.FunctionalTransactionCheck
open Functional
universe u v w
-- Consumers can retain the preflight result across successful updates.
example {Context : Type u} {Key : Type v} [BEq Key] [Hashable Key]
    {Value : Context → Key → Type w} (registry updated : IndexedRegistry Context Key Value)
    (changes pending : List (RegistryEdit Context Key Value))
    (applied : registry.patchTransaction changes = .ok updated)
    (Claim : Except String Unit → Prop) (known : Claim (registry.checkTransaction pending)) :
    Claim (updated.checkTransaction pending) := by
  rw [IndexedRegistry.checkTransaction_after registry updated changes pending applied]
  exact known
private def Value (c : Nat) : Bool → Type
  | true => {n : Nat // c ≤ n}
  | false => Bool
private def replacement (value : Nat) : (key : Bool) → Option (Factory Nat (fun c => Value c key))
  | true => if value % 3 == 0 then none else some (fun c => ⟨c + value, by omega⟩)
  | false => if value % 3 == 0 then none else some (fun _ => value % 2 == 0)
private def recipe (width : Nat) : List (CapabilityEdit Nat Bool Value) :=
  (List.range width).map (fun i => ⟨i % 2 == 0, replacement i (i % 2 == 0)⟩)
private def same : Except String Unit → Except String Unit → Bool
  | .ok _, .ok _ => true
  | .error a, .error b => a == b
  | _, _ => false
private def providerSame (a b : Provider Nat Bool Value) : Bool :=
  [0, 7].all (fun c =>
    (a true).map (fun f => (f c).val) == (b true).map (fun f => (f c).val) &&
    (a false).map (fun f => (show Bool from f c)) == (b false).map (fun f => (show Bool from f c)))
#eval do
  IO.println "FUNCTIONAL-TRANSACTION-CHECK-START"
  let names := ["A", "B", "C", "D"]
  let choices := names ++ ["Missing", "LaterMissing"]
  let mut plans : List (List String) := [[]]
  let mut level : List (List String) := [[]]
  for _ in List.range 3 do
    level := level.flatMap (fun prior => choices.map (fun name => prior ++ [name]))
    plans := plans ++ level
  let mut cases := 0
  let mut successes := 0
  let mut rejected := 0
  let mut cached := 0
  for mask in List.range 16 do
    let registered : List String := (names.zipIdx.filter
      (fun entry : String × Nat => mask / 2^entry.2 % 2 == 1)).map Prod.fst
    -- Registered providers initially have no capabilities: name checks cannot
    -- be mistaken for successful capability preparation.
    let registry : ProviderRegistry Nat Bool Value :=
      ⟨registered.foldl (fun table name => table.insert name (fun _ => none)) {}⟩
    let indexed := IndexedRegistry.ofRegistry registry
    for width in [0, 3, 64] do
      let cells := recipe width
      for plan in plans do
        let edits := plan.map (fun name => (name, cells))
        let expected : Except String Unit := match plan.find? (fun name => !registered.contains name) with
          | none => .ok () | some name => .error name
        unless same (registry.checkTransaction edits) expected &&
            same (indexed.checkTransaction edits) expected &&
            same (checkTransactionNames registered.contains edits) expected do
          throw (IO.userError "preflight/initial-name oracle mismatch")
        unless same ((registry.patchTransaction edits).map (fun _ => ())) expected &&
            same ((indexed.patchTransaction edits).map (fun _ => ())) expected do
          throw (IO.userError "preflight/full transaction outcome mismatch")
        match indexed.patchTransaction edits with
        | .error _ => rejected := rejected + 1
        | .ok updated =>
          successes := successes + 1
          let pending := edits ++ [("Missing", []), ("LaterMissing", cells)]
          unless same (updated.checkTransaction pending) (indexed.checkTransaction pending) do
            throw (IO.userError "cached indexed preflight changed")
          let .ok ordinary := registry.patchTransaction edits | throw (IO.userError "ordinary control failed")
          unless same (ordinary.checkTransaction pending) (registry.checkTransaction pending) do
            throw (IO.userError "cached ordinary preflight changed")
          cached := cached + 1
        for name in choices do
          unless providerSame (indexed.dictionary name) (registry.dictionary name) do
            throw (IO.userError "original query snapshot changed")
        cases := cases + 1
    IO.println s!"FUNCTIONAL-TRANSACTION-CHECK-PROGRESS masks={mask+1} cases={cases}"
  unless cases == 12432 && successes == 1056 && rejected == 11376 && cached == successes do
    throw (IO.userError s!"unexpected preflight corpus cases={cases} successes={successes} rejected={rejected}")
  let empty : ProviderRegistry Nat Bool Value := ⟨({} : Std.HashMap String (Provider Nat Bool Value)).insert "Empty" (fun _ => none)⟩
  unless same (empty.checkTransaction [("Empty", [])]) (.ok ()) do
    throw (IO.userError "registered empty name rejected")
  let .error true := Requirements.prepare (empty.dictionary "Empty") [true] |
    throw (IO.userError "preflight wrongly guarantees capability availability")
  IO.println s!"FUNCTIONAL-TRANSACTION-CHECK-OK cases={cases} successes={successes} rejected={rejected} cached={cached} contexts=2"
#print axioms checkTransactionNames_ok_iff
#print axioms checkTransactionNames_congr
#print axioms ProviderRegistry.checkTransaction_outcome
#print axioms IndexedRegistry.checkTransaction_outcome
#print axioms ProviderRegistry.checkTransaction_after
#print axioms IndexedRegistry.checkTransaction_after
#print axioms IndexedRegistry.ofRegistry_checkTransaction
end LeanPoo.Tests.FunctionalTransactionCheck
