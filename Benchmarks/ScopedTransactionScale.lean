import LeanPoo.Functional.ScopedTransaction
open LeanPoo C4 Functional
private def Value (c _ : Nat) := {n : Nat // c ≤ n}
private def base : Provider Nat Nat Value := fun _ => some (fun c => ⟨c + 1, by omega⟩)
private def cells (mode : String) (count width chunk : Nat) : List (RegistryEdit Nat Nat Value) :=
  (List.range (count / chunk)).map (fun batch =>
    (if mode == "keys" || mode == "positive" then "Source" else "Outside",
     (List.range chunk).map (fun offset =>
       let i := batch * chunk + offset
       let key := i % width + (if mode == "keys" then 1 else 0)
       (⟨key, if i % 7 == 0 then none else some (fun c => ⟨c+i+2, by omega⟩)⟩ : CapabilityEdit Nat Nat Value))))
private def observation (result : Except String (Except Nat (Requirements.Factories Nat Value [0]))) :
    String × Nat := match result with
  | .error name => ("name:" ++ name, 0)
  | .ok (.error key) => ("key:" ++ toString key, 0)
  | .ok (.ok ready) => ("ok", (Requirements.build ready 0).1.val + (Requirements.build ready 7).1.val)
def main (args : List String) : IO Unit := do
  let [variant, mode, countText, widthText, chunkText] := args |
    throw (IO.userError "variant mode count width chunk required")
  let some count := countText.toNat? | throw (IO.userError "invalid count")
  let some width := widthText.toNat? | throw (IO.userError "invalid width")
  let some chunk := chunkText.toNat? | throw (IO.userError "invalid chunk")
  unless count > 0 && width > 0 && chunk > 0 && count % chunk == 0 &&
      (variant == "full" || variant == "scoped") && ["outside", "keys", "positive", "unknown"].contains mode do
    throw (IO.userError "invalid parameters")
  let graph : Graph := {nodes := [{name := "Source"}, {name := "Outside"},
    {name := "Root", parentOrders := [["Source"]]}]}
  let .ok order := linearizeVerified graph "Root" | throw (IO.userError "graph rejected")
  let index := order.indexAncestors
  let registry := IndexedRegistry.ofRegistry (ProviderRegistry.ofGraph graph (fun name => if name == "Root" then fun _ => none else base))
  let edits := cells mode count width chunk ++ (if mode == "unknown" then [("Missing", [])] else [])
  let impact := Requirements.transactionMayAffect index [0] edits
  let start ← IO.monoNanosNow
  let result ← if variant == "scoped" then
    pure (Requirements.prepareTransaction index registry edits [0])
  else pure ((registry.patchTransaction edits).map (fun updated : IndexedRegistry Nat Nat Value =>
    Requirements.prepare (assemble order updated.dictionary) [0]))
  let elapsed := (← IO.monoNanosNow) - start
  -- Apply factories and compute independent scalar controls outside the timer.
  let actual := observation result
  let mut wanted : Option Nat := some 1
  if mode == "positive" then
    for i in List.range count do
      if i % width == 0 then wanted := if i % 7 == 0 then none else some (i+2)
  let expected := if mode == "unknown" then ("name:Missing", 0) else
    match wanted with | none => ("key:0", 0) | some n => ("ok", 2*n+7)
  unless actual == expected && impact == (mode == "positive") do
    throw (IO.userError "scoped/full scalar oracle mismatch")
  IO.println s!"variant={variant} mode={mode} count={count} width={width} chunk={chunk} batches={edits.length} impact={impact} status={actual.1} checksum={actual.2} elapsed_ns={elapsed} oracle_parity=true"
