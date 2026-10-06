import LeanPoo.Functional.CachedPreparation
open LeanPoo C4 Functional
private def Value (c _ : Nat) := {n : Nat // c ≤ n}
private def base : Provider Nat Nat Value := fun _ => some (fun c => ⟨c+1, by omega⟩)
private def changes (mode : String) (count requests chunk : Nat) : List (RegistryEdit Nat Nat Value) :=
  (List.range (count / chunk)).map (fun batch =>
    (if mode == "outside" || mode == "unknown" then "Outside" else "Source",
     (List.range chunk).map (fun offset =>
       let i := batch*chunk+offset
       let overlap := (mode == "early" && i == 0) || (mode == "late" && i == count-1)
       let key := if overlap then (if mode == "early" then 0 else requests-1) else requests+i%32
       (⟨key, if mode == "late" && overlap then none else some (fun c => ⟨c+i+2, by omega⟩)⟩ : CapabilityEdit Nat Nat Value))))
private def sumValues : {keys : List Nat} → Requirements.Results Value c keys → Nat
  | [], _ => 0
  | _ :: _, (head, tail) => head.val + sumValues tail
private def observe (result : Except String (Except Nat (Requirements.Factories Nat Value keys))) : String × Nat :=
  match result with
  | .error name => ("name:"++name, 0)
  | .ok (.error key) => ("key:"++toString key, 0)
  | .ok (.ok ready) => ("ok", sumValues (Requirements.build ready 0) + sumValues (Requirements.build ready 7))
def main (args : List String) : IO Unit := do
  let [variant, mode, countText, requestsText, chunkText] := args |
    throw (IO.userError "variant mode count requests chunk required")
  let some count := countText.toNat? | throw (IO.userError "invalid count")
  let some requests := requestsText.toNat? | throw (IO.userError "invalid requests")
  let some chunk := chunkText.toNat? | throw (IO.userError "invalid chunk")
  unless count > 0 && requests > 0 && chunk > 0 && count % chunk == 0 &&
      ["indexed", "cached"].contains variant && ["outside", "keys", "early", "late", "unknown"].contains mode do
    throw (IO.userError "invalid parameters")
  let graph : Graph := {nodes := [{name := "Source"}, {name := "Outside"},
    {name := "Root", parentOrders := [["Source"]]}]}
  let .ok order := linearizeVerified graph "Root" | throw (IO.userError "graph rejected")
  let ancestry := order.indexAncestors
  let registry := IndexedRegistry.ofRegistry (ProviderRegistry.ofGraph graph
    (fun name => if name == "Root" then fun _ => none else base))
  let keys := List.range requests
  let edits := changes mode count requests chunk ++ (if mode == "unknown" then [("Missing", [])] else [])
  let begin ← IO.monoNanosNow
  let scope := Requirements.KeyIndex.ofKeys keys
  let cache := Requirements.cacheCertified (assemble order registry.dictionary) keys
    (fun _ _ => True) (fun _ _ _ => True.intro)
  -- IO cell materializes the retained inputs before the query clock boundary.
  let retained ← IO.mkRef (scope, cache)
  let (scope, cache) ← retained.get
  let setupNs := (← IO.monoNanosNow)-begin
  let start ← IO.monoNanosNow
  let result ← if variant == "indexed" then
      pure (Requirements.prepareTransactionIndexed ancestry scope registry edits)
    else pure ((Requirements.prepareTransactionCached ancestry scope registry edits cache).map
      Requirements.TransactionPreparation.forget)
  let queryNs := (← IO.monoNanosNow)-start
  let actual := observe result
  let expected := if mode == "unknown" then ("name:Missing", 0) else if mode == "late" then
    ("key:"++toString (requests-1), 0) else ("ok", 9*requests+(if mode == "early" then 2 else 0))
  unless actual == expected do throw (IO.userError "indexed/list scalar outcome mismatch")
  IO.println s!"variant={variant} mode={mode} count={count} requests={requests} chunk={chunk} batches={edits.length} status={actual.1} checksum={actual.2} setup_ns={setupNs} query_ns={queryNs} oracle_parity=true"
