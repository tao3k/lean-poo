import LeanPoo.Deriving.DictionaryCompiler
import LeanPoo.Functional.DictionaryTransport
import LeanPoo.Functional.GraphConstraints

namespace LeanPoo.Tests.DictionaryTransport
open Functional Functional.Requirements
universe u v w x

example {Context : Type u} {Key : Type v} {Value : Context → Key → Type w}
    {Fields : Context → Key → Type x} (bridge : DictionaryTransport.Family Value Fields)
    (provider : Provider Context Key Value) (keys : List Key) :
    prepare (DictionaryTransport.provider bridge provider) keys =
      (prepare provider keys).map (Requirements.observe (DictionaryTransport.expose bridge)) :=
  DictionaryTransport.prepare_provider bridge provider keys

class Quantity (context : Nat) where
  value : Nat
  lower : context ≤ value
  apply : Nat → Nat
  law : ∀ n, apply n = n+value
derive_dictionary Quantity
class Flag where
  value : Bool
  label : String
  law : label = if value then "true" else "false"
derive_dictionary Flag

private inductive Key where | quantity | flag | ghost
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr
private instance : Hashable Key where hash _ := 0
private abbrev Value (c : Nat) : Key → Type
  | .quantity | .ghost => Quantity c
  | .flag => Flag
private abbrev Fields (c : Nat) : Key → Type 1
  | .quantity | .ghost => Quantity.Fields (context := c)
  | .flag => Flag.Fields
private def bridge : DictionaryTransport.Family Value Fields := fun c key => match key with
  | .quantity | .ghost => Quantity.dictionaryBridge (context := c)
  | .flag => Flag.dictionaryBridge
private abbrev quantity (c n : Nat) : Quantity c := ⟨c+n, by omega, fun x => x+(c+n), fun _ => rfl⟩
private abbrev flag (value : Bool) : Flag := ⟨value, if value then "true" else "false", rfl⟩
private partial def diverge (n : Nat) : Nat := diverge n
private def sources (mask : Nat) (name : String) : Provider Nat Key Value := fun key =>
  match key with
  | .quantity => if (name == "A" || name == "B") && mask % 2 == 1 then
      some (fun c => quantity c (if name == "A" then 1 else 2)) else none
  | .flag => if (name == "A" || name == "B") && mask / 2 % 2 == 1 then
      some (fun _ => flag (name == "A")) else none
  | .ghost => if name == "Outside" then some (fun c => quantity c (diverge 0)) else none
private def graph : C4.Graph := {nodes := [{name := "Root", parentOrders := [["A", "B"]]},
  {name := "A"}, {name := "B"}, {name := "Outside"}]}
private def targets : List C4.Graph := [graph,
  {nodes := [{name := "Root", parentOrders := [["B", "A"]]}, {name := "A"}, {name := "B"}]},
  {nodes := [{name := "Root", parentOrders := [["B"]]}, {name := "B"}]},
  {nodes := [{name := "Root", parentOrders := [["Outside", "A", "B"]]},
    {name := "Outside"}, {name := "A"}, {name := "B"}]}]
private def keys : List Key := [.quantity, .flag, .quantity]
private def Claim (c : Nat) (data : Results Value c keys) : Prop :=
  c ≤ data.1.value ∧ @Quantity.apply c data.1 0 = data.1.value ∧ data.2.1.label = if data.2.1.value then "true" else "false"
private theorem admit (provider : Provider Nat Key Value) (factories : Factories Nat Value keys)
    (_selected : Selected provider keys factories) (c : Nat) : Claim c (build factories c) := by
  rcases factories with ⟨q, f, second, empty⟩
  exact ⟨(q c).lower, (@Quantity.law c (q c) 0).trans (Nat.zero_add _), (f c).law⟩
private def FieldClaim (c : Nat) (data : Results Fields c keys) : Prop :=
  Claim c (observeResults (DictionaryTransport.reveal bridge) data)
private theorem fieldAdmit (provider : Provider Nat Key Fields) (factories : Factories Nat Fields keys)
    (_selected : Selected provider keys factories) (c : Nat) : FieldClaim c (build factories c) := by
  rcases factories with ⟨q, f, second, empty⟩
  let actual := Quantity.fromFields (q c)
  let other := Flag.fromFields (f c)
  exact ⟨actual.lower, (@Quantity.law c actual 0).trans (Nat.zero_add _), other.law⟩

private def methodConsumer {ready : Certified keys Claim} (c : Nat) (data : Snapshot ready c) :
    {value : Nat // c ≤ value} :=
  data.consume (Output := fun context => {value : Nat // context ≤ value}) (fun context values _ => by
    letI : Quantity context := values.1
    exact ⟨Quantity.apply (context := context) 5, by
      rw [Quantity.law]
      exact Nat.le_trans (Quantity.lower (context := context)) (Nat.le_add_left _ _)⟩)

#eval do
  IO.println "DICTIONARY-TRANSPORT-START"
  let .ok order := C4.linearizeVerified graph "Root" | throw (IO.userError "graph")
  let mut misses := 0
  let mut values := 0
  let mut cacheReads := 0
  let mut reused := 0
  let mut fresh := 0
  let mut refused := 0
  for mask in List.range 4 do
    let source := assemble order (sources mask)
    let mapped := assemble order (fun name => DictionaryTransport.provider bridge (sources mask name))
    let requests : List (List Key) := [[], [.quantity], [.flag], keys, [.flag, .quantity, .flag]]
    for request in requests do
      match prepare source request, prepare mapped request with
      | .error a, .error b =>
        unless a == b do throw (IO.userError "automatic conversion changed first missing key")
        misses := misses+1
      | .ok _, .ok factories =>
        for c in [0,7,23] do
          -- Invoke the actual generated dictionary's method through fields.
          for key in request do
            match key with
            | .quantity =>
              let some factory := mapped .quantity | throw (IO.userError "prepared quantity disappeared")
              let dictionary := Quantity.fromFields (factory c)
              letI : Quantity c := dictionary
              unless Quantity.value (context := c) == c+1 && Quantity.apply (context := c) 3 == 3+c+1 do
                throw (IO.userError "converted provider changed method dispatch")
            | .flag =>
              let some factory := mapped .flag | throw (IO.userError "prepared flag disappeared")
              let dictionary := Flag.fromFields (factory c)
              unless dictionary.value && dictionary.label == "true" do throw (IO.userError "converted flag changed")
            | .ghost => throw (IO.userError "unrequested divergent method")
            values := values+1
          let _built := build factories c
      | _, _ => throw (IO.userError "conversion changed preparation availability")
    if mask == 3 then
      let .ok ready := prepareCertified source keys Claim (admit source) | throw (IO.userError "source certificate")
      let initial := ContextSlot.empty ready
      let (_, hot, _) := initial.read 7
      let converted := DictionaryTransport.slot bridge hot
      for c in [7,0,23] do
        let (actual, _, hit) := converted.read c
        let (prior, _, priorHit) := hot.read c
        let restored := observeResults (DictionaryTransport.reveal bridge) actual.val
        unless hit == priorHit && restored.1.value == prior.val.1.value &&
            @Quantity.apply c restored.1 5 == 5+c+1 && restored.2.1.label == prior.val.2.1.label do
          throw (IO.userError "joint proof/cache conversion changed context or dispatch")
        let _retainedJoint := actual.property.2
        let (consumed, next, consumedHit) := DictionaryTransport.consumeSnapshot bridge converted methodConsumer c
        unless consumed.val == 5+c+1 && consumedHit == priorHit && (next.read c).2.2 do
          throw (IO.userError "proof-aware dictionary consumer changed method result/cache state")
        cacheReads := cacheReads+1
    let registry : IndexedRegistry Nat Key Fields :=
      IndexedRegistry.ofRegistry (ProviderRegistry.ofGraph graph (fun name => DictionaryTransport.provider bridge (sources mask name)))
    let provider := assemble order registry.dictionary
    let cached := cacheCertified provider keys FieldClaim (fieldAdmit provider)
    let .ok absent := checkAbsent provider [.ghost] | throw (IO.userError "old ghost absence")
    let original : ConstraintCache provider keys [.ghost] FieldClaim := ⟨cached, BuiltContextCache.empty cached, absent⟩
    let warmed := match original.read 7 with | .error _ => original | .ok read => read.next
    for targetGraph in targets do
      let .ok ⟨target, outcome⟩ := migrateGraphConstraints order.indexAncestors warmed (KeyIndex.ofKeys keys)
          targetGraph "Root" (fun _ _ => none) [] | throw (IO.userError "actual target compile")
      match outcome with
      | .error (.introduced actual) =>
        unless actual.key == Key.ghost && target.index.order.output.contains "Outside" do
          throw (IO.userError "converted negative conflict changed")
        refused := refused+1
      | .error (.missing key _) =>
        let expected := if mask % 2 == 0 then Key.quantity else Key.flag
        unless key == expected && !target.index.order.output.contains "Outside" do
          throw (IO.userError "converted capability errors changed")
        refused := refused+1
      | .ok accepted =>
        let admission : accepted.positive.Admission := by
          cases accepted.positive with
          | reused _ _ _ => trivial
          | fresh _ _ => exact fieldAdmit (assemble target.index.order target.registry.dictionary)
        let next := accepted.certify admission
        let .ok data := next.read 7 | throw (IO.userError "accepted field cache")
        let decoded := observeResults (DictionaryTransport.reveal bridge) data.data
        let choseA := (target.index.order.output.filter (fun name => name == "A" || name == "B")).head? == some "A"
        unless decoded.1.value == (if choseA then 8 else 9) && decoded.2.1.value == choseA &&
            data.reused == target.canReuse order (KeyIndex.ofKeys keys) do
          throw (IO.userError "converted actual migration returned stale method/proof/cache")
        let _joint := data.correct
        if data.reused then reused := reused+1 else fresh := fresh+1
  unless misses == 10 && values == 30 && cacheReads == 3 && reused == 1 && fresh == 2 && refused == 13 do
    throw (IO.userError s!"dictionary transport coverage changed: {misses}, {values}, {cacheReads}, {reused}, {fresh}, {refused}")
  IO.println s!"DICTIONARY-TRANSPORT-OK missing={misses} methods={values} cache-reads={cacheReads} graph-reused={reused} graph-fresh={fresh} graph-refused={refused}"

#print axioms LeanPoo.Functional.DictionaryTransport.provider_from_to
#print axioms LeanPoo.Functional.DictionaryTransport.prepare_provider
#print axioms LeanPoo.Functional.DictionaryTransport.certified_build
#print axioms LeanPoo.Functional.DictionaryTransport.slot_read_value
#print axioms LeanPoo.Functional.DictionaryTransport.slot_read_reused
#print axioms LeanPoo.Functional.DictionaryTransport.consumeSnapshot_state
#print axioms LeanPoo.Functional.DictionaryTransport.consumeSnapshot_value
end LeanPoo.Tests.DictionaryTransport
