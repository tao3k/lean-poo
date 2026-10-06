import LeanPoo.Functional.IndexedOverlay

namespace LeanPoo.Tests.FunctionalIndexedOverlay
open Functional
universe u v w x

-- A generic consumer claim is reused without per-key require or step alignment.
example {Context : Type u} {Key : Type v} [BEq Key] [Hashable Key] [LawfulBEq Key] [DecidableEq Key] {Value : Context → Key → Type w}
    {Result : Type x} (base : Provider Context Key Value)
    (edits : List (CapabilityEdit Context Key Value)) (keys : List Key)
    (consume : Requirements.Factories Context Value keys → Result) (Claim : Except Key Result → Prop)
    (known : Claim ((Requirements.prepare
      (edits.foldl (fun provider edit => provider.patchKey edit.1 edit.2) base) keys).map consume)) :
    Claim ((Requirements.prepare (IndexedOverlay.compile base edits).provider keys).map consume) := by
  rw [Requirements.prepare_indexed_compile, Requirements.prepare_overlay_compile]
  exact known

private inductive Capability where
  | quantity | flag | bound
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Inhabited
-- Every key deliberately collides: correctness cannot depend on hash separation.
private instance : Hashable Capability := ⟨fun _ => 0⟩
private def number : Capability → Nat
  | .quantity => 0 | .flag => 1 | .bound => 2
private def Value (c : Nat) : Capability → Type
  | .quantity => {n : Nat // c ≤ n}
  | .flag => Bool
  | .bound => PLift (c ≤ c + 2)
private def base : Provider Nat Capability Value
  | .quantity => some (fun c => ⟨c + 1, by omega⟩)
  | .flag => none
  | .bound => some (Factory.fromProof (fun _ => by omega))
private def replacement (available : Bool) (value : Nat) : (key : Capability) →
    Option (Factory Nat (fun c => Value c key))
  | .quantity => if available then some (fun c => ⟨c + value, by omega⟩) else none
  | .flag => if available then some (fun _ => value % 2 == 1) else none
  | .bound => if available then some (Factory.fromProof (fun _ => by omega)) else none
private def values : {keys : List Capability} → Requirements.Results Value c keys → List Nat
  | [], _ => []
  | .quantity :: _, (head, tail) => head.val :: values tail
  | .flag :: _, (head, tail) => (if (show Bool from head) then 1 else 0) :: values tail
  | .bound :: _, (_, tail) => 1 :: values tail
private def observe (provider : Provider Nat Capability Value) (keys : List Capability) (c : Nat) :
    Except Capability (List Nat) := (Requirements.prepare provider keys).map (fun ready => values (Requirements.build ready c))
private def same : Except Capability (List Nat) → Except Capability (List Nat) → Bool
  | .ok a, .ok b => a == b
  | .error a, .error b => a == b
  | _, _ => false
private def oracle (cells : Array (Option Nat)) (keys : List Capability) (c : Nat) :
    Except Capability (List Nat) := do
  let mut output := []
  for key in keys do
    let some value := cells[number key]! | throw key
    let observed := match key with
      | .quantity => c + value
      | .flag => value % 2
      | .bound => 1
    output := output ++ [observed]
  return output
private def lists : List (List Capability) :=
  [[], [.quantity], [.flag], [.bound], [.quantity, .flag, .bound],
   [.bound, .flag, .quantity], [.quantity, .quantity], [.flag, .quantity, .flag]]

#eval do
  IO.println "FUNCTIONAL-INDEXED-OVERLAY-START"
  let mut histories := 0
  let mut updates := 0
  let mut prefixChecks := 0
  let mut batchChecks := 0
  for mask in List.range 8 do
    for length in [1, 2, 8, 32] do
      let mut overlay := IndexedOverlay.ofProvider base
      let mut sequential := base
      let mut edits : List (CapabilityEdit Nat Capability Value) := []
      let mut cells : Array (Option Nat) := #[some 1, none, some 1]
      for step in List.range length do
        let key := [Capability.quantity, .flag, .bound][step % 3]!
        let available := ((mask / (2 ^ number key)) % 2 == 1) != (step / 3 % 2 == 1)
        let value := step + 2
        let edit := replacement available value key
        let saved := overlay
        overlay := overlay.extend [⟨key, edit⟩]
        for keys in lists do
          for c in [0, 7] do
            unless same (observe saved.provider keys c) (oracle cells keys c) do
              throw (IO.userError "retained overlay snapshot changed")
        sequential := sequential.patchKey key edit
        edits := edits ++ [(⟨key, edit⟩ : CapabilityEdit Nat Capability Value)]
        cells := cells.set! (number key) (if available then some value else none)
        unless overlay.overrides.size ≤ 3 do throw (IO.userError "history leaked into overlay size")

        for keys in lists do
          for c in [0, 7] do
            let expected := oracle cells keys c
            unless same (observe overlay.provider keys c) expected && same (observe sequential keys c) expected do
              throw (IO.userError "prefix factory result/first error differs from independent oracle")
            prefixChecks := prefixChecks + 1
        updates := updates + 1
      let compiled := IndexedOverlay.compile base edits
      for keys in lists do
        for c in [0, 7] do
          unless same (observe compiled.provider keys c) (oracle cells keys c) do
            throw (IO.userError "batch result/first error differs from independent oracle")
          batchChecks := batchChecks + 1
      histories := histories + 1
    IO.println s!"FUNCTIONAL-INDEXED-OVERLAY-PROGRESS histories={histories} updates={updates}"
  -- Same-key history: the compiled provider stores one override, not 256 wrappers.
  let repeated : List (CapabilityEdit Nat Capability Value) :=
    (List.range 256).map (fun step => ⟨.quantity, replacement true (step + 1) .quantity⟩)
  let compact := IndexedOverlay.compile base repeated
  unless compact.overrides.size == 1 &&
      same (observe compact.provider [.quantity, .bound] 7) (.ok [263, 1]) &&
      same (observe compact.provider [.flag, .quantity] 7) (.error .flag) do
    throw (IO.userError "repeated-key normalization failed")
  unless histories == 32 && updates == 344 && prefixChecks == 5504 && batchChecks == 512 do
    throw (IO.userError "unexpected overlay corpus")
  IO.println s!"FUNCTIONAL-INDEXED-OVERLAY-OK histories={histories} updates={updates} prefixChecks={prefixChecks} batchChecks={batchChecks} repeatedEdits=256 storedOverrides=1 contexts=2"

#print axioms IndexedOverlay.ofProvider_provider
#print axioms IndexedOverlay.set_base
#print axioms IndexedOverlay.set_provider
#print axioms IndexedOverlay.extend_base
#print axioms IndexedOverlay.extend_provider
#print axioms IndexedOverlay.extend_append
#print axioms IndexedOverlay.compile_provider
#print axioms Requirements.prepare_indexed_extend
#print axioms Requirements.prepare_indexed_compile
end LeanPoo.Tests.FunctionalIndexedOverlay
