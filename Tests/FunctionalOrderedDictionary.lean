import LeanPoo.Functional.OrderedDictionary

namespace LeanPoo.Tests.FunctionalOrderedDictionary
open Functional Prototype

private instance {ε α : Type} [BEq ε] [BEq α] : BEq (Except ε α) where
  beq left right := match left, right with
    | .error a, .error b => a == b
    | .ok a, .ok b => a == b
    | _, _ => false

abbrev Map := OrderedDictionary OrderOps.integer (· < ·) Nat
def blank : Map := OrderedDictionary.empty _ _ OrderOps.integer_laws

-- The reference scans the caller's history backwards. It never uses trees,
-- comparison dispatch, acons, fold, writeView or a library transaction.
def lastValue (entries : List (Int × Nat)) (key : Int) : Option Nat :=
  ((entries.reverse.find? (fun entry => entry.1 == key)).map Prod.snd)

def canonical (entries : List (Int × Nat)) : List (Int × Nat) :=
  ((entries.map Prod.fst).eraseDups.mergeSort (· ≤ ·)).filterMap fun key =>
    (lastValue entries key).map (key, ·)

-- Recompute heights and balance from child structure, ignoring retained proofs
-- and production height/fold methods. Compare the complete ordered export too.
def inspect : Tree Int Nat → Bool × Nat
  | .empty => (true, 0)
  | .node left _ _ cached right =>
    let a := inspect left
    let b := inspect right
    let height := 1 + max a.2 b.2
    (a.1 && b.1 && cached == some height && a.2 ≤ b.2 + 1 && b.2 ≤ a.2 + 1, height)

def verify (map : Map) (expected : List (Int × Nat)) : IO Unit := do
  unless (inspect map.tree).1 && map.tree.inorder == canonical expected do
    throw (IO.userError "AVL height/balance or complete ordered contents")
  for key in (List.range 40).map (fun n => Int.ofNat n - 15) do
    unless map.get key == lastValue expected key do
      throw (IO.userError s!"all-key lookup: {key}")
  unless map.fold (fun key value acc => acc ++ [(key, value)]) [] == canonical expected do
    throw (IO.userError "actual afoldr order")

def patterns : List (List Int) := [[], [3, 2, 1], [1, 2, 3], [3, 1, 2], [1, 3, 2],
  [2, 1, 3, 2, 1, 2], (List.range 16).map Int.ofNat,
  ((List.range 16).map Int.ofNat).reverse, [8, 4, 12, 2, 6, 10, 14, 1, 3, 5, 7, 9, 11, 13, 15]]

def checkWrites : IO Nat := do
  let mut count := 0
  for shift in [-9, 0, 7] do
    for keys in patterns do
      let entries := keys.zipIdx |>.map (fun (key, index) => (key + shift, index + 1))
      let map := blank.writeMany entries
      verify map entries
      for split in List.range (entries.length + 1) do
        let prior := blank.writeMany (entries.take split)
        let next := prior.writeMany (entries.drop split)
        verify next entries
        verify prior (entries.take split)
        count := count + 1
      for extra in [[], [(shift, 40)], [(shift+1, 50), (shift, 60), (shift+1, 70)]] do
        let overrides := blank.writeMany extra
        let merged := map.merge overrides
        verify merged (entries ++ extra)
        let actual := (Dictionary.avl (Acc := Except String (Tree Int Nat)) OrderOps.integer).merge
          overrides.tree map.tree
        unless actual.toOption == some merged.tree do
          throw (IO.userError "existing source merge")
        verify map entries
        count := count + 1
  return count

abbrev FactoryMap := OrderedDictionary OrderOps.integer (· < ·) (Factory Nat (fun _ => Nat))
def flatten {keys : List Int} (data : Requirements.Results (fun (_ : Nat) (_ : Int) => Nat) 0 keys) : List Nat :=
  match keys, data with
  | [], _ => []
  | _ :: _, (head, tail) => head :: flatten tail

def expectedPrepare (entries : List (Int × Nat)) : List Int → Except Int (List Nat)
  | [] => .ok []
  | key :: rest => match lastValue entries key with
    | none => .error key
    | some value => (expectedPrepare entries rest).map (value :: ·)

-- Functions, not eagerly evaluated divergent values, test selection stopping.
partial def forbidden (_context : Nat) : Nat := forbidden 0

def checkPreparation : IO Nat := do
  let mut count := 0
  for base in [[], [(1, 2), (2, 3)], [(1, 4), (2, 5), (3, 6)]] do
    for extra in [[], [(1, 7)], [(2, 8), (2, 9), (4, 10)]] do
      let original : FactoryMap := (OrderedDictionary.empty _ _ OrderOps.integer_laws).writeMany
        (base.map fun (key, value) => (key, fun context => context + value))
      let changed := original.writeMany (extra.map fun (key, value) => (key, fun context => context + value))
      for keys in [[], [1], [2, 1], [1, 1, 3], [4, 9, 1], [9, 1, 10]] do
        let actual := (Requirements.prepare changed.provider keys).map (fun factories =>
          flatten (Requirements.build factories 0))
        unless actual == expectedPrepare (base ++ extra) keys do
          throw (IO.userError "complete preparation / first missing / repeated key")
        count := count + 1
  let guarded : FactoryMap := (OrderedDictionary.empty _ _ OrderOps.integer_laws).writeMany [(1, forbidden)]
  let chosen := Requirements.prepare guarded.provider [1]
  unless chosen.toOption.isSome do throw (IO.userError "preparation forced a factory")
  let failed := Requirements.prepare guarded.provider [1, 99, 1]
  match failed with
  | .error 99 => pure ()
  | _ => throw (IO.userError "missing capability failed before factory execution")
  return count + 2

structure Move where
  source : Int
  target : Int
  amount : Nat
  deriving Repr
inductive Error where
  | same | missing (key : Int) | insufficient (available requested : Nat)
  deriving BEq, Repr

def proposal (view : Int → Option Nat) (move : Move) : Except Error (List (Int × Nat)) :=
  if move.source = move.target then .error .same
  else match view move.source with
    | none => .error (.missing move.source)
    | some source => match view move.target with
      | none => .error (.missing move.target)
      | some target => if move.amount ≤ source then
          .ok [(move.source, source-move.amount), (move.target, target+move.amount)]
        else .error (.insufficient source move.amount)

-- A separate finite resource vector uses positional replacement and ordinary
-- arithmetic. It has no tree, functional overwrite or proposed-write callback.
def modelRead (state : List Nat) (key : Int) : Option Nat :=
  if 1 ≤ key ∧ key ≤ 4 then state[key.toNat - 1]? else none

def modelStep (state : List Nat) (move : Move) : Except Error (List (Int × Nat)) × List Nat :=
  if move.source = move.target then (.error .same, state)
  else match modelRead state move.source with
    | none => (.error (.missing move.source), state)
    | some source => match modelRead state move.target with
      | none => (.error (.missing move.target), state)
      | some target => if source < move.amount then (.error (.insufficient source move.amount), state)
        else
          let debit := source - move.amount
          let credit := target + move.amount
          (.ok [(move.source, debit), (move.target, credit)],
            (state.set (move.source.toNat-1) debit).set (move.target.toNat-1) credit)

def modelBatch (state : List Nat) : List Move → Except Error (List (List (Int × Nat))) × List Nat
  | [] => (.ok [], state)
  | move :: rest =>
    let (result, next) := modelStep state move
    match result with
    | .error error => (.error error, next)
    | .ok output =>
      let (result, final) := modelBatch next rest
      (result.map (output :: ·), final)

def observe (state : Map) := [-2, -1, 0, 1, 2, 3, 4, 5, 6].map state.get
def modelObserve (state : List Nat) := [-2, -1, 0, 1, 2, 3, 4, 5, 6].map (modelRead state)
def entriesOf (state : List Nat) := state.zipIdx |>.map (fun (value, index) => ((index+1 : Nat), value))
def intEntries (state : List Nat) := (entriesOf state).map (fun (key, value) => ((key : Int), value))

def checkTransfers : IO (Nat × Nat × Nat) := do
  let mut singles := 0
  let mut batches := 0
  let mut continuations := 0
  for first in [0, 2, 5] do
    for second in [0, 3] do
      for third in [1, 4] do
        let vector := [first, second, third, 0]
        let map := blank.writeMany (intEntries vector)
        for source in [-1, 1, 2, 3, 4, 5] do
          for target in [-1, 1, 2, 3, 4, 5] do
            for amount in [0, 1, 2, 4, 9] do
              let move : Move := ⟨source, target, amount⟩
              let actual := map.transact proposal move
              let expected := modelStep vector move
              unless actual.1 == expected.1 && observe actual.2 == modelObserve expected.2 do
                throw (IO.userError s!"transfer {repr move}")
              unless expected.2.foldl (· + ·) 0 == vector.foldl (· + ·) 0 do
                throw (IO.userError "resource conservation")
              verify actual.2 (intEntries expected.2)
              let schedule : List Move := [⟨1, 2, 1⟩, move, ⟨3, 4, 1⟩]
              let actualBatch := map.transactBatch proposal schedule
              let expectedBatch := modelBatch vector schedule
              unless actualBatch.1 == expectedBatch.1 && observe actualBatch.2 == modelObserve expectedBatch.2 do
                throw (IO.userError "prefix / failure state / suffix stopping")
              verify actualBatch.2 (intEntries expectedBatch.2)
              let resume : List Move := [⟨2, 3, 1⟩, ⟨1, 4, 0⟩]
              let actualResume := actualBatch.2.transactBatch proposal resume
              let expectedResume := modelBatch expectedBatch.2 resume
              unless actualResume.1 == expectedResume.1 && observe actualResume.2 == modelObserve expectedResume.2 do
                throw (IO.userError "continuation")
              verify actualResume.2 (intEntries expectedResume.2)
              unless observe map == modelObserve vector do throw (IO.userError "original snapshot")
              singles := singles + 1
              batches := batches + 1
              continuations := continuations + 1
  return (singles, batches, continuations)

partial def forbiddenProposal (_view : Int → Option Nat) (_move : Move) : Except Error (List (Int × Nat)) :=
  forbiddenProposal _view _move

def checkStopping : IO Nat := do
  let initial := blank.writeMany [(1, 5), (2, 0), (3, 1), (4, 0)]
  let guarded := fun view (move : Move) =>
    if move.source = 99 then forbiddenProposal view move else proposal view move
  for refusal in [Move.mk 2 2 0, ⟨2, 3, 9⟩, ⟨-1, 3, 0⟩] do
    let actual := initial.transactBatch guarded [⟨1, 2, 2⟩, refusal, ⟨99, 3, 0⟩]
    let expected := modelBatch [5, 0, 1, 0] [⟨1, 2, 2⟩, refusal]
    unless actual.1 == expected.1 && observe actual.2 == modelObserve expected.2 do
      throw (IO.userError "divergent callback suffix / exact retained prefix")
  return 3

def run : IO Unit := do
  let writes ← checkWrites
  let preparation ← checkPreparation
  let (singles, batches, continuations) ← checkTransfers
  let stopping ← checkStopping
  IO.println s!"FUNCTIONAL-ORDERED-DICTIONARY-OK writes={writes} preparations={preparation} transfers={singles} batches={batches} continuations={continuations} stopping={stopping}"

#eval run
#print axioms OrderedDictionary.get_writeMany
#print axioms OrderedDictionary.merge_source
#print axioms OrderedDictionary.prepare_writeMany
#print axioms OrderedDictionary.transactBatch_view
#print axioms OrderedDictionary.transactBatch_error_iff
#print axioms Validation.traverseState_transport

end LeanPoo.Tests.FunctionalOrderedDictionary
