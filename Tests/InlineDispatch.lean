import LeanPoo.Object.InlineDispatch

namespace LeanPoo.Tests.InlineDispatch

private abbrev Args := List String × Nat

private def precedence (args : Args) : List (List String) := [args.1]

private def generic : Except Object.MultimethodError
    (Object.Multimethod Args Nat Nat) := do
  let mut result : Object.Multimethod Args Nat Nat :=
    { arity := 1
      precedence
      combine := fun methods args => methods.foldl (· + ·) args.2 }
  for i in [:64] do
    result ← result.register [.prototype s!"P{i}"] (i + 1)
  result.registerWhen [.prototype "P0"] (fun args => args.2 % 2 == 0) 1000

private def shape : List String :=
  (List.range 64).map (fun i => s!"P{i}")

private def observed : Option Bool := do
  let generic ← generic.toOption
  let initial := Object.InlineDispatch.create generic
  let even : Args := (shape, 2)
  let odd : Args := (shape, 3)
  let narrower : Args := (shape.drop 1, 2)
  let (evenResult, afterEven) ← (initial.call even).toOption
  let (oddResult, afterOdd) ← (afterEven.call odd).toOption
  let (narrowResult, afterNarrow) ← (afterOdd.call narrower).toOption
  let revised ← (afterOdd.register [.prototype "P0"] 5000).toOption
  let (revisedResult, revisedAfterCall) ← (revised.call even).toOption
  let guarded ← (afterOdd.registerWhen [.prototype "P1"]
    (fun args => args.2 == 3) 2000).toOption
  let (guardedResult, _) ← (guarded.call odd).toOption
  return initial.entries.isEmpty && !afterEven.entries.isEmpty &&
    !afterOdd.entries.isEmpty && !afterNarrow.entries.isEmpty &&
    afterNarrow.entries.head?.map Object.InlineEntry.shape == some [shape.drop 1] &&
    revised.entries.isEmpty && !revisedAfterCall.entries.isEmpty &&
    guarded.entries.isEmpty &&
    evenResult == 3082 && oddResult == 2083 &&
    narrowResult == 2081 && revisedResult == 7081 &&
    guardedResult == 4083 &&
    (initial.call even).toOption.map Prod.fst == some evenResult &&
    (Object.InlineDispatch.direct generic even).toOption == some evenResult &&
    (Object.InlineDispatch.direct generic odd).toOption == some oddResult &&
    (Object.InlineDispatch.direct generic narrower).toOption == some narrowResult &&
    (afterOdd.call even).toOption.map Prod.fst == some evenResult &&
    (revised.call even).toOption.map Prod.fst == some revisedResult

example : observed = some true := by native_decide

private def arityFailure : Bool :=
  let generic : Object.Multimethod Args Nat Nat :=
    { arity := 1
      precedence := fun args => [args.1, args.1]
      combine := fun _ _ => 0 }
  match (Object.InlineDispatch.create generic).call (shape, 0) with
  | .error (.arity 1 2) => true
  | _ => false

example : arityFailure = true := by native_decide

private def fourRecentShapes : Option Bool := do
  let generic ← generic.toOption
  let mut site := Object.InlineDispatch.create generic
  for index in [:5] do
    let args : Args := (shape.drop index, 2)
    let (result, updated) ← (site.call args).toOption
    let direct ← (Object.InlineDispatch.direct generic args).toOption
    if result != direct then return false
    site := updated
  let firstOrder := site.entries.map Object.InlineEntry.shape
  let (_, touched) ← (site.call (shape.drop 2, 2)).toOption
  let (_, revised) ← (touched.call (shape.drop 5, 2)).toOption
  return firstOrder == [4, 3, 2, 1].map (fun i => [shape.drop i]) &&
    revised.entries.length == 4 &&
    revised.entries.map Object.InlineEntry.shape ==
      [5, 2, 4, 3].map (fun i => [shape.drop i])

#guard fourRecentShapes == some true

end LeanPoo.Tests.InlineDispatch
