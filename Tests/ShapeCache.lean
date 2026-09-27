import LeanPoo.Object.InlineDispatch
import LeanPoo.Object.PreparedMultimethod

namespace LeanPoo.Tests.ShapeCache

open LeanPoo.Object

private def shape (index : Nat) : DispatchShape := [[s!"P{index}"]]

private def lruOrder : Bool := Id.run do
  let cache := (List.range 8).foldl
    (fun (cache : ShapeCache Nat) index => cache.remember (shape index) index)
    ({} : ShapeCache Nat)
  let touched := cache.touch (shape 0)
  let next := touched.remember (shape 8) 8
  return cache.size == 8 && touched.recent.head? == some (shape 0) &&
    next.size == 8 && next.get? (shape 1) == none &&
    next.get? (shape 0) == some 0 && next.get? (shape 8) == some 8

#guard lruOrder

private abbrev Args := DispatchShape × Nat

private def generic : Multimethod Args Nat Nat :=
  { arity := 1
    precedence := Prod.fst
    combine := fun methods args => methods.foldl Nat.add args.2 }

private def candidateEviction : Option Bool := do
  let initial ← (generic.register [.any] 1).toOption
  let mut current := initial
  for index in [:32] do
    let args : Args := (shape index, index)
    let (value, updated) ← (current.call args).toOption
    let direct ← (InlineDispatch.direct current args).toOption
    if value != direct then return false
    current := updated
  let bounded := current.cache.size == 8 &&
    (current.cache.get? (shape 0)).isNone &&
    (current.cache.get? (shape 31)).isSome
  let (_, touched) ← (current.call (shape 24, 24)).toOption
  let (_, next) ← (touched.call (shape 32, 32)).toOption
  return bounded && next.cache.size == 8 &&
    (next.cache.get? (shape 24)).isSome &&
    (next.cache.get? (shape 25)).isNone

#guard candidateEviction == some true

private def effectiveEviction : Option Bool := do
  let initial : PreparedMultimethod Args Nat Nat Nat :=
    PreparedMultimethod.create 1 Prod.fst
      (fun methods => methods.foldl Nat.add 0)
      (fun effective args => effective + args.2)
  let mut current ← (initial.register [.any] 1).toOption
  for index in [:32] do
    let (value, updated) ← (current.call (shape index, index)).toOption
    if value != index + 1 then return false
    current := updated
  let bounded := current.effectiveCache.size == 8 &&
    current.generic.cache.size == 8 &&
    (current.effectiveCache.get? (shape 24)).isSome
  let (_, touched) ← (current.call (shape 24, 24)).toOption
  let (_, next) ← (touched.call (shape 32, 32)).toOption
  return bounded && next.effectiveCache.size == 8 &&
    (next.effectiveCache.get? (shape 24)).isSome &&
    (next.effectiveCache.get? (shape 25)).isNone

#guard effectiveEviction == some true

end LeanPoo.Tests.ShapeCache
