import LeanPoo.Object.DispatchTable
import LeanPoo.Object.MultimethodCombination
import LeanPoo.Object.InlineDispatch
import LeanPoo.Object.PreparedMultimethod

namespace LeanPoo.Tests.QualifiedCombination

open LeanPoo

inductive Qualifier where
  | check
  | label
  deriving DecidableEq

abbrev Body : Qualifier → Type
  | .check => Nat → Bool
  | .label => String

abbrev Input := List (List String) × Nat

inductive Operation where
  | run
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable

abbrev Args (_ : Operation) := Input
abbrev Method (_ : Operation) := Sigma Body
abbrev Result (_ : Operation) := Except String (List String)
abbrev Table := Object.DispatchTable Operation Args Method Result

private def generic : Object.Multimethod Input (Sigma Body)
    (Except String (List String)) :=
  Object.Multimethod.qualified 2 Prod.fst fun methods input =>
    if (methods.lookup .check).all (fun check => check input.2) then
      .ok (methods.lookup .label)
    else
      .error "rejected"

private def plugin : Object.DispatchTable.Edit (Key := Operation)
    (Args := Args) (Method := Method) (Result := Result) Unit := do
  Object.DispatchTable.registerIn .run
    [.prototype "A", .prototype "B"] ⟨.label, "specific"⟩
  Object.DispatchTable.contributeIn .run
    [.prototype "A", .prototype "B"] ⟨.check, fun size => size < 100⟩
  Object.DispatchTable.contributeIn .run
    [.prototype "A", .prototype "B"] ⟨.label, "newest"⟩

private def observed : Option Bool := do
  let initial := (Object.DispatchTable.empty : Table).install .run generic
  let base ← (initial.register .run [.any, .any] ⟨.label, "fallback"⟩).toOption
  let shape := [["A"], ["B"]]
  let (_, warm) ← (base.call .run (shape, 1)).toOption
  let (_, extended) ← (plugin.run warm).toOption
  let cleared := ((extended.get? .run).map (·.cache.size)) == some 0
  let (small, cached) ← (extended.call .run (shape, 1)).toOption
  let (large, _) ← (cached.call .run (shape, 101)).toOption
  let (old, _) ← (warm.call .run (shape, 1)).toOption
  let smallOk := match small with
    | .ok labels => labels == ["newest", "specific", "fallback"]
    | .error _ => false
  let largeRejected := match large with
    | .error message => message == "rejected"
    | .ok _ => false
  let oldOk := match old with
    | .ok labels => labels == ["fallback"]
    | .error _ => false
  return cleared && smallOk && largeRejected && oldOk

#guard observed == some true

#guard match generic.contribute [.prototype "A"] ⟨.label, "bad"⟩ with
  | .error (.arity 2 1) => true
  | _ => false

private def optimizedPaths : Option Bool := do
  let shape := [["A"], ["B"]]
  let method : Sigma Body := ⟨.label, "specific"⟩
  let check : Sigma Body := ⟨.check, fun size => size < 100⟩
  let site ← ((Object.InlineDispatch.create generic).register
    [.prototype "A", .prototype "B"] method).toOption
  let (_, warmedSite) ← (site.call (shape, 1)).toOption
  let revisedSite ← (warmedSite.contribute
    [.prototype "A", .prototype "B"] check).toOption
  let siteCleared := revisedSite.entries.isEmpty
  let (siteResult, _) ← (revisedSite.call (shape, 101)).toOption
  let prepared : Object.PreparedMultimethod Input (Sigma Body)
      (Object.QualifiedMethods Qualifier Body) (Except String (List String)) :=
    Object.PreparedMultimethod.create 2 Prod.fst
      (fun contributions =>
        Object.QualifiedMethods.prependAll contributions.toList {})
      (fun methods input =>
        if (methods.lookup .check).all (fun accepts => accepts input.2) then
          .ok (methods.lookup .label)
        else .error "rejected")
  let prepared ← (prepared.register
    [.prototype "A", .prototype "B"] method).toOption
  let (_, warmedPrepared) ← (prepared.call (shape, 1)).toOption
  let revisedPrepared ← (warmedPrepared.contribute
    [.prototype "A", .prototype "B"] check).toOption
  let preparedCleared := revisedPrepared.effectiveCache.size == 0 &&
    revisedPrepared.generic.cache.size == 0
  let (preparedResult, _) ← (revisedPrepared.call (shape, 101)).toOption
  return siteCleared && preparedCleared &&
    (match siteResult with | .error message => message == "rejected" | _ => false) &&
    (match preparedResult with | .error message => message == "rejected" | _ => false)

#guard optimizedPaths == some true

end LeanPoo.Tests.QualifiedCombination
