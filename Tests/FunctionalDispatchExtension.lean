import LeanPoo.Functional.DispatchExtension

namespace LeanPoo.Tests.FunctionalDispatchExtension
open Functional.DispatchExtension Object

structure Args where
  document : String
  channel : String
  amount : Nat
def precedence (args : Args) : DispatchShape := [[args.document, "Document"], [args.channel, "Channel"]]
abbrev Generic := Multimethod Args String Unit
def blank : Generic := { arity := 2, precedence, combine := fun _ _ => () }

-- Independent finite domain model: association lists, complete pair enumeration,
-- symbolic predicates and ordered watch scanning. No trie, cache, sparse
-- traversal, production edit, or negative checker is used by this oracle.
inductive Tag where | named (name : String) | wildcard deriving BEq
inductive Predicate where | always | above (limit : Nat) | never
def Predicate.holds : Predicate → Args → Bool
  | .always, _ => true | .above limit, args => args.amount > limit | .never, _ => false
def Tag.specializer : Tag → Specializer | .named name => .prototype name | .wildcard => .any
structure Change where
  kind : Nat
  path : List Tag
  predicate : Predicate
  label : String
def Change.edit (change : Change) : Edit Args String :=
  let path := change.path.map Tag.specializer
  match change.kind with
  | 0 => .register path change.label
  | 1 => .contribute path change.label
  | 2 => .registerWhen path change.predicate.holds change.label
  | _ => .erase path
abbrev Table := List (List Tag × List (Predicate × String))
def update (table : Table) (change : Change) : Table :=
  let old := ((table.find? (fun row => row.1 == change.path)).map Prod.snd).getD []
  let methods := if change.kind = 0 then [(Predicate.always, change.label)]
    else if change.kind = 1 then (Predicate.always, change.label) :: old
    else if change.kind = 2 then (change.predicate, change.label) :: old else []
  (change.path, methods) :: table.filter (fun row => row.1 != change.path)
def modelPatch : Table → List Change → Except Nat Table
  | table, [] => .ok table
  | table, change :: rest => if change.path.length = 2 then modelPatch (update table change) rest else .error change.path.length
def modelObserve (table : Table) (watch : Watch Args) : List String := Id.run do
  let shape := match watch with | .shape shape => shape | .call args => precedence args
  let first := ((shape[0]?).getD []).map Tag.named ++ [.wildcard]
  let second := ((shape[1]?).getD []).map Tag.named ++ [.wildcard]
  let mut labels := []
  for left in first do
    for right in second do
      for (predicate, label) in (((table.find? (fun row => row.1 == [left, right])).map Prod.snd).getD []) do
        let active := match watch with | .shape _ => true | .call args => predicate.holds args
        if active then labels := labels ++ [label]
  return labels
def modelFirst (table : Table) : List (Watch Args) → Nat → Option (Nat × String)
  | [], _ => none
  | watch :: rest, index => match modelObserve table watch with
    | [] => modelFirst table rest (index+1) | first :: _ => some (index, first)

def low : Args := ⟨"Invoice", "Bank", 10⟩
def high : Args := ⟨"Invoice", "Bank", 150⟩
def card : Args := ⟨"Invoice", "Card", 20⟩
def p (document channel : String) : List Tag := [.named document, .named channel]
def changes (limit : Nat) : List (List Change) := [
  [], [⟨2, p "Invoice" "Bank", .above limit, "guard"⟩],
  [⟨2, p "Invoice" "Bank", .never, "false"⟩],
  [⟨0, p "Document" "Bank", .always, "inherited"⟩],
  [⟨0, [.wildcard, .named "Bank"], .always, "wild-left"⟩],
  [⟨1, [.named "Invoice", .wildcard], .always, "wild-right"⟩],
  [⟨1, p "Invoice" "Card", .always, "unrelated"⟩],
  [⟨2, p "Invoice" "Bank", .above limit, "guard"⟩, ⟨3, p "Invoice" "Bank", .always, "erase"⟩],
  [⟨2, p "Invoice" "Bank", .above limit, "guard"⟩, ⟨0, [.wildcard], .always, "bad-arity"⟩],
  [⟨0, [.wildcard], .always, "bad-first"⟩, ⟨0, p "Document" "Bank", .always, "inherited"⟩],
  [⟨0, p "Invoice" "Bank", .always, "old"⟩, ⟨2, p "Invoice" "Bank", .never, "false"⟩],
  [⟨0, p "Invoice" "Bank", .always, "old"⟩, ⟨0, p "Invoice" "Bank", .always, "replacement"⟩]]
def watchLists : List (List (Watch Args)) := [[], [.call low], [.call high], [.shape (precedence low)],
  [.call low, .call high, .shape (precedence ⟨"Report", "Bank", 0⟩)],
  [.shape (precedence ⟨"Report", "Bank", 0⟩), .call high, .call low, .call high]]
def check : IO Unit := do
  let initial : Change := ⟨0, p "Invoice" "Card", .always, "card"⟩
  let installed ← IO.ofExcept ((initial.edit.apply blank).mapError (fun _ => "initial"))
  let (_, warm) ← IO.ofExcept ((installed.call card).mapError (fun _ => "warm"))
  let mut count := 0
  for source in [installed, warm] do
    for limit in [0, 10, 100, 200] do
      for transaction in changes limit do
        for watches in watchLists do
          let previous ← IO.ofExcept ((Functional.DispatchExtension.check source watches).mapError (fun _ => "baseline"))
          let edits := transaction.map Change.edit
          let actual := guard source watches previous edits
          let model := modelPatch (update [] initial) transaction
          let correct := match model, actual with
            | .error expected, .error (.registration (.arity arity actual) _) => arity == 2 && actual == expected
            | .ok table, .ok revision => (modelFirst table watches 0).isNone &&
                revision.snapshot.cache.values.size == (if transaction.isEmpty then source.cache.values.size else 0)
            | .ok table, .error (.introduced _ _ conflict) =>
                (modelFirst table watches 0) == some (conflict.earlier.length, (conflict.violation.firstMethod).getD "no-method")
            | _, _ => false
          unless correct do throw (IO.userError "negative extension outcome / first conflict / arity priority")
          let (publication, retained) := publish source watches previous edits
          if publication.toOption.isNone then
            unless retained.cache.values.size == source.cache.values.size do throw (IO.userError "refused warm-cache publication")
          count := count+1
  IO.println s!"dispatch extension: {count} independent controls"

#eval check
#guard (match Functional.DispatchExtension.check blank [.shape []] with
  | .error conflict => match conflict.violation with | .arity _ => true | _ => false
  | .ok _ => false)
-- Costed observation must preserve the independent reference for both watches.
#guard (observedCounted blank (.call ⟨"Invoice", "Card", 10⟩)).1 == reference blank (.call ⟨"Invoice", "Card", 10⟩)
#guard (observedCounted blank (.shape [["Invoice"], ["Card"]])).2 == 0
#guard cacheComparisons (List.replicate 8 [["Other"]]) [["Missing"]] == 8
#print axioms selectCounted_cached
#print axioms observedCounted_result
#guard (rememberRecent (List.replicate 12 [["Other"]]) [["New"]]).length == 8
#print axioms remembered_comparisons
#print axioms cacheComparisons_capacity
#print axioms guard_ok_iff
#print axioms Revision.cacheSound
#print axioms Violation.firstMethod_origin
end LeanPoo.Tests.FunctionalDispatchExtension
