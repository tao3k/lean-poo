import LeanPoo.Functional.Assembly

namespace LeanPoo.Tests.FunctionalAssembly
open C4 Functional

universe u v w
variable {Context : Type u} {Key : Type v} {Value : Context → Key → Type w}

example (order : VerifiedOrder graph root) (providers : String → Provider Context Key Value)
    (key : Key) (factory : Factory Context (fun context => Value context key))
    (selected : assemble order providers key = some factory) :
    ∃ name, Ancestor graph name root ∧ providers name key = some factory := assemble_origin selected

example (providers : String → Provider Context Key Value) (name : String) (rest : List String)
    (key : Key) (absent : providers name key = none) :
    select (name :: rest) providers key = select rest providers key := select_skip absent

/- A context-indexed witness cannot be carried from an earlier context merely
because C4 selects the same provider. The factory must return a new witness
at the supplied context's exact type. -/
private structure SampleContext where
  minimum : Nat
private def Witness (context : SampleContext) (_key : Unit) := {value : Nat // context.minimum ≤ value}
example (_old : Witness ⟨5⟩ ()) : True := by
  fail_if_success have _transferred : Witness ⟨10⟩ () := _old
  trivial
private def source : Provider SampleContext Unit Witness := fun _ =>
  some fun context => ⟨context.minimum + 1, by omega⟩
private def override : Provider SampleContext Unit Witness := fun _ =>
  some fun context => ⟨context.minimum + 3, by omega⟩
private def providers : String → Provider SampleContext Unit Witness
  | "Override" => override
  | "Source" => source
  | _ => fun _ => none

#guard (Functional.apply (select ["Absent", "Source"] providers) ⟨5⟩ ()).map (·.val) == some 6
#guard (Functional.apply (select ["Override", "Source"] providers) ⟨5⟩ ()).map (·.val) == some 8
#guard (Functional.apply (select ["Override", "Source"] providers) ⟨10⟩ ()).map (·.val) == some 13
#guard (select ["Absent"] providers ()).isNone

private def preparePair (provider : Provider SampleContext Unit Witness) :
    Except Unit (Factory SampleContext (fun context => Witness context () × Witness context ())) := do
  let factory ← require provider ()
  pure (Factory.zipWith (fun _ left right => (left, right)) factory factory)

#guard ((preparePair (select ["Override", "Source"] providers)).toOption.map
  (fun build => ((build ⟨5⟩).1.val, (build ⟨10⟩).2.val))) == some (8, 13)
#guard match preparePair (select ["Absent"] providers) with
  | .error () => true
  | .ok _ => false

private structure ExtendedContext where
  source : SampleContext
  order : Nat
private def atSource := Factory.reindex ExtendedContext.source
  (fun context : SampleContext => (⟨context.minimum + 1, by omega⟩ : Witness context ()))
#guard (atSource ⟨⟨10⟩, 7⟩).val == 11
example (_earlier : Witness ⟨5⟩ ()) : True := by
  fail_if_success have _wrong : Witness ⟨10⟩ () :=
    Factory.reindex ExtendedContext.source (fun _ => _earlier) ⟨⟨10⟩, 7⟩
  trivial

example (order : VerifiedOrder graph root) (providers : String → Provider Context Key Value)
    (key : Key) (factory : Factory Context (fun context => Value context key))
    (ready : require (assemble order providers) key = .ok factory) :
    ∃ name, Ancestor graph name root ∧ providers name key = some factory :=
  assemble_origin (require_ok_iff.mp ready)

#print axioms select_origin
#print axioms assemble_origin
#print axioms apply_selected
#print axioms require_ok_iff
#print axioms require_missing_iff
#eval IO.println "FUNCTIONAL-ASSEMBLY-OK"
end LeanPoo.Tests.FunctionalAssembly
