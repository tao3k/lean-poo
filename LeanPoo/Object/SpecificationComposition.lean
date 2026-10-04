import LeanPoo.Object.Memo

/-! Chapter 9's alternative nested extension protocol combines direct
extensions and local parent orders into one specification. Direct methods
are finalizers: later parents are evaluated before those methods. -/

namespace LeanPoo.Object

universe u v

/-- Compose two direct declarations, most-specific first. Methods retain
open self and delayed next. The more-specific direct default wins. -/
def Declaration.compose [DecidableEq Key]
    (child parent : Declaration Key Value) : Declaration Key Value :=
  let keys := (child.slots.map Entry.key ++ parent.slots.map Entry.key).eraseDups
  let slots := keys.filterMap fun key =>
    let method := match child.slot key, parent.slot key with
      | none, none => none
      | some spec, none => some spec
      | none, some spec => some spec
      | some outer, some inner => some (Prototype.SlotSpec.computed
          (Prototype.Method.compose outer.toMethod inner.toMethod))
    method.map fun spec => ⟨key, spec, fun _ => inferInstance⟩
  { slots, defaults := parent.defaults ++ child.defaults }

/-- Merge direct extensions and local orders without inheriting the input
identities. Suffix policy is explicit, since the paper gives no merge rule
for conflicting suffix flags. Inputs are most-specific first. -/
def Specification.fuse [DecidableEq Key]
    (specifications : List (Specification Key Value))
    (suffix : Bool := false) : Specification Key Value :=
  { declaration := specifications.foldr
      (fun spec inherited => spec.declaration.compose inherited) Declaration.empty
    parentOrders := specifications.flatMap (·.parentOrders)
    suffix }

inductive SpecificationFusionError where
  | c4 (error : C4.Error)
  | repeatedSource (name : String)
  | sourceInAncestry (name : String)
  deriving Repr

/-- Fuse explicitly selected specifications from one family into a fresh
identity. Reject a selected source remaining in the merged ancestry: its
direct extension would otherwise run both there and in the fused finalizer.
No opaque function equality or cross-family identity inference is required. -/
def Memoized.fuseSpecifications {Key : Type u} {Value : Key → Type v}
    [DecidableEq Key] [BEq Key] [LawfulBEq Key] [Hashable Key]
    (family : Memoized Key Value) (name : String) (sources : List String)
    (suffix : Bool := false) :
    Except SpecificationFusionError (Memoized Key Value) := do
  if (family.plan.schema.graph.findNode? name).isSome then
    throw (.c4 (.duplicateNode name))
  let (_, reversed) ← sources.foldlM (fun (seen, specs) source => do
    if seen.contains source then throw (.repeatedSource source)
    let some node := family.plan.schema.graph.findNode? source |
      throw (.c4 (.unknownNode source))
    let spec : Specification Key Value :=
      { declaration := (family.plan.schema.declaration source).getD Declaration.empty
        parentOrders := node.parentOrders
        suffix := node.suffix }
    return (seen.insert source, spec :: specs))
    (({} : Std.HashSet String), ([] : List (Specification Key Value)))
  let spec := Specification.fuse reversed.reverse suffix
  let plan ← (LeanPoo.mixC4 family.plan.schema
    { name, parentOrders := spec.parentOrders, suffix := spec.suffix }
    spec.declaration).mapError .c4
  for source in sources do
    if plan.precedence.contains source then
      throw (.sourceInAncestry source)
  return family.rebuild plan

end LeanPoo.Object
