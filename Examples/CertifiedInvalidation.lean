import LeanPoo.Proof.Invalidation

namespace LeanPoo.Examples.CertifiedInvalidation

private def graph : C4.Graph :=
  { nodes := [{ name := "Combined", parentOrders := [["Left", "Right"]] },
      { name := "Left", parentOrders := [["Base"]] },
      { name := "Right", parentOrders := [["Base"]] },
      { name := "Base" }, { name := "Unrelated" }] }

private def impact : Except C4.RankError (List String) := do
  let result ← Proof.certifyInvalidation graph ["Base"]
  return result.names

#guard match impact with
  | .ok names => names == ["Base", "Left", "Right", "Combined"]
  | .error _ => false

#eval impact

-- The returned names carry an exact proof for paths of any length.
example (changed : List String) (result : Proof.CertifiedInvalidation graph changed)
    (name : String) : name ∈ result.names ↔
      ∃ origin ∈ changed, ∃ steps, Proof.Descendant graph origin steps name :=
  result.characterizes name

end LeanPoo.Examples.CertifiedInvalidation
