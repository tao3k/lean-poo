import LeanPoo.C4.Linearize

open LeanPoo.C4

private def base : List Node :=
  [{ name := "Object", suffix := true },
   { name := "Named", parentOrders := [["Object"]], suffix := true },
   { name := "Other" }]

private def graph (order : List String) : Graph :=
  { nodes := base ++ [{ name := "Child", parentOrders := [order] }] }

#guard match linearize (graph ["Named", "Object"]) "Child" with
  | .ok order => order == ["Child", "Named", "Object"]
  | .error _ => false

#guard match linearize (graph ["Other", "Named", "Object"]) "Child" with
  | .ok order => order == ["Child", "Other", "Named", "Object"]
  | .error _ => false

#guard match linearize (graph ["Object", "Named"]) "Child" with
  | .error .suffixOrderViolation => true
  | _ => false

#guard match linearize (graph ["Named", "Other", "Object"]) "Child" with
  | .error .suffixOrderViolation => true
  | _ => false
