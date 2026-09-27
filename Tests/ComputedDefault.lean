import LeanPoo.Object.Class

open LeanPoo

private def classSpec : Object.ClassSpec String (fun _ => Nat) :=
  { name := "ComputedDefault"
    rules :=
      [{ key := "total"
         default := some 7
         compute := some (.computed fun _ inherited =>
           some ((inherited ()).getD 0 + 1)) }] }

#guard match classSpec.instantiate with
  | .ok object => object.read "total" == some 8
  | .error _ => false

#guard (classSpec.toDeclaration.default "total") == some 7
