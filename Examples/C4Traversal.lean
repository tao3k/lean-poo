import LeanPoo.C4.Linearize

open LeanPoo.C4

private def duplicateReachable : Graph :=
  { nodes := [{ name := "A" }, { name := "A" },
      { name := "Root", parentOrders := [["A"]] }] }

private def duplicateUnreachable : Graph :=
  { nodes := [{ name := "A" }, { name := "A" }, { name := "Root" }] }

private def unknownParent : Graph :=
  { nodes := [{ name := "Root", parentOrders := [["Missing"]] }] }

private def cycle : Graph :=
  { nodes := [{ name := "A", parentOrders := [["B"]] },
      { name := "B", parentOrders := [["A"]] }] }

private def diamond : Graph :=
  { nodes := [{ name := "O" },
      { name := "A", parentOrders := [["O"]] },
      { name := "B", parentOrders := [["O"]] },
      { name := "Root", parentOrders := [["A", "B"]] }] }

example : (match linearize duplicateReachable "Root" with
    | .error (.duplicateNode name) => name == "A"
    | _ => false) = true := by
  native_decide

example : (match linearize duplicateUnreachable "Root" with
    | .ok order => order == ["Root"]
    | _ => false) = true := by
  native_decide

example : (match linearize unknownParent "Root" with
    | .error (.unknownNode name) => name == "Missing"
    | _ => false) = true := by
  native_decide

example : (match linearize cycle "A" with
    | .error (.cycle name) => name == "A"
    | _ => false) = true := by
  native_decide

example : (match linearize diamond "Root" with
    | .ok order => order == ["Root", "A", "B", "O"]
    | _ => false) = true := by
  native_decide
