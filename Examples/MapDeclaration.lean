import LeanPoo.Object.Memo

open LeanPoo

private def entries : Std.DHashMap Nat (fun _ => Nat) :=
  ({} : Std.DHashMap Nat (fun _ => Nat)).insert 3 30 |>.insert 1 10 |>.insert 2 20

private def declaration : Object.Declaration Nat (fun _ => Nat) :=
  Object.Declaration.fromMap entries (· <= ·)

#guard declaration.slots.map Object.Entry.key == [1, 2, 3]

private def schema : Object.Schema Nat (fun _ => Nat) :=
  { graph := { nodes := [{ name := "Base" }] }
    declaration := fun name => if name == "Base" then some declaration else none }

#guard match Object.compile schema "Base" with
  | .ok plan =>
    let object := plan.memoize
    object.read 1 == some 10 && object.read 2 == some 20 &&
      object.read 3 == some 30 && object.read 4 == none
  | .error _ => false
