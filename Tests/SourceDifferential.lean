import LeanPoo.Prototype.Record
import LeanPoo.Prototype.Object
import LeanPoo.Prototype.Class
import LeanPoo.Prototype.AVL
import LeanPoo.Prototype.C3

/-! Actual Lean observations for direct comparison with the 24 pinned
Racket checks. The JSON normalization preserves symbols, dotted pairs,
integral complex coordinates, tree layout and cached AVL heights. -/
open LeanPoo.Prototype
open Lean
namespace LeanPoo.Tests.SourceDifferential

private def list (values : List Json) := Json.arr values.toArray
private def symbol (name : String) := Json.mkObj [("symbol", .str name)]
private def pair (left right : Json) := Json.mkObj [("pair", list [left, right])]
private def complex (value : Int × Int) := Json.mkObj [("complex", list [toJson value.1, toJson value.2])]
private def emit (line : Nat) (value : Json) : IO Unit :=
  IO.println ("POOF-DIFFERENTIAL " ++ (Json.mkObj [("line", toJson line), ("canonical", value)]).compress)

inductive Key where | x | y | z deriving DecidableEq
private abbrev Value : Key → Type | .x | .y => Int | .z => Int × Int
private abbrev Rec := Record Key Value
private abbrev Layer := Proto Rec Rec Rec
private def base : Rec := { lookup := fun key => match key with
  | .x => some 1 | .y => some 2 | .z => none }
private def x3 : Layer := Record.slot .x (3 : Int)
private def doubleX : Layer := Record.modify .x (fun x : Int => 2 * x)
private def zXY : Layer := Record.compute .z fun self =>
  ((self.lookup .x).getD 0, (self.lookup .y).getD 0)
private unsafe def close (layer : Layer) : Rec := Record.instantiate layer base
private def xy (record : Rec) := list [toJson ((record.lookup .x).getD 0), toJson ((record.lookup .y).getD 0)]
private def xyz (record : Rec) := list [toJson ((record.lookup .x).getD 0),
  toJson ((record.lookup .y).getD 0), complex ((record.lookup .z).getD (0, 0))]

private def treeJson : Tree Symbol String → Json
  | .empty => list []
  | .node left key value height right =>
    let entry := pair (symbol key.name) (.str value)
    let payload := match height with | none => list [entry] | some height => pair entry (toJson height)
    list [treeJson left, payload, treeJson right]

private def comparison (value : Except String Ordering) : Json :=
  symbol (match value.toOption with | some .lt => "<" | some .eq => "=" | some .gt => ">" | none => "error")

private def evenLayer : Proto (FixedFunction Int Int) (FixedFunction Int Int) (FixedFunction Int Int) :=
  fun self inherited => FixedFunction.ofFun fun x => if x < 0 then self (-x) else inherited x
private def cube : Proto (FixedFunction Int Int) (FixedFunction Int Int) (FixedFunction Int Int) :=
  fun _ inherited => FixedFunction.ofFun fun x => let y := inherited x; y * y * y

private unsafe def run : IO Unit := do
  emit 272 (xy base)
  emit 328 (xy (close x3))
  emit 332 (xyz (close zXY))
  emit 336 (xy (close doubleX))
  emit 344 (xyz (close (compose zXY (compose doubleX x3))))
  emit 352 (list ([compose zXY (compose doubleX x3), compose doubleX (compose zXY x3),
    compose doubleX (compose x3 zXY)].map fun layer => complex (((close layer).lookup .z).getD (0, 0))))
  emit 362 (list ([compose (compose zXY doubleX) x3, compose (compose doubleX zXY) x3,
    compose (compose doubleX x3) zXY].map fun layer => complex (((close layer).lookup .z).getD (0, 0))))
  emit 376 (toJson [((close (compose doubleX x3)).lookup .x).getD 0,
    ((close (compose x3 doubleX)).lookup .x).getD 0])
  emit 456 (toJson (((Record.instantiate x3 Record.empty).lookup .x).getD 0))
  emit 465 (xy (Record.instantiate (compose (Record.slot .x (1 : Int)) (Record.slot .y (2 : Int))) Record.empty))
  let numbers := OrderOps.instantiate (DelayedProto.compose OrderOps.compareMixin OrderOps.number)
  let strings := OrderOps.instantiate (DelayedProto.compose OrderOps.compareMixin OrderOps.string)
  let symbols := OrderOps.instantiate (OrderOps.symbol strings)
  emit 715 (list [toJson (numbers.less 23 42), comparison (numbers.compare 8 4),
    toJson (strings.less "Hello" "World"), comparison (strings.compare "Foo" "FOO"), comparison (strings.compare "42" "42")])
  let s := Symbol.mk
  emit 731 (list [toJson (symbols.less (s "aardvark") (s "aaron")), toJson (symbols.equal (s "zzz") (s "zzz")),
    toJson (symbols.greater (s "aa") (s "a")), comparison (symbols.compare (s "alice") (s "bob")),
    comparison (symbols.compare (s "b") (s "c")), comparison (symbols.compare (s "c") (s "a"))])
  let bst : Dictionary Symbol String (List String) := Dictionary.instantiate symbols Dictionary.binaryTree
  let avl : Dictionary Symbol String (List String) := Dictionary.instantiate symbols
    (DelayedProto.compose Dictionary.avlRebalance Dictionary.binaryTree)
  let entries := [(s "a", "I"), (s "b", "II"), (s "c", "III"), (s "d", "IV"), (s "e", "V")]
  let plain ← IO.ofExcept (bst.fromList entries)
  let balanced ← IO.ofExcept (avl.fromList entries)
  emit 792 (treeJson plain)
  emit 839 (treeJson balanced)
  for (dictionary, tree, line) in [(bst, plain, 797), (avl, balanced, 842)] do
    let values ← IO.ofExcept ((["a", "b", "c", "d", "e", "z"].map s).mapM (dictionary.ref tree))
    emit line (list (values.map fun value => match value with | none => .bool false | some value => .str value))
  let absoluteCube := instantiate (compose evenLayer (compose cube
    (constant (FixedFunction.ofFun fun x : Int => x)))) (FixedFunction.ofFun fun _ : Int => (0 : Int))
  emit 869 (toJson (([3, -2, 0, -1] : List Int).map absoluteCube))
  let plus : DelayedProto Nat Nat Nat := fun _ inherited => inherited.get + 1
  let twice : DelayedProto Nat Nat Nat := fun _ inherited => inherited.get * 2
  emit 878 (toJson [(DelayedProto.instantiate (DelayedProto.compose plus twice) (Thunk.pure 30)).get,
    (DelayedProto.instantiate (DelayedProto.compose twice plus) (Thunk.pure 30)).get])
  emit 1895 (toJson ([Sum.inl [], Sum.inl ["1"], Sum.inl ["a", "b", "c"], Sum.inr "nil"].map C3.notNull))
  emit 1896 (list ((C3.removeNulls [["a", "b", "c"], [], ["d", "e"], [], ["f"], [], []]).map
    fun names => list (names.map symbol)))
  let graph : C3.Graph := [("O", []), ("A", ["O"]), ("B", ["O"]), ("C", ["O"]), ("D", ["O"]), ("E", ["O"]),
    ("K1", ["A", "B", "C"]), ("K2", ["D", "B", "E"]), ("K3", ["D", "A"]), ("Z", ["K1", "K2", "K3"])]
  let orders ← IO.ofExcept ((C3.linearizeMany graph ["O", "A", "K1", "Z"]).mapError (fun _ => "C3 error"))
  emit 1897 (list (orders.map fun order => list (order.map symbol)))
  let empty : Record String (fun _ => Int) := Record.empty
  let layer := DelayedProto.compose (Object.recordSlotGen "a" (fun _ _ => some (1 : Int)))
    (DelayedProto.compose (Object.recordSlotGen "b" (fun _ _ => some (2 : Int))) (Object.recordSlotGen "c" (fun _ _ => some (3 : Int))))
  let object := Object.ofPrototype layer (Thunk.pure empty)
  emit 1974 (toJson (["a", "b", "c"].map fun key => (object.value.lookup key).getD 0))
  let foo := Object.ofPrototype (Object.recordSlotGen "foo" (fun _ _ => some (1 : Int))) (Thunk.pure empty)
  emit 1975 (toJson ((foo.value.lookup "foo").getD 0))
  let descriptor := ((Descriptor.top "Int" toString : Descriptor Int).withJson).listOf
  emit 1976 (toJson ([descriptor.decodeJson (.arr #[]), descriptor.decodeJson (toJson ([1, 2, 3] : List Int)),
    descriptor.decodeJson (.arr #[toJson (1 : Int), .str "a", toJson (2 : Int)]),
    descriptor.decodeJson (Json.mkObj [("car", toJson (1 : Int)), ("cdr", toJson (2 : Int))])].map Except.isOk))

#eval run
end LeanPoo.Tests.SourceDifferential
