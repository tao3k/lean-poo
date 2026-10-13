import LeanPoo.Functional.Codec

namespace LeanPoo.Tests.FunctionalCodec
open Functional

example (codec : Codec α wire ε) (values : List α) :
    codec.list.decode (codec.list.encode values) = .ok values := codec.list.decode_encode values

private def checked (bound : Nat) :=
  ((Codec.identity Nat String).refine (fun n => n ≤ bound) "element").list.refine
    (fun values => (values.map Subtype.val).sum ≤ bound) "total"

#eval do
  let mut cases := 0
  for bound in List.range 8 do
    for rows in (show List (List Nat) from [[], [0], [1, 1], [2, 3], [8, 0], [3, 4, 5]]) do
      let codec := checked bound
      let expected := if (show List Nat from rows).any (fun n => bound < n) then some "element"
        else if bound < (show List Nat from rows).sum then some "total" else none
      match codec.decode rows, expected with
      | .error error, some reason =>
        unless error == reason do throw (IO.userError "nested codec error priority")
      | .ok accepted, none =>
        unless codec.encode accepted == rows do throw (IO.userError "nested codec changed values")
        match codec.decode (codec.encode accepted) with
        | .error _ => throw (IO.userError "valid configuration failed roundtrip")
        | .ok recovered =>
          unless codec.encode recovered == rows do throw (IO.userError "roundtrip changed order")
      | _, _ => throw (IO.userError "codec differs from independent bounded-list control")
      cases := cases+1
  let left := (Codec.identity Nat String).refine (fun n => n ≤ 2) "left"
  let right := (Codec.identity Nat String).refine (fun n => n ≤ 1) "right"
  match (left.product right).decode (3, 2) with
  | .error "left" => pure ()
  | _ => throw (IO.userError "product must refuse left first")
  IO.println s!"FUNCTIONAL-CODEC-OK batches={cases} productErrorPriority=1"

-- Transport retains the same value-level inverse obligation for every inhabitant.
example (codec : Codec α wire ε) (forward : α → β) (backward : β → α)
    (inverse : ∀ b, forward (backward b) = b) (value : β) :
    (codec.transport forward backward inverse).decode
      ((codec.transport forward backward inverse).encode value) = .ok value :=
  (codec.transport forward backward inverse).decode_encode value

#print axioms Codec.refine
#print axioms Codec.refine_decode_error
#print axioms Codec.refine_rejected
#print axioms Codec.product
#print axioms Codec.list
#print axioms Codec.transport
#print axioms Codec.represent_decode
#print axioms Codec.toJson_roundtrip
end LeanPoo.Tests.FunctionalCodec
