import LeanPoo.Prototype.RecordCodec
open LeanPoo.Prototype
namespace LeanPoo.Tests.PaperRecordCodec
inductive Key where | count | tag | flag deriving BEq, DecidableEq
abbrev Value : Key → Type
  | .count => Nat | .tag => String | .flag => Bool
private def fields : RecordDescription Key Value :=
  { name := "Client"
    keys := [.count,.tag,.flag]
    label := fun key => match key with | .count => "count" | .tag => "tag" | .flag => "flag"
    field := fun key => match key with
      | .count => ((Descriptor.top "Nat" toString : Descriptor Nat).withJson).refine "SmallNat" (· ≤ 16)
      | .tag => ((Descriptor.top "String" id : Descriptor String).withJson).refine "Nonempty" (!·.isEmpty)
      | .flag => (Descriptor.top "Bool" toString : Descriptor Bool).withJson }
private def record (count : Nat) (tag : String) (flag : Bool) : Record Key Value :=
  { lookup := fun key => match key with
    | .count => some count | .tag => some tag | .flag => some flag }
private def run : IO Unit := do
  let codec ← IO.ofExcept (RecordCodec.prepare fields)
  let mut contexts := 0
  for count in List.range 17 do
    for tag in ["plain","值","quote\"slash\\"] do
      for flag in [false,true] do
        let original := record count tag flag
        let wire ← IO.ofExcept (codec.encodeText original)
        let restored ← IO.ofExcept (codec.decodeText wire)
        unless restored.lookup .count == some count && restored.lookup .tag == some tag &&
            restored.lookup .flag == some flag do throw (IO.userError "generated heterogeneous text/JSON codec")
        contexts := contexts+1
  let valid ← IO.ofExcept (codec.encodeJson (record 3 "yes" true))
  let malformed := [Lean.Json.mkObj [("count",Lean.toJson (3 : Nat)),("tag",.str "yes")],
    Lean.Json.mkObj [("count",Lean.toJson (3 : Nat)),("tag",.str "yes"),("flag",.bool true),("extra",.null)],
    Lean.Json.mkObj [("count",.str "wrong"),("tag",.str "yes"),("flag",.bool true)],
    Lean.Json.mkObj [("count",Lean.toJson (17 : Nat)),("tag",.str "yes"),("flag",.bool true)],
    Lean.Json.mkObj [("count",Lean.toJson (3 : Nat)),("tag",.str ""),("flag",.bool true)],.arr #[]]
  for raw in malformed do
    unless !(codec.decodeJson raw).isOk do throw (IO.userError "bad generated record wire admitted")
  unless !(codec.encodeJson (record 17 "yes" true)).isOk &&
      !(codec.encodeJson (Record.empty : Record Key Value)).isOk && (codec.decodeJson valid).isOk do
    throw (IO.userError "generated encode admission")
  let duplicate := { fields with label := fun _ => "same" }
  let blank := { fields with label := fun _ => "" }
  let repeated := { fields with keys := [.count,.count] }
  unless !(RecordCodec.prepare duplicate).isOk && !(RecordCodec.prepare blank).isOk &&
      !(RecordCodec.prepare repeated).isOk do throw (IO.userError "ambiguous field labels admitted")
  let noCodec : RecordDescription Unit (fun _ => Nat) :=
    { name := "NoCodec", keys := [()], label := fun _ => "value", field := fun _ => Descriptor.top "Nat" toString }
  unless !(RecordCodec.prepare noCodec).isOk do throw (IO.userError "missing codec admitted")
  let empty : RecordDescription Unit (fun _ => Nat) := { noCodec with keys := [] }
  let emptyCodec ← IO.ofExcept (RecordCodec.prepare empty)
  unless (emptyCodec.decodeJson (Lean.Json.mkObj [])).isOk &&
      !(emptyCodec.decodeJson (Lean.Json.mkObj [("extra",.null)])).isOk do throw (IO.userError "empty record codec")
  let original := record 3 "old" false
  let changed ← IO.ofExcept (fields.set original .count 4)
  unless changed.lookup .count == some 4 && changed.lookup .tag == original.lookup .tag &&
      changed.lookup .flag == original.lookup .flag do throw (IO.userError "typed update frame")
  let edits : List (Sigma Value) := [⟨.count, 5⟩, ⟨.tag, "new"⟩]
  let patched ← IO.ofExcept (fields.patch original edits)
  unless patched.lookup .count == some 5 && patched.lookup .tag == some "new" &&
      patched.lookup .flag == original.lookup .flag && fields.accepts patched &&
      original.lookup .count == some 3 do throw (IO.userError "heterogeneous patch or snapshot")
  let repeated : List (Sigma Value) := [⟨.count, 5⟩, ⟨.count, 6⟩]
  let replaced ← IO.ofExcept (fields.patch original repeated)
  unless replaced.lookup .count == some 6 do throw (IO.userError "patch order")
  let badEdits : List (Sigma Value) := [⟨.count, 5⟩, ⟨.tag, ""⟩]
  unless !(fields.patch original badEdits).isOk && original.lookup .count == some 3 do
    throw (IO.userError "rejected patch returned partial state")
  unless contexts == 102 do throw (IO.userError "codec context coverage drift")
  IO.println "POOF-RECORD-CODEC-OK contexts=102 malformedWire=6 encodeRefusals=2 schemaRefusals=4 patchCases=3 unicode=true emptySchema=true"
private unsafe def prepareOnce : IO Unit := do
  let calls ← IO.mkRef (0 : Nat)
  let counted := { fields with field := fun key => unsafeBaseIO do
    calls.modify (·+1)
    return fields.field key }
  let compiled ← IO.ofExcept (RecordCodec.prepare counted)
  for count in List.range 17 do
    let raw ← IO.ofExcept (compiled.encodeJson (record count "value" true))
    let _ ← IO.ofExcept (compiled.decodeJson raw)
  unless (← calls.get) == 3 do throw (IO.userError "prepared catalog rediscovered field descriptors")
  IO.println "POOF-RECORD-CODEC-PREPARED-OK fieldDiscoveries=3 roundTrips=17"
#eval run
#eval prepareOnce
#print axioms RecordDescription.set_lookup_same
#print axioms RecordDescription.set_lookup_other
#print axioms RecordDescription.set_preserves_accepts
#print axioms RecordDescription.patch_preserves_accepts
#print axioms RecordDescription.patch_lookup_untouched
end LeanPoo.Tests.PaperRecordCodec
