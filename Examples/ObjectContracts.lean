import LeanPoo.Functional.ObjectContract

/-! Executable structural checks: field inventory, type distinction, obligations,
prototype refusal, diagnostic paths and existing invocation admission. -/
namespace LeanPoo.Examples.ObjectContracts
open Functional.ObjectContract Functional.ObjectDiagnostics
/-- A stored Boolean is a value, distinct from a missing field. -/
inductive Value where
  | number (value : Int)
  | text (value : String)
  | flag (value : Bool)
  deriving Repr, DecidableEq
/-- Explicit finite view; the Scheme adapter uses its object's actual slot lookup. -/
structure Input where
  object : Bool := true
  prototype : Bool := true
  slots : List (String × Value)
/-- The model never requests an undeclared value just to inspect its name. -/
def view : View Input String Value :=
  ⟨Input.object,Input.prototype,(fun value => value.slots.map Prod.fst),
    (fun value key => value.slots.lookup key)⟩
/-- Field-specific recognizers preserve full caller-supplied diagnostic paths. -/
def number (name : String) : Field String Value String := ⟨name,fun value path =>
  match value with | .number _ => [] | _ => [.rejected path "number required"]⟩
/-- The actual service accepts ports 1 through 65535, not arbitrary integers. -/
def port : Field String Value String := ⟨"port",fun value path =>
  match value with
  | .number n => if 1 ≤ n ∧ n ≤ 65535 then [] else [.rejected path "port required"]
  | _ => [.rejected path "port required"]⟩
/-- The fixture's port recognizer has precisely the executable Scheme interval. -/
theorem port_valid_iff (value : Value) (path : List String) :
    port.check value path = [] ↔ ∃ n, value = .number n ∧ 1 ≤ n ∧ n ≤ 65535 := by
  cases value <;> simp [port]
/-- Host strings use the same ordinary recognizer boundary as other fields. -/
def text (name : String) : Field String Value String := ⟨name,fun value path =>
  match value with | .text _ => [] | _ => [.rejected path "string required"]⟩
/-- Boolean false is accepted as present; absence is checked separately by lookup. -/
def flag (name : String) : Field String Value String := ⟨name,fun value path =>
  match value with | .flag _ => [] | _ => [.rejected path "boolean required"]⟩
/-- Cross-field checks are total and deliberately independent of field recognition. -/
def relations (value : Input) (path : List String) : List (Issue String String) :=
  let capacity := match value.slots.lookup "capacity",value.slots.lookup "used" with
    | some (.number total),some (.number used) =>
      if 0 ≤ used ∧ used ≤ total then [] else [.rejected (path ++ ["used"]) "capacity exceeded"]
    | _,_ => [.rejected path "invalid capacity shape"]
  let transport := match value.slots.lookup "secure",value.slots.lookup "port" with
    | some (.flag secure),some (.number port) =>
      if !secure || port == 443 then [] else [.rejected (path ++ ["port"]) "secure port required"]
    | _,_ => [.rejected path "invalid transport shape"]
  capacity ++ transport
/-- The concrete example reuses the same four-phase contract interpretation. -/
def service : Contract Input String Value String :=
  ⟨view,[text "host",port,number "capacity",number "used",flag "secure"],true,[],relations,Or.inl rfl⟩
/-- One actual accepted configuration and two independently failing relationships. -/
def good : Input := ⟨true,true,[("host",.text "api"),("port",.number 443),("capacity",.number 10),
  ("used",.number 5),("secure",.flag true)]⟩
/-- A finite executable scenario supplements, and does not replace, general laws. -/
def check : Except String Unit := do
  unless diagnose service good ["config"] == [] do throw "valid service refused"
  let bad : Input := ⟨true,true,[("host",.text "api"),("port",.number 80),("capacity",.number 2),
    ("used",.number 3),("secure",.flag true)]⟩
  unless diagnose service bad ["config"] == [.rejected ["config","used"] "capacity exceeded",
    .rejected ["config","port"] "secure port required"] do throw "obligations lost order or paths"
  let wrongType : Input := {good with slots := [("host",.text "api"),("port",.number 443),("capacity",.number 10),
    ("used",.flag false),("secure",.flag false)]}
  unless diagnose service wrongType [] == [.rejected ["used"] "number required"] do
    throw "structural refusal entered relationships or confused false with absence"
  let missing : Input := {good with slots := [("host",.text "api"),("port",.number 443),("capacity",.number 10),
    ("secure",.flag false),("prot",.number 80)]}
  unless diagnose service missing [] == [.unknownField ["prot"],.missingField ["used"]] do
    throw "inventory or required field refused incorrectly"
  unless diagnose service {missing with prototype := false} [] == [.prototypeMismatch []] do
    throw "prototype refusal forced fields"
  for invalidPort in [0,65536] do
    let invalid : Input := {good with slots := [("host",.text "api"),("port",.number invalidPort),
      ("capacity",.number 10),("used",.number 5),("secure",.flag false)]}
    unless diagnose service invalid [] == [.rejected ["port"] "port required"] do
      throw "port recognizer diverged from the Scheme range"
  let negative : Input := {good with slots := [("host",.text "api"),("port",.number 443),
    ("capacity",.number 10),("used",.number (-1)),("secure",.flag true)]}
  unless diagnose service negative [] == [.rejected ["used"] "capacity exceeded"] do
    throw "negative integers bypassed the relation check"
  let invocation : Functional.DeclarativeMetadata.Contract Unit Input Bool := {
    input := predicate "service" service
    output := ⟨"boolean",fun _ => True,fun _ => isTrue True.intro⟩
    meaning := fun _ _ _ => True
    decide := fun _ _ _ => isTrue True.intro
    rule := .truth }
  let execute (_ : Input) : Except String (Bool × Nat) := .ok (true,7)
  match invocation.invoke execute wrongType with
  | .error (.input "service") => pure ()
  | _ => throw "existing invocation bypassed structural input admission"
  let normalized := checkedAction (fun n : Nat => .ok (n+1) : Nat → Except String Nat)
    (fun n => .ok (n*2)) 3
  match normalized with
  | .ok 8 => pure ()
  | _ => throw "consumer received original unvalidated value"
#eval match check with
  | .ok () => IO.println "OBJECT-CONTRACTS-OK"
  | .error message => throw (IO.userError message)
#print axioms port_valid_iff
#print axioms all_nil_iff
#print axioms andThen_assoc
#print axioms diagnose_nil_iff
#print axioms required_sound
#print axioms required_lookup_congr
#print axioms required_semantics_iff
#print axioms predicate_holds_iff
#print axioms checkedAction_refused
#print axioms checkedAction_accepted
end LeanPoo.Examples.ObjectContracts
