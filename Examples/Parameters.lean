import LeanPoo.Functional.Parameters

/-! Checked positional prefixes compose with the existing delayed slot semantics.
The executable Gerbil fixture additionally tests actual C3, macro hygiene, generic
argument forwarding, Type admission, FUN effects and multiple values. -/
namespace LeanPoo.Examples.Parameters
open Functional.Parameters
abbrev Service := Template String Int

/-- Parameters remain absent until bound; unrelated data is retained exactly. -/
def service : Service := ⟨["capacity","tariff"],fun key => if key = "independent" then some 7 else none⟩

/-- Required input lookup preserves absence rather than treating it as zero. -/
def require (source : Service) (key : String) : Except String Int :=
  match source.fields key with | none => .error "missing parameter" | some value => .ok value

/-- The C3-resolved fee chain shares one final self and one base contribution. -/
def fee : LeanPoo.Prototype.Method Service Int :=
  LeanPoo.Prototype.Method.compose
    (fun self next => next () + (self.fields "tariff").getD 0)
    (LeanPoo.Prototype.Method.compose (fun _ next => next ()+1)
      (LeanPoo.Prototype.Method.compose (fun _ next => next ()+2) (fun _ _ => 5)))

/-- Admission precedes arithmetic/effects; discount uses canonical optional input. -/
def quote (source : Service) (units : Int) (discount : Option Int) : Except String Int := do
  let capacity ← require source "capacity"
  let tariff ← require source "tariff"
  unless capacity ≥ 0 && tariff ≥ 0 do throw "negative parameter"
  return units * (capacity*tariff + fee source (fun _ => 0)) - optional discount (fun _ => 0)

/-- Use the checked public specialization boundary, retaining its original failure. -/
def bind (source : Service) (values : List Int) : Except String Service :=
  match checkedSpecialize ".parameters" source values with
  | .ok next => .ok next
  | .error .declaration => .error "invalid declaration"
  | .error .excess => .error "too many arguments"

/-- Compare finite returned/error observations without equating opaque receivers. -/
def sameQuote (left right : Except String Int) : Bool :=
  match left,right with
  | .ok a,.ok b => a == b
  | .error a,.error b => a == b
  | _,_ => false

/-- Rejection has no partially specialized receiver available to a consumer. -/
def rejected (result : Except String Service) : Bool :=
  match result with | .error _ => true | .ok _ => false

/-- Full and staged construction agree, formulas use derived fields, and malformed
metadata/excess/negative inputs cannot produce an admitted quote. -/
def test : Except String Unit := do
  let staged ← bind service [10]
  unless staged.remaining == ["tariff"] && staged.fields "capacity" == some 10 &&
      staged.fields "tariff" == none && sameQuote (quote staged 2 none) (.error "missing parameter") do throw "partial closure"
  let complete ← bind staged [3]
  let direct ← bind service [10,3]
  unless complete.remaining.isEmpty && sameQuote (quote complete 2 none) (.ok 82) &&
      sameQuote (quote complete 2 (some 1)) (.ok 81) && sameQuote (quote direct 2 none) (quote complete 2 none) &&
      complete.fields "independent" == some 7 && service.fields "capacity" == none do throw "complete final self"
  let negative ← bind service [-1,3]
  unless sameQuote (quote negative 2 none) (.error "negative parameter") do throw "admission gate"
  unless rejected (bind service [1,2,3]) && rejected (bind complete [1]) do throw "excess closure"
  let invalid : Service := ⟨["capacity","capacity"],service.fields⟩
  unless rejected (bind invalid []) do throw "invalid empty specialization"
  unless bindings ["region"] ["capacity","tariff"] false == ["region"] &&
      bindings ["region"] ["capacity","tariff"] true == ["region","capacity","tariff"] do throw "lexical imports"

#print axioms Functional.Parameters.specialize_zero
#print axioms Functional.Parameters.specialize_excess
#print axioms Functional.Parameters.specialize_remaining
#print axioms Functional.Parameters.bind_append
#print axioms Functional.Parameters.specialize_append
#print axioms Functional.Parameters.bind_frame
#print axioms Functional.Parameters.invalid_declaration
#print axioms Functional.Parameters.valid_drop
#print axioms Functional.Parameters.checked_append
#print axioms Functional.Parameters.bindings_membership
#print axioms Functional.Parameters.inherited_alias
#print axioms Functional.Parameters.optional_supplied
#print axioms Functional.Parameters.optional_absent
#eval match test with
  | .ok () => IO.println "PARAMETERS-OK"
  | .error cause => throw (IO.userError cause)
end LeanPoo.Examples.Parameters
