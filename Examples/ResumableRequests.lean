import LeanPoo.Functional.RequestHandling
import LeanPoo.Prototype.LinearState

/-! A nested request descriptor drives one stateful workload batch. Input and
workload failures preserve the same cache across pure, mutable and linear uses. -/
namespace LeanPoo.Examples.ResumableRequests
open Functional Requirements Prototype
abbrev Value (_ _ : Nat) := Nat
abbrev keys : List Nat := [0,1]
def ready : Certified (Value := Value) keys (fun c data => data.1 = c+6 ∧ data.2.1 = c+1) :=
  ⟨(fun c => c+6, fun c => c+1, PUnit.unit), fun _ => ⟨rfl,rfl⟩⟩
abbrev Job := {amount : Nat // 0 < amount ∧ amount ≤ 6}
abbrev Input := (Nat × List Job) × String
abbrev Wire := (Nat × List Nat) × String
def schema : Codec Input Wire String :=
  ((Codec.identity Nat String).product
    ((Codec.identity Nat String).refine (fun amount => 0 < amount ∧ amount ≤ 6) "job outside range").list).product
      (Codec.identity String String)
def context (input : Input) := input.1.1
def load (input : Input) := (input.1.2.map Subtype.val).sum

structure Receipt where
  total : Nat
  limit : Nat
  bounded : total ≤ limit
  charge : Nat
  label : String
def serve (input : Input) (data : Snapshot ready (context input)) : Except String Receipt :=
  if bounded : load input ≤ data.val.1 then
    .ok ⟨load input, data.val.1, bounded, load input * data.val.2.1, input.2⟩
  else .error "workload exceeds limit"

def batch (requests : List Wire) (slot : ContextSlot ready) := slot.callBatch schema context serve requests
def update (requests : List Wire) (slot : ContextSlot ready) : ContextSlot ready × Except String Unit :=
  let (outcome, next) := batch requests slot
  (next, outcome.map (fun _ => ()))

/-- The existing consuming-reference protocol retains precisely the failed
batch's partial cache, including a cache read by the failing workload. -/
theorem failedLinear (requests : List Wire) (slot final : ContextSlot ready) (error : String)
    (failed : batch requests slot = (.error error, final)) :
    LinearState.stepValue (some slot) (update requests) = (some final, .error error) := by
  simp [LinearState.stepValue, update, failed, Except.map]

theorem successfulLinear (requests : List Wire) (slot final : ContextSlot ready) (outputs : List Receipt)
    (success : batch requests slot = (.ok outputs, final)) :
    LinearState.stepValue (some slot) (update requests) = (none, .ok final) := by
  simp [LinearState.stepValue, update, success, Except.map]

def storedContext (slot : ContextSlot ready) : Option Nat := slot.retained.map (·.1)
def failures : List (List Wire × String × Nat) :=
  [([((0,[2,2]),"first"), ((3,[4,4]),"second"), ((8,[0,4]),"invalid"), ((9,[1]),"later")],
     "job outside range", 3),
   ([((0,[2,2]),"first"), ((3,[4,4]),"second"), ((5,[6,6]),"too-large"), ((9,[1]),"later")],
     "workload exceeds limit", 5)]

def run : IO Unit := do
  for entry in failures do
    let (requests, error, retained) : List Wire × String × Nat := entry
    let initial := ContextSlot.empty ready
    let (outcome, retainedSlot) := batch requests initial
    match outcome with
    | .error actual => unless actual == error do throw (IO.userError "wrong first workload failure")
    | .ok _ => throw (IO.userError "invalid workload batch accepted")
    unless storedContext retainedSlot == some retained do throw (IO.userError "pure failure rolled back or ran suffix")
    let mutable ← IO.mkRef initial
    let (next, status) := update requests (← mutable.get)
    mutable.set next
    match status with
    | .error actual => unless actual == error do throw (IO.userError "mutable error changed")
    | .ok _ => throw (IO.userError "mutable failure accepted")
    unless storedContext (← mutable.get) == some retained do throw (IO.userError "mutable failure cache differs")
    let linear ← LinearState.create initial
    let alias := linear
    let .error actual ← linear.step (update requests) | throw (IO.userError "linear failure accepted")
    unless actual == error do throw (IO.userError "linear error changed")
    let current ← IO.ofExcept (← alias.read)
    unless storedContext current == some retained do throw (IO.userError "failed linear alias lost partial cache")
    let retry : List Wire := [((retained,[1,2]),"retry")]
    let (resumed, final) := batch retry current
    let .ok outputs := resumed | throw (IO.userError "retry refused")
    unless outputs.length == 1 && (outputs.map (·.charge)) == [3*(retained+1)] &&
        (final.read retained).2.2 do throw (IO.userError "retry amount/cache changed")
    let (mutableNext, resumedStatus) := update retry (← mutable.get)
    mutable.set mutableNext
    unless resumedStatus.toOption.isSome && storedContext (← mutable.get) == some retained &&
        ((← mutable.get).read retained).2.2 do throw (IO.userError "mutable retry lost retained cache")
    let .ok fresh ← alias.step (update retry) | throw (IO.userError "linear retry refused")
    let saved ← IO.ofExcept (← fresh.read)
    unless storedContext saved == some retained && (← alias.read).toOption.isNone &&
        storedContext initial == none do throw (IO.userError "linear consumption or pure snapshot changed")
    IO.println s!"{error}: pure/mutable/linear retained context={retained}; retry charge={3*(retained+1)}"

#eval run

end LeanPoo.Examples.ResumableRequests
