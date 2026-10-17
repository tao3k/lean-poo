import LeanPoo.Prototype.Representation

/-! A shared-service shape changes across edits, topology replacement and retry.
These source laws complement executable Gerbil C3/FUN/contract controls; they
make no claim about collector history or physical allocation performance. -/
namespace LeanPoo.Examples.Representation
open Prototype.Representation

/-- Persistent direct contributions retain both same-name method contributions. -/
def original : List (String × Int) := [("capacity",10),("fee",1),("fee",2)]
example : putFirst original "fee" 7 = [("capacity",10),("fee",7),("fee",2)] := by decide
example : first original "fee" = some 1 := by decide
example : erase original "fee" = [("capacity",10)] := by decide

/-- One closed receiver's computed total after its shared parent has been resolved. -/
def service (owner revision token : Nat) (total : Int) : View Int :=
  ⟨owner,revision,token,["total","capacity"],fun key =>
    if key = "total" then some total else if key = "capacity" then some 10 else none⟩

/-- A successfully prepared access site certifies total's actual vector position. -/
def totalSite : Site := ⟨1,0,10,["total","capacity"],"total",0,rfl⟩
example : read totalSite (service 1 0 10 33) = some 33 := by decide
/-- An identical shape on another service cannot reuse the original receiver's cell. -/
example : read totalSite (service 2 0 10 93) = none := by decide
/-- Returning to the old total does not authorize a pre-revision guard (ABA control). -/
example : read totalSite (service 1 2 12 33) = none := by decide
/-- Replacing topology allocates a new receiver-local layout even with equal names. -/
example : read totalSite (service 1 0 11 33) = none := by decide

/-- Preparing again after a supported revision permits a fresh computation. -/
def refreshed : Site := ⟨1,2,12,["total","capacity"],"total",0,rfl⟩
example : read refreshed (service 1 2 12 63) = some 63 := by decide
/-- New slot insertion can move offsets; the new certified site supplies that index. -/
def reshaped : View Int := ⟨1,3,13,["approval","total","capacity"],fun key =>
  if key = "total" then some 93 else none⟩
/-- The old shape cannot select a value from a shifted vector index. -/
example : read refreshed reshaped = none := by decide
/-- Failed/absent computations cannot be represented as a successful value guard. -/
example : cell reshaped 0 = none := by decide

end LeanPoo.Examples.Representation
