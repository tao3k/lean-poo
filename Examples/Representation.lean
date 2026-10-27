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

/-- Repeated methods count toward promotion even when only one name is present. -/
def repeated : List (String × Int) := List.replicate 8 ("fee", 1)
example : pack repeated = .small repeated := by decide
example : pack (repeated ++ [("extra", 0)]) = .tree (repeated ++ [("extra", 0)]) true := by decide
example : ((pack repeated).put "fee" 7).entries = ("fee", 7) :: List.replicate 7 ("fee", 1) := by decide

/-- One multi-round service trace promotes, removes all duplicates and demotes. -/
def revisions : List (Edit Int) := [.put "extra" 0, .put "fee" 7, .remove "fee", .put "capacity" 30]
example : (revisions.foldl editStorage (pack repeated)).entries = [("extra", 0), ("capacity", 30)] := by decide
example : searchWork repeated "missing" = 8 := by decide
example : searchWork repeated "fee" = 1 := by decide

/-- Tree-only construction stays tree-only across writes/removal, regardless of size. -/
example : packWith false original = .tree original false := by decide
example : ((packWith false original).put "extra" 0).compact = false := by decide
example : ((packWith true original).remove "fee").compact = true := by decide

#print axioms revision_trace
#print axioms compact_search_bound

/-- Same-shape service switching reuses an offset while the old value guard fails. -/
example : readPrepared totalSite (service 2 4 20 93)
    (fun _ => (Except.error "must not evaluate" : Except String Int)) = .ok 93 := by
  apply readPrepared_current <;> rfl

/-- Symbolic resolution is skipped only for the attested shared shape. -/
example : resolutionWork totalSite (service 2 4 20 93) = 0 := by rfl

/-- Opaque checked Functions come from the new receiver without Function equality. -/
example (f : Nat → Nat) : readPrepared totalSite
    (⟨2,4,20,["total","capacity"],fun _ => some f⟩ : View (Nat → Nat))
    (fun _ => (Except.error "unused" : Except String (Nat → Nat))) = .ok f := by
  apply readPrepared_current <;> rfl

/-- Tracked evaluation cannot force a refused layout-preparation branch. -/
example : selectRead true (fun _ => (Except.ok (11 : Int) : Except String Int))
    (fun _ => .error "layout must stay lazy") = .ok 11 := rfl

end LeanPoo.Examples.Representation
