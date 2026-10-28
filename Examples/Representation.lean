import LeanPoo.Prototype.RepresentationIndex
import LeanPoo.Prototype.RepresentationNames
import LeanPoo.Prototype.SlotSpec

/-! A shared-service shape changes across edits, topology replacement and retry.
These source laws complement executable Gerbil C3/FUN/contract controls; they
make no claim about collector history or physical allocation performance. -/
namespace LeanPoo.Examples.Representation
open Prototype.Representation

/-- A final-self override cuts 64 opaque inherited builders, retaining its suffix. -/
def overriddenSpecs : List (Prototype.SlotSpec Int Int) :=
  List.replicate 64 (.computed (fun _ next => 100 + next ())) ++
    [.self (fun owner => owner * 3), .modify (fun value => value + 3)]
example : (overriddenSpecs.foldl Prototype.SlotSpec.push []).length = 2 := by decide
example : Prototype.SlotSpec.compile (overriddenSpecs.foldl Prototype.SlotSpec.push [])
    2 (fun _ => -1) () = 9 := by decide
example : Prototype.SlotSpec.preparationWork overriddenSpecs = 68 := by decide
example : Prototype.SlotSpec.builderWork overriddenSpecs = 66 := by decide
example : Prototype.SlotSpec.builderWork
    (overriddenSpecs.foldl Prototype.SlotSpec.push []) = 2 := by decide
example : Prototype.SlotSpec.prepare (Self := Unit) (α := Int)
    [.error "malformed", .ok (.constant 7)] = .error "malformed" := rfl
example (f : Nat → Nat) : Prototype.SlotSpec.compile
    (Prototype.SlotSpec.push [] (.constant f)) () (fun _ => f) () = f := rfl
example : Prototype.SlotSpec.compile
    (Prototype.SlotSpec.push [] (.thunk (fun _ => (Except.error "retry" : Except String Bool))))
    () (fun _ => .ok false) () = .error "retry" := rfl

/-- A forged cyclic metadata spine is checked against a finite private directory. -/
def cyclicNames (_ : Nat) : NameCell := ⟨"callback", .cell 0⟩
example : matchesNameSpine cyclicNames (.cell 0) ["callback"] = false := by decide
example : nameSpineWork cyclicNames (.cell 0) ["callback", "callback"] = 3 := by decide
example : matchesNameSpine cyclicNames .invalid ["callback"] = false := rfl
example : namesCopyCells 64 1 1 = 128 := rfl
example : namesCopyCells 64 0 0 = 0 := rfl

/-- Repairing structural metadata retains a warmed false cell and preparation ID. -/
def namesAuthority : NamesAuthority Bool :=
  ⟨["enabled"],4,17,[3],⟨1,4,99,["enabled"],fun name => if name = "enabled" then some false else none⟩⟩
/-- The warmed static site retains the original false-valued cell across metadata repair. -/
def enabledSite : Site := ⟨1,4,99,["enabled"],"enabled",0,rfl⟩
example : read enabledSite (refreshNames namesAuthority 18).view = some false := by decide
example : (refreshNames namesAuthority 18).preparation = [3] := rfl
example : namesCurrent (refreshNames namesAuthority 18)
    ⟨true,4,17,["enabled"],.cell 0⟩ = false := by decide
example : (replaceExposedNames (exposeNames namesAuthority) ["client-only"]).1.names =
    ["enabled"] := rfl

/-- Repeated methods and unrelated fields retain sparse ordinals after deletion. -/
def indexedMethods : List (Nat × (String × Int)) :=
  [(0,("tariff",7)), (1,("enabled",0)), (2,("tariff",8)), (19,("callback",1))]

/-- The name index covers both tariff contributions, independently of other names. -/
theorem indexedMethods_valid : IndexMatches indexedMethods "tariff" [0,2] := by
  intro entry present
  simp [indexedMethods] at present
  rcases present with rfl | rfl | rfl | rfl <;> simp

example : orderedPayloads (erasePositions indexedMethods [0,2]) =
    [("enabled",0), ("callback",1)] := by decide
example : first (orderedPayloads (erasePositions indexedMethods [0,2])) "tariff" = none :=
  erasePositions_absent _ _ _ indexedMethods_valid
example : indexedEraseWork (matchingPositions indexedMethods "tariff") = 4 := by decide

/-- Live count two is occupied; a high-water ordinal is required for reinsertion. -/
example : ([(0,("enabled",false)), (2,("other",true))].map Prod.fst).contains 2 = true := by decide
example : PositionsBelow indexedMethods 20 := by
  intro entry present
  simp [indexedMethods] at present
  rcases present with rfl | rfl | rfl | rfl <;> decide

/-- Functions are opaque payload identities; no function equality oracle is needed. -/
example (f g : Nat → Nat) :
    orderedPayloads (erasePositions [(0,("method",f)), (8,("kept",g))] [0]) = [("kept",g)] := by
  simp [orderedPayloads, erasePositions]

/-- The existing sealed preflight preserves the original sparse source on refusal. -/
example (active : Bool) :
    Object.publishEdit indexedMethods
      (Object.guardedEdit true active indexedMethods (fun entries => erasePositions entries [0,2])) = indexedMethods :=
  Object.publishEdit_sealed _ _ _

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

/-- A pinned opaque hook survives unavailable unrelated metadata after invalidation. -/
example (hook : Nat → Nat) : selectLayoutRead false false true
    (fun _ => (Except.ok hook : Except String (Nat → Nat)))
    (fun _ => .error "retired layout") (fun _ => .error "metadata refused") = .ok hook := rfl

/-- The same cold state grants no bypass to a non-anchor field. -/
example : selectLayoutRead false false false
    (fun _ => (Except.ok (7 : Int) : Except String Int))
    (fun _ => .ok 9) (fun _ => .error "metadata refused") = .error "metadata refused" := rfl

/-- Successful retry can prepare the revised value; no old value was installed. -/
example : selectLayoutRead false false false
    (fun _ => (Except.ok (7 : Int) : Except String Int))
    (fun _ => .ok 7) (fun _ => .ok 9) = .ok 9 := rfl

/-- A cold service batch uses ordinary lazy demand, preserving receiver order. -/
example : demandBatch false totalSite [service 1 0 1 33, service 2 0 2 63]
    (fun view => match view.fields "total" with
      | some n => (Except.ok n : Except String Int)
      | none => .error "missing") = .ok [33, 63] := by rfl

/-- An original refusal stops the complete source batch before later results. -/
example : demandBatch false totalSite [service 1 0 1 33, service 2 0 2 63]
    (fun view => if view.owner = 1 then (Except.error "refused" : Except String Int)
      else .ok 63) = .error "refused" := by rfl

/-- Retrying with current post-revision views observes the new totals. -/
example : demandBatch false totalSite [service 1 2 3 53, service 2 2 4 103]
    (fun view => match view.fields "total" with
      | some n => (Except.ok n : Except String Int)
      | none => .error "missing") = .ok [53, 103] := by rfl

/-- A warmed false value can remain unpromoted until the first indexed demand. -/
example : readPrepared totalSite (deferCells
    (⟨2,3,7,["total","capacity"],fun _ => some false⟩ : View Bool))
    (fun _ => (Except.ok false : Except String Bool)) = .ok false :=
  readPrepared_deferred _ _ _

/-- An opaque checked Function is retained exactly after successful promotion. -/
example (f : Nat → Nat) : readPrepared totalSite
    (rememberCell (deferCells
      (⟨2,3,7,["total","capacity"],fun _ => some f⟩ : View (Nat → Nat))) "total" f)
    (fun _ => (Except.error "unused" : Except String (Nat → Nat))) = .ok f := by
  apply readPrepared_remembered <;> rfl

/-- Refused demand cannot appear as a newly successful memo cell. -/
example : readPrepared totalSite (deferCells (service 2 3 7 33))
    (fun _ => (Except.error "original refusal" : Except String Int)) = .error "original refusal" :=
  readPrepared_deferred _ _ _

/-- A two-name shape still allocates cells but needs no value-table seeding probes. -/
example : seedingLookups false ["total", "capacity"] = 0 := rfl

/-- Permuted complete catalogs reuse the prior order without taking old values. -/
example : shapeMatches ["capacity", "total"] ["total", "capacity"] = true := by decide

/-- An equal-size replacement is rejected; length alone is insufficient. -/
example : shapeMatches ["capacity", "approval"] ["total", "capacity"] = false := by decide

/-- An old shape still reads the NEW receiver's false, never a former value. -/
example : (prepareFromHint
    (⟨2,3,7,["capacity","total"],fun _ => some false⟩ : View Bool)
    ["total","capacity"]).fields "total" = some false := rfl

/-- Removing a field falls back to the current catalog after a shared revision. -/
example : (prepareFromHint (service 2 3 7 33) ["total","capacity","approval"]).names =
    ["total","capacity"] := by decide

/-- Shape reuse composes with ordinary refusal and retry without new admission. -/
example : demandRead true totalSite
    (prepareFromHint (deferCells (service 2 3 7 33)) ["capacity","total"])
    (fun _ => (Except.error "original refusal" : Except String Int)) = .error "original refusal" := by
  apply demandRead_prepareFromHint
  intro value cached
  simp [deferCells] at cached

/-- Only canonical-sort entries are eliminated; complete set checks stay charged. -/
example : shapeSorts ["capacity","total"] ["total","capacity"] = 0 := by decide

/-- Loading failure stops before binding lookup, retaining the exact cause. -/
example : enterModule (fun _ => (Except.error "module refused" : Except String Unit))
    (fun _ => .ok (fun (row : List Int) => .ok row)) [1,2] =
    ([EntryStage.load], .error "module refused") := rfl

/-- A refreshed runtime binding receives the original argument row. -/
example : enterModule (fun _ => (Except.ok () : Except String Unit))
    (fun _ => .ok (fun (row : List Int) => .ok (row, false))) [1,2] =
    ([EntryStage.load, .resolve, .invoke], .ok ([1,2],false)) := rfl

/-- Standard successful module caching never memoizes business invocation results. -/
example : enterModule (fun _ => initializedResult (some (.ok ())) (fun _ => .error "unused"))
    (fun _ => .ok (fun (n : Nat) => (Except.ok (n+1) : Except String Nat))) 3 =
    ([EntryStage.load, .resolve, .invoke], .ok 4) := rfl

/-- An initialization refusal stays memoized until standard explicit reload. -/
example : initializedResult (some (.error "original")) (fun _ => (Except.ok () : Except String Unit)) =
    .error "original" := rfl

/-- Shared dependency bootstrap still performs initialization exactly once. -/
example : (modulePreparation true ["object","mop","object"]).bootstrapInitializers = 2 ∧
    (modulePreparation true ["object","mop","object"]).entryDiscoveries = 0 := by decide

/-- The dynamic reference retains each distinct common dependency's discovery. -/
example : (modulePreparation false ["object","mop","object"]).entryDiscoveries = 2 := by decide


/-- Different service extensions put the common total at different offsets. -/
def compactOffset : Offset "total" := ⟨["total", "capacity"], 0, rfl⟩
/-- A policy-bearing service has the same requested field in a different layout. -/
def policyOffset : Offset "total" := ⟨["policy", "total", "capacity"], 1, rfl⟩
/-- Two successful demands close this finite descriptor working set. -/
def serviceOffsets : Offsets "total" :=
  (({} : Offsets "total").remember compactOffset).remember policyOffset

/-- Alternating known layouts removes both name lookups after warming. -/
example : serviceOffsets.namedWork compactOffset.names = 0 ∧
    serviceOffsets.namedWork policyOffset.names = 0 := by decide

/-- A third shape is not admitted by a two-entry history. -/
example : serviceOffsets.namedWork ["audit", "total"] = 1 := by decide

/-- Revision/owner changes never make old values authoritative at a reused offset. -/
example : readOffsets serviceOffsets
    (⟨99, 7, 200, compactOffset.names, fun key => if key = "total" then some false else none⟩ : View Bool)
    (fun _ => (Except.error "unused" : Except String Bool)) = .ok false := by
  apply readOffsets_current (index := 0) <;> rfl

/-- Function cells are delivered unchanged, without a decidable equality on functions. -/
example (f : Nat → Nat) : readOffsets serviceOffsets
    (⟨99, 8, 201, policyOffset.names, fun key => if key = "total" then some f else none⟩ : View (Nat → Nat))
    (fun _ => (Except.error "unused" : Except String (Nat → Nat))) = .ok f := by
  apply readOffsets_current (index := 1) <;> rfl

/-- Uncomputed cells retain the ordinary lazy refusal, even for a known descriptor. -/
example : readOffsets serviceOffsets
    (⟨99, 9, 202, policyOffset.names, fun _ => none⟩ : View Nat)
    (fun _ => (Except.error "original refusal" : Except String Nat)) = .error "original refusal" :=
  readOffsets_lazy _ _ _ rfl

/-- Failed recomputation preserves the complete prior descriptor history. -/
example : serviceOffsets.publish (some compactOffset)
    (Except.error "original refusal" : Except String Nat) = serviceOffsets := rfl

/-- A successful third layout evicts only the older descriptor and can later rewarm. -/
example : ((serviceOffsets.remember ⟨["audit", "total"], 1, rfl⟩).remember compactOffset).resolve
    compactOffset.names = some 0 := by decide

/-- Missing-name fallback cannot create a falsely successful primary index. -/
example : (serviceOffsets.publish none (Except.ok false : Except String Bool)).primary = none := rfl

end LeanPoo.Examples.Representation
