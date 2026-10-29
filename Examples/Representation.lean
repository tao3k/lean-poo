import LeanPoo.Prototype.ValueStorage
import LeanPoo.Prototype.RepresentationIndex
import LeanPoo.Prototype.RepresentationNames
import LeanPoo.Prototype.RepresentationDeclarations
import LeanPoo.Prototype.SlotSpec

/-! A shared-service shape changes across edits, topology replacement and retry.
These source laws complement executable Gerbil C3/FUN/contract controls; they
make no claim about collector history or physical allocation performance. -/
namespace LeanPoo.Examples.Representation
open Prototype.Representation

/-- Effects visit duplicate keys in source order, independent of snapshot copying. -/
def traversalRows : List (String × Bool) := [("a",false),("a",true),("b",false)]
example : visitEntries (fun seen name value => (Except.ok (seen ++ [(name,value)]) :
    Except String (List (String × Bool)))) (entrySnapshot traversalRows) [] =
      .ok traversalRows := rfl
example : entryKeys traversalRows = ["a","a","b"] := rfl
example : visitEntries (fun (_ : Nat) _ (_ : Bool) => (Except.error false : Except Bool Nat))
    traversalRows 0 = .error false := rfl
example (f : Nat → Nat) : visitEntries
    (fun seen _ value => (Except.ok (value :: seen) : Except String (List (Nat → Nat))))
    [("callback",f)] [] = .ok [f] := rfl
example : (composeMetadata (packWith true traversalRows) (packWith true [])).2.2.derived = none := rfl
/-- Width 64 includes two target contributions and two direct default entries. -/
example : compositionExportCells 66 2 false = 136 := rfl
example : compositionExportCells 66 2 true = 0 := rfl

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

/-- A forged reflection entry cannot replace a false descriptor in the real catalog. -/
example : (((exposeCatalog (packWith true [("enabled", false)] : Storage Bool)).replacePublic
    [("forged", true)]).root.entries) = [("enabled", false)] := rfl

/-- Function descriptors survive public-view replacement without forcing their bodies. -/
example (f g : Nat → Nat) :
    first (((exposeCatalog (packWith false [("callback", f)] : Storage (Nat → Nat))).replacePublic
      [("callback", g)]).root.entries) "callback" = some f := rfl

/-- Constructor grammar failure is distinct from a later descriptor refusal. -/
example : captureCatalog true (.error "symbolic specification required" : Except String (List (String × Nat))) =
    .error "symbolic specification required" := rfl

/-- One refused descriptor prevents publication of an earlier private scratch value. -/
example : prepareCatalog (packWith false [("first", 1), ("refused", 2)] : Storage Nat) 0
    (fun state name value => if name = "refused" then .error "descriptor refusal" else .ok (state + value)) =
      (.error "descriptor refusal" : Except String (Storage Nat × Nat)) := rfl

/-- A fresh retry observes both contributions; no partial result is reused. -/
example : prepareCatalog (packWith true [("first", 1), ("refused", 2)] : Storage Nat) 0
    (fun state _ value => .ok (state + value) : Nat → String → Nat → Except String Nat) =
      .ok (packWith true [("first", 1), ("refused", 2)], 3) := rfl

/-- Sharing an empty root cannot make a persistent successor mutate it. -/
example : ((packWith false [] : Storage Bool).entries,
    ((packWith false ([] : List (String × Bool))).put "enabled" false).entries) =
      ([], [("enabled", false)]) := rfl

/-- A hidden most-specific declaration remains selected ahead of a public ancestor. -/
example : selectDeclarations [("value", true), ("value", false)] = [("value", true)] := by decide

/-- A later getter refusal wins over an earlier getter's own refusal. -/
example : checkVisibility (fun n => if n = 2 then .error "later" else .error "earlier")
    [("a", 1), ("b", 2)] = (.error "later" : Except String (List (String × Nat))) := rfl

/-- Observed current preparation is required even when the warm directory was empty. -/
example : chooseVisible true (some ([] : List (String × Bool)))
    (fun _ => .error "current refusal") = (.error "current refusal" : Except String (List (String × Bool))) := rfl

/-- Public visibility is not a reusable result of concrete value admission. -/
example : (declarationWork false true true).valueChecks = 1 := rfl

/-- A source edit between visibility preparation and publication refuses the directory. -/
example : finishVisibility 7 8 (.ok [("enabled", false)]) =
    (.error "object changed during declaration reflection" : Except String (List (String × Bool))) := rfl

/-- A corrected retry preserves false without interpreting it as no visible cache. -/
example : finishVisibility 9 9 (.ok [("enabled", false)]) =
    (.ok [("enabled", false)] : Except String (List (String × Bool))) := rfl

/-- Existing owner-names evidence rejects a changed source even if field names agree. -/
example (authority : NamesAuthority Bool) (read : NamesEvidence)
    (changed : read.revision ≠ authority.revision) : namesCurrent authority read = false :=
  namesCurrent_revision authority read changed

/-- One unique current catalog needs no semantic deduplication. -/
example : selectDeclarations [("callback", false), ("enabled", true)] =
    [("callback", false), ("enabled", true)] := by decide

/-- All-pass reuse keeps the exact logical root, including a Function payload. -/
example (f : Nat → Nat) : filteredCatalog (packWith true [("callback", f)]) [("callback", f)] =
    packWith true [("callback", f)] := filteredCatalog_all_pass _

/-- Partial filtering still retains false payloads in their original order. -/
example : (filteredCatalog (packWith true [("enabled", false), ("hidden", true)])
    [("enabled", false)]).entries = [("enabled", false)] := rfl

/-- Sharing an all-pass root cannot authorize a query from an older source revision. -/
example : finishVisibility 4 5 (.ok [("enabled", false)]) =
    (.error "object changed during declaration reflection" : Except String (List (String × Bool))) := rfl

/-- Reusing builders does not remove the successful field's concrete value check. -/
example : catalogRebuilds true true = 0 ∧ (declarationWork false true true).valueChecks = 1 := ⟨rfl,rfl⟩

/-- Reverse folding keeps false and Function payloads without input snapshots. -/
example (f : Nat → Nat) : foldVisibility (fun _ => (.ok false : Except String Bool))
    [("callback", f)] = .ok [("callback", f)] := rfl

/-- The rightmost failing getter still wins before any earlier visibility check. -/
example : foldVisibility (fun n => if n = 2 then .error "right" else .error "left")
    [("a", 1), ("b", 2)] = (.error "right" : Except String (List (String × Nat))) := rfl

/-- Eliminating a 32-entry private export removes 64 logical cells, not GC time. -/
example : visibilityExportCells 32 true = 0 ∧ visibilityExportCells 32 false = 64 := ⟨rfl,rfl⟩

/-- A foreign carrier refuses before an otherwise failing elaboration callback. -/
example : captureThenPrepareCatalog true (.error "proper list required" : Except String (List (String × Bool)))
    (0 : Nat) (fun _ _ _ => .error "hook must not run") = .error "proper list required" := rfl

/-- Retrying with a finite duplicate catalog preserves Function leaves and order. -/
example (f : Nat → Nat) :
    (captureThenPrepareCatalog true (.ok [("callback", f), ("callback", f)] :
        Except String (List (String × (Nat → Nat))))
      ([] : List String) (fun seen key _ => .ok (seen ++ [key]))).map
        (fun result => (result.1.entries, result.2)) =
      .ok ([("callback", f), ("callback", f)], ["callback", "callback"]) := rfl

/-- The same grammar cause precedes any descriptor effects under either policy. -/
example : captureThenPrepareCatalog false (.error false : Except Bool (List (String × Nat)))
    (0 : Nat) (fun count _ _ => .ok (count + 1)) = .error false := rfl

/-- Four isolated package VMs and two backends replace 3×3 within 12 slots. -/
example : parallelPreparation ⟨3,3⟩ = ⟨4,2⟩ := rfl

/-- Both configurations retain the same declared 24 GiB Scheme heap envelope. -/
example : (BuildAllocation.mk 3 3).heapGiB = 24 ∧
    (parallelPreparation ⟨3,3⟩).heapGiB = 24 := ⟨rfl,rfl⟩

/-- Small configured capacity is preserved instead of disabling its existing overlap. -/
example : parallelPreparation ⟨1,3⟩ = ⟨1,3⟩ := rfl

/-- Four bounded standard compiler sessions and two backends each keep the
same twelve active capacities as the preceding isolated package arrangement. -/
example : boundedPreparation 12 = ⟨4,2⟩ ∧
    (boundedPreparation 12).slots = (BuildAllocation.mk 4 2).slots := ⟨rfl,rfl⟩

/-- The approved frontend ceiling and unchanged CLI/backend ceilings fit the
existing root phase's configured sum. This is not a process RSS measurement. -/
example : heapLimitSum (boundedPreparation 12) 1 2 2 =
    heapLimitSum ⟨1,12⟩ 2 2 2 := rfl

/-- Six bounded sessions prepare the same distinct common import closure;
all twenty-five logical test packages remain in the declared inventory. -/
example : preparationVisits 25 ["compiler", "make", "poo", "make"] = 75 ∧
    preparationVisits 6 ["compiler", "make", "poo", "make"] = 18 := by decide

/-- Queuing one bounded part before another changes preparation order while
retaining all declared units, including repeated units within a part. -/
example (types contracts collections : List String) :
    (declaredBuildUnits [types, contracts, collections]).Perm
      (declaredBuildUnits [contracts, types, collections]) :=
  declaredBuildUnits_perm (List.Perm.swap _ _ _)

/-- Exact tick accounting includes both post-report cleanup and final reap. -/
example : admitCheckTimes (some ⟨100,110,130,190,200,210,220,230⟩) 4 8 8 =
    .ok [10,20,60,10,10,10,10] := rfl

/-- Empty/missing observations never qualify merely because a tool printed OK. -/
example : admitCheckTimes none 0 0 0 = .error "incomplete check observation" ∧
    admitCheckTimes none 1 1 1 = .error "missing check phase" := ⟨rfl, rfl⟩

/-- A validated Function cannot escape a metadata revision, even when its body
is retained by identity; no Function application is needed by the fence. -/
example (callback : Nat → Nat) :
    publishDeclaredValue 4 5 (.ok callback)
      (fun f => .ok (f 7)) = .error "object changed during declaration reflection" := by
  apply publishDeclaredValue_stale
  decide

/-- A validator's original error wins over stale success diagnostics. -/
example : publishDeclaredValue 4 5 (.error "validator-refused" : Except String Nat)
    (fun n => .ok (n + 1)) = .error "validator-refused" := rfl

/-- Repair and fresh admission may install; a refused prior request is not reused. -/
example : publishDeclaredValue 6 6 (.ok 11 : Except String Nat)
    (fun n => .ok (n + 1)) = .ok 12 := rfl

/-- Multiple immutable roots retain first-name priority across mixed backends. -/
example : (mergeCatalogs true
    [packWith true [("shared", false), ("a", true)],
     packWith false [("shared", true), ("b", false)]]).entries =
      [("shared", false), ("a", true), ("b", false)] := by decide

/-- A hidden first override suppresses its visible shared ancestor after merging. -/
example : checkVisibility (E := String) (fun (value : Bool × Nat) => .ok value.1)
    (mergeCatalogs true [packWith false [("value", (true, 1))],
      packWith true [("value", (false, 2)), ("other", (false, 3))]]).entries =
        .ok [("other", (false, 3))] := by
  simp [mergeCatalogs, entries_packWith, selectDeclarations, checkVisibility]

/-- Functions remain actual shared values; the merge never evaluates their bodies. -/
example (callback : Nat → Nat) : first (mergeCatalogs false
    [packWith true [("callback", callback)], packWith false [("callback", id)]]).entries
      "callback" = some callback := by
  rw [mergeCatalogs_first]
  simp [entries_packWith, first]

/-- Refused keys preserve a Function value and revision without invoking it. -/
example (callback : Nat → Nat) : Object.publishEdit (callback, 7)
    (checkedKeyEdit (.error "symbol-refused") false false (callback, 7)
      (fun _ _ => (id, 8))) = (callback, 7) := rfl

/-- Typed-key correction can retry, while valid sealed requests keep refusal. -/
example : checkedKeyEdit (.ok "capacity") false false (2 : Nat)
    (fun _ n => n + 1) = .ok 3 := rfl

/-- Bad key admission precedes activity/sealing; their valid-key errors remain exact. -/
example : checkedKeyEdit (.error "symbol-refused") true true (2 : Nat)
    (fun _ n => n + 1) = .error "symbol-refused" := rfl

/-- A genuine identity in a cyclic caller spine is not the saved finite root list. -/
example : matchesNameSpine (fun _ => ⟨"read", .cell 0⟩) (.cell 0) ["read"] = false := rfl

/-- A damaged warm spine goes through admission and cannot deliver its cached result. -/
example : obtainRootProjection (fun _ => ⟨"read", .cell 0⟩) (.cell 0)
    (some (["read"], 9)) (fun _ => .error "list-refused")
    (fun _ => .ok 12) (fun n => .ok n) = .error "list-refused" := rfl

/-- Restored finite roots take the warm path without another cold scan/build. -/
example : obtainRootProjection (fun _ => ⟨"read", .nil⟩) (.cell 0)
    (some (["read"], 9)) (fun _ => .error "cold-scan")
    (fun _ => .error "build") (fun n => .ok n) = .ok 9 := rfl

/-- Finite membership never bypasses the source revision fence, including ABA. -/
example : obtainRootProjection (fun _ => ⟨"read", .nil⟩) (.cell 0)
    (some (["read"], 9)) (fun _ => .ok ["read"])
    (fun _ => .ok 9) (fun (_ : Nat) => .error "stale slot dependency") =
      .error "stale slot dependency" := rfl

/-- Corrected cold requests propagate the actual builder result for fresh issuance. -/
example : obtainRootProjection (fun _ => ⟨"read", .nil⟩) (.cell 0) none
    (fun _ => .ok ["read"]) (fun names => .ok names.length)
    (fun n => .ok n) = .ok 1 := rfl

/-- A later descriptor reaches both cloned catalogs and their shared join. -/
example : Proof.invalidatedNodes
    (registerDeclarations "left" ["capacity", "tariff"]
      (registerDeclarations "right" ["capacity", "tariff"]
        ⟨[⟨"join", [["left", "right"]], false⟩]⟩)) ["tariff"] =
      ["tariff", "left", "right", "join"] := by decide

/-- Cold definition callbacks cannot alter the unconsumed catalog suffix. -/
example : editDeclaredSource
    (registerDeclarations "service" ["first", "later"] ⟨[]⟩) "later"
    (fun name => name == "service") (7 : Nat) (fun _ => 99) =
      .error "object mutation during computation" := by
  apply editDeclaredSource_active "service" "later" ["first", "later"] ⟨[]⟩
  · simp
  · rfl

/-- Repaired construction permits a fresh supported revision without a saved refusal. -/
example : editDeclaredSource
    (registerDeclarations "service" ["first", "later"] ⟨[]⟩) "later"
    (fun _ => false) (7 : Nat) (fun n => n + 1) = .ok 8 := by
  exact editDeclaredSource_retry _ _ _ _

/-- Three preparations of two declared fields retain only the constructor's two binds. -/
example : declarationBindingAttempts 2 3 false = 8 ∧
    declarationBindingAttempts 2 3 true = 2 := ⟨rfl, rfl⟩

/-- Admission keeps descriptor identity and declaration order while capturing types. -/
example : resolveDeclarationTypes [("first", 3), ("later", 7)]
    (fun n => if n = 3 then Except.ok "early-type" else Except.ok "later-type") =
      (Except.ok [("first", (3, "early-type")), ("later", (7, "later-type"))] :
        Except String (List (String × (Nat × String)))) := rfl

/-- A later metadata failure wins before an earlier definition body could refuse. -/
example : defineResolvedDeclarations (.error "type-refused") (0 : Nat)
    (fun _ _ (_ : Nat × String) => .error "definition-refused") = .error "type-refused" := rfl

/-- Successful definitions still observe the preceding private scratch state. -/
example : defineResolvedDeclarations
    (.ok [("first", (3, "integer")), ("later", (7, "integer"))]) []
    (fun prior name (value : Nat × String) =>
      (Except.ok (prior ++ [(name, value.1, prior.length)]) : Except String _)) =
      .ok [("first", 3, 0), ("later", 7, 1)] := rfl

/-- Capturing both branches protects the active leaf before older's hook executes. -/
example : editDeclaredSource
    (registerResolvedTypes "older" [("capacity", (2, "capacity-type"))]
      (registerResolvedTypes "newer" [("tariff", (3, "tariff-type"))]
        ⟨[⟨"receiver", [["newer", "older"]], false⟩]⟩)) "tariff-type"
    (fun name => name == "receiver") (3 : Nat) (fun _ => 99) =
      .error "object mutation during computation" := by
  apply editDeclaredSource_affected _ _ "receiver"
  · decide
  · rfl

/-- Duplicate/shared parent identities survive owned reflection in their original order. -/
example : (exposeParents ["left", "shared", "left"] (9 : Nat)).2 =
    ["left", "shared", "left"] := rfl

/-- Damaged caller data cannot change retained functions, revisions or graph roots. -/
example (callback : Nat → Nat) :
    (Prod.map id (fun _ => ["foreign"])
      (exposeParents ["service"] (callback, 7, ["service"]))).1 =
        (callback, 7, ["service"]) := rfl

/-- Invalid C3 order preserves the supplied whole state, without invoking installation. -/
example : Object.publishEdit (9, 3)
    (checkedParentEdit (.error "cycle") false false (9, 3)
      (fun (_ : List String) _ => (99, 4))) = (9, 3) := rfl

/-- Corrected parent replacement uses the same source installation; sealing still wins. -/
example : checkedParentEdit (.ok ["new"]) false false ((["old"], 3) : List String × Nat)
    (fun parents old => (parents, old.2 + 1)) = .ok (["new"], 4) := rfl

/-- Four internal reconstructions retain their capture cost without four query copies. -/
example : parentSpineCells 3 4 4 = 24 ∧ parentSpineCells 3 0 4 = 12 := ⟨rfl, rfl⟩

/-- Repeated/shared C3 identities and Function-bearing service state require no
new admission on default warm demand; this does not erase public snapshot cost. -/
example : precedenceQuery (some ["join", "billing", "risk", "shared"]) false
    (fun _ => .error "must remain lazy") =
      (0, .ok ["join", "billing", "risk", "shared"]) := rfl

/-- A source revision clears the cache: a false-like refusal cannot resurrect
an older admitted order, and a corrected resolver may retry through the same path. -/
example : precedenceQuery (none : Option (List String)) false (fun _ => .error "refused") =
    (1, .error "refused") ∧
    precedenceQuery (none : Option (List String)) false (fun _ => .ok ["join", "new"]) =
      (1, .ok ["join", "new"]) := ⟨rfl, rfl⟩

/-- Scratch-field construction invalidates a pristine leaf without running a
walker, while a newly registered child still propagates a false refusal. -/
example : Object.invalidationAfterCheck "scratch" (.ok (false, []))
    (fun _ => (Except.error false : Except Bool (List String))) = .ok ["scratch"] ∧
    Object.invalidationAfterCheck "scratch" (.ok (true, ["shared"]))
      (fun _ => (Except.error false : Except Bool (List String))) = .error false := ⟨rfl, rfl⟩

/-- Clearing a cached function advances once and retains its original failure. -/
example (callback : Nat → Nat) :
    (Object.finishInvalidation (⟨7, some callback⟩ : Object.RevisionCache (Nat → Nat))
      (Except.error false : Except Bool Unit)).1.revision = 8 := rfl

/-- Prelinking the unified value-admission root moves its discovery, not its
initializers, out of entry. Physical closure size and mapping cost stay external. -/
example : (addPreparation
    (modulePreparation true ["object", "mop"])
    (modulePreparation true ["object-contract"])).bootstrapInitializers = 3 := by decide

/-- A successful false result is one primary value, visible to either reader. -/
example (view : View Bool) (evaluate : Unit → Except String Bool) :
    primaryRead (commitPrimary (Error := String) view "enabled" (.ok false)).1
      "enabled" evaluate = .ok false := primaryRead_committed _ _ _ _

/-- Failed callback evaluation retains exact state for independent retry. -/
example (view : View (Nat → Nat)) (later : Except Bool (Nat → Nat)) :
    commitPrimary (commitPrimary view "callback" (.error false)).1 "callback" later =
      commitPrimary view "callback" later := commitPrimary_retry _ _ _ _

/-- Clearing cells keeps lazy demand and the original callback refusal. -/
example (site : Site) (view : View Bool) :
    demandRead true site (deferCells view)
      (fun _ => primaryRead (deferCells view) site.name (fun _ => Except.error false)) =
      Except.error false := demandRead_cleared _ _ _ _

/-- A dependency inserted before the target shifts its offset during evaluation. -/
example : finalValueOffset ["target", "fallback"] ["early", "target", "fallback"]
    0 (fun _ => 1) = 1 := by decide

/-- False is present; unrelated uncomputed declarations do not count. -/
example : populatedCells [none, some false, none] = 1 := by decide

/-- Replacing a false payload by another present value does not increase count. -/
example : adjustPopulation 3 (some false) (some true) = 3 := by decide

/-- A failed callback may have inserted a shared dependency before refusing its
own target; its two present cells survive and a later retry adds exactly one. -/
example : populatedCells (commitCountedCell [some false, some true] [] none
    (Except.error "refused" : Except String Bool)) = 2 ∧
    populatedCells (commitCountedCell (Error := String) [some false, some true] [] none (.ok false)) = 3 := by decide

/-- Sparse seeded false and Function-valued cells retain exact observations;
occupancy is generated with the cells rather than a later value scan. -/
example (callback : Nat → Nat) :
    (seedPrimaryCells ["callback", "unused"]
      (fun name => if name = "callback" then some callback else none)).1 = [some callback, none] := by
  simp [seedPrimaryCells_values]

/-- A refused candidate cannot replace a live callback; retry may replace it. -/
example (callback : Nat → Nat) :
    publishSeed (Error := Bool) (publishSeed [some callback] (.error false)) (.ok [none]) = [none] :=
  publishSeed_retry _ _ false

/-- An evicted target is recomputed after an earlier dynamic dependency changes
its offset. Rebinding the final view immediately makes the exact false visible. -/
example :
    let view : View Bool := ⟨4, 7, 9, ["dependency", "target"], fun name =>
      if name = "target" then some false else none⟩
    let site := currentValueSite view "target" 1 (by decide)
    read site view = some false ∧ resolutionWork site view = 0 := by decide

/-- A previously warmed Function site is not replaced by an error credential;
ordinary demand can later retry and publish from its final certified view. -/
example (old : Option Site) (view : View (Nat → Nat))
    (offset : Option { index : Nat // view.names[index]? = some "target" }) :
    finishIndexedDemand old view "target" offset (.error false) = (old, .error false) := rfl

/-- Insertion around an uncomputed cell preserves Function identity and false
occupancy; restoring the old segments recovers exactly the prior sparse store. -/
example (callback : Nat → Nat) :
    growPrimaryCells [some callback, none] [some callback] (some callback) =
      [some callback, none, some callback, some callback] ∧
    populatedCells (growPrimaryCells [some false, none] [some true] (some false)) = 3 := by
  simp [growPrimaryCells, populatedCells]

/-- Eviction does not invalidate a still-current credential. A later source
revision remains a hard refusal, even if its shape and values are restored. -/
example (view : View Bool) (site : Site) (current : valid site view) :
    finishIndexedDemand (Error := String) (some site) view site.name
      (some ⟨site.index, current.2.2.2 ▸ site.indexed⟩) (.ok false) =
      (some site, .ok false) := finishIndexedDemand_keep site view current false

-- A refused middle case retains its state update and cannot erase the last case.
example : observeSuiteCases ([[[1, 2]], [[3]]] : List (List (List Nat)))
    (fun n seen => (if n = 2 then Except.error "refused" else Except.ok n, seen ++ [n]))
    ([] : List Nat) = ([.ok 1, .error "refused", .ok 3], [1, 2, 3]) := rfl

end LeanPoo.Examples.Representation
