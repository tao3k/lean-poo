import LeanPoo.Functional.TableObservation
import LeanPoo.Functional.TableFold
import LeanPoo.Functional.TableIndex
import LeanPoo.Functional.TableFocus
import LeanPoo.Functional.TableMapping
import LeanPoo.Functional.TableProjection
import LeanPoo.Functional.SetAlgebra
import LeanPoo.Functional.TableSelection

/-! Receiver-bound service revisions advance the collection proposal's future
work. Functions are immutable opaque payloads, never compared or rewrapped. -/
namespace LeanPoo.Examples.CollectionStyles
open Functional.OrderedDictionary

/-- One admitted service row contains its budget and an already checked callback. -/
abbrev Ledger := Nat × (Nat → Nat)

/-- A pure revision changes the budget, preserving the exact callback. -/
def revise (budget : Nat) (before : Ledger) : Except String Ledger :=
  if budget ≤ before.1 then .ok (budget, before.2) else .error "budget exceeded"

/-- The shared callback is opaque to the style engine. -/
def callback (value : Nat) : Nat := value + 1

/-- The original posh receiver is a persistent view of a checked service. -/
def before : TableReceiver Ledger := ⟨7, .posh, 10, some (100, callback)⟩

/-- Posh revision leaves its predecessor available with the same Function. -/
example : receiverStep before 11 (revise 80) =
    (before, .ok ⟨7, .posh, 11, some (80, callback)⟩) := by
  exact receiverStep_posh 7 10 11 (100, callback) (80, callback) (revise 80) (by simp [revise])

/-- The same revision in classy keeps the receiver identity and callback. -/
example : receiverStep ⟨7, .classy, 12, some (100, callback)⟩ 99 (revise 80) =
    (⟨7, .classy, 12, some (80, callback)⟩,
     .ok ⟨7, .classy, 12, some (80, callback)⟩) := by
  exact receiverStep_classy 7 12 99 (100, callback) (80, callback) (revise 80) (by simp [revise])

/-- A refused update retains the whole receiver and the original failure cause. -/
example : receiverStep before 11 (revise 120) =
    (before, .error (.callback "budget exceeded")) := by
  apply receiverStep_failure before 11 (100, callback) (revise 120) "budget exceeded" rfl
  simp [revise]

/-- Failed target construction cannot consume a live linear source. -/
example : prepareStyleConvert (.passing .linear) (some (80, callback))
    (fun _ => (Except.error "presentation refused" : Except String Ledger)) =
      (some (80, callback), .error (.callback "presentation refused")) := rfl

/-- Retrying that source with a complete classy result transfers the same Function. -/
example : prepareStyleConvert (E := String) (.passing .linear) (some (80, callback))
    (fun row => .ok (TablePresentation.receiver .classy, row)) =
      (none, .ok (.receiver .classy, (80, callback))) := rfl

/-- Competing installation wins once; a stale receiver cannot overwrite it. -/
example : installStyle (E := String) ReceiverStyle.classy.base
    ⟨3, some (80, callback)⟩ 2 (50, callback) =
      (⟨3, some (80, callback)⟩, .error .stale) :=
  receiver_install_stale .classy _ 2 _ (by decide)

/-- Reverse transfer recovers the exact pure snapshot and retires classy aliases. -/
example : prepareStyleConvert (E := String) (.receiver .classy) (some (80, callback))
    (fun row => .ok (TablePresentation.receiver .posh, row)) =
      (none, .ok (.receiver .posh, (80, callback))) := rfl

/-- The backend snapshot is finite for the worked service collection. -/
def enumerateLedger (row : Ledger) : Except String (List (Nat × Ledger)) :=
  .ok [(1, row)]

/-- Capturing before publication retains the exact checked callback and old budget. -/
example : issueStyleCursor [3, 8] [3, 8] before.value enumerateLedger =
    .ok ⟨[3, 8], [(1, (100, callback))]⟩ := rfl

/-- A fresh observation after classy publication uses the successor budget. -/
example : issueStyleCursor [3, 8] [3, 8]
    (receiverStep ⟨7, .classy, 12, some (100, callback)⟩ 99 (revise 80)).1.value
    enumerateLedger = .ok ⟨[3, 8], [(1, (80, callback))]⟩ := rfl

/-- The already issued iterator remains a snapshot even after retiring its owner. -/
example : pullStyleCursor ⟨[3, 8], [(1, (100, callback))]⟩ [3, 8] =
    (.ok (some (1, (100, callback)), ⟨[3, 8], []⟩), 1) := rfl

/-- Reusing a retired owner to issue a new iterator refuses. -/
example : issueStyleCursor [3, 8] [3, 8] (none : Option Ledger) enumerateLedger =
    .error .consumed := rfl

/-- Metadata changes invalidate the delayed snapshot before advancing its tail. -/
example : pullStyleCursor ⟨[3, 8], [(1, (100, callback))]⟩ [3, 9] =
    (.error (), 0) := by
  apply pullStyleCursor_stale
  decide

/-- EOF must refuse too; exhaustion is not an origin-validation shortcut. -/
example : pullStyleCursor (K := Nat) (V := Ledger) ⟨[3, 8], []⟩ [3, 9] =
    (.error (), 0) := by
  apply pullStyleCursor_stale
  decide

/-- A missing range capability is an explicit refusal, never a made-up order. -/
example : observeStyle (E := String) (R := List Ledger) [3] [3] before.value none =
    .error .unsupported := rfl

/-- Callback failure retains its original cause and prevents an IO result. -/
example : observeStyle [3] [3] before.value
    (some (fun row => revise 120 row)) = .error (.backend "budget exceeded") := rfl

/-- A partial service ledger retains the exact already-admitted callback. -/
def ledgerView (key : Nat) : Option Ledger :=
  if key = 1 then some (100, callback) else if key = 2 then some (200, callback) else none

/-- Reserving capacity refuses missing/insufficient rows before publication. -/
def reserveCapacity (amount : Nat) : Option Ledger → Except String (Option Ledger)
  | none => .error "missing service"
  | some (capacity, run) =>
    if amount ≤ capacity then .ok (some (capacity - amount, run)) else .error "capacity"

/-- A consuming point modification updates capacity and retains callable behavior. -/
example : (focusModify .linear (some ledgerView) 1 (reserveCapacity 30)).2.map
    (fun view => (view 1).map (fun row => (row.1, row.2 4))) = .ok (some (70, 5)) := rfl

/-- A second service remains unchanged, including the opaque Function field. -/
example : replace ledgerView 1 (some (70, callback)) 2 = ledgerView 2 := rfl

/-- Failure keeps the owner live for a fresh, explicit smaller reservation. -/
example : focusModify .linear (some ledgerView) 1 (reserveCapacity 101) =
    (some ledgerView, .error (.callback "capacity")) := rfl

/-- Composed service focus retains its unrelated frame; it is not a second owner. -/
example : (focusServiceModify .mutable (some (ledgerView, 42)) 1 (reserveCapacity 30)).2.map
    (fun service => ((service.1 1).map Prod.fst, service.2)) = .ok (some 70, 42) := rfl

/-- Old prepared work cannot overwrite a reentrant winner. -/
example : (installStyle (E := String) .mutable
    (⟨1, some (replace ledgerView 1 (some (99, callback)))⟩ : TableGeneration (Nat → Option Ledger))
    0 (replace ledgerView 1 (some (70, callback)))).2 = .error .stale := rfl

/-- Required absence is explicit refusal with no fabricated default callback. -/
example : focusModify .pure (some ledgerView) 9
    (requireFocus "missing service" (fun row => .ok (row.1 - 1, row.2))) =
    (some ledgerView, .error (.callback "missing service")) := rfl

/-- Even a get-put no-op observes the linear retirement discipline. -/
example : (focusWrite (E := String) .linear 1 (ledgerView 1) (some ledgerView)).1 = none := rfl

/-- Shared admitted callbacks survive value mapping and deliberate row removal. -/
def serviceRows : List (Nat × Ledger) := [(1, (100, callback)), (2, (10, callback)), (3, (0, callback))]

/-- Retire service three and reserve from every other ORIGINAL row. -/
def reserveServices (amount : Nat) (key : Nat) (row : Ledger) : Except String (Option Ledger) :=
  if key = 3 then .ok none else reserveCapacity amount (some row)

/-- The late insufficient row refuses the whole bulk request without retirement. -/
example : styleMapBindings .linear (some serviceRows) (reserveServices 20) (fun _ => .ok ()) =
    (some serviceRows, .error (.callback "capacity")) := rfl

/-- A fresh smaller request yields one complete result with the same callbacks. -/
example : (styleMapBindings .linear (some serviceRows) (reserveServices 5) (fun _ => .ok ())).2.map
    (fun rows => rows.map (fun entry => (entry.1, entry.2.1, entry.2.2 4))) =
    .ok [(1, 95, 5), (2, 5, 5)] := rfl

/-- Value mapping cannot change a Function leaf when the callback retains it. -/
example : mapBindings (E := String) (fun _ (row : Ledger) => .ok (some row)) serviceRows =
    .ok serviceRows := mapBindings_identity serviceRows

/-- Whole-root refinement can refuse a typed projection before publication. -/
example : styleMapBindings .mutable (some serviceRows)
    (fun key row => .ok (if key = 1 then some row else none))
    (fun rows => if rows.any (fun row => row.1 == 2) then .ok () else .error "primary lost") =
    (some serviceRows, .error (.callback "primary lost")) := rfl

/-- Cost accounting charges only the generic path's changed writes, not Trie nodes. -/
example : mappingWrites [false, true, false, true] = 2 := rfl

/-- A unique index is checked on the final primary, allowing a complete swap. -/
def indexRows : List (Nat × Nat) := [(1, 10), (2, 20)]
/-- Reuse the shared final-root admission stage for the finite uniqueness law. -/
def admitUniqueRows (rows : List (Nat × Nat)) : Except String Unit :=
  if (rows.map Prod.snd).Nodup then .ok () else .error "unique conflict"

example : styleMapBindings .linear (some indexRows)
    (fun key _ => .ok (some (if key = 1 then 20 else 10))) admitUniqueRows =
      (none, .ok [(1, 20), (2, 10)]) := rfl

/-- A genuine collision refuses and keeps the old owner available for retry. -/
example : styleMapBindings .linear (some indexRows)
    (fun _ _ => .ok (some 30)) admitUniqueRows =
      (some indexRows, .error (.callback "unique conflict")) := rfl

/-- A key-negating representation invokes callbacks at the visible coordinates. -/
example : mapBindings (E := String) (fun (key : Int) (value : Nat) =>
    .ok (some (if key = -1 then value + 1 else value + 2))) [(-1, 10), (-2, 20)] =
      .ok [(-1, 11), (-2, 22)] := rfl

/-- Service decomposition keeps opaque callbacks, including at the pivot. -/
def splitServiceRows : List (Nat × Ledger) :=
  [(1, (10, callback)), (2, (20, callback)), (3, (30, callback))]

/-- The explicit numeric comparer is relative to the service being routed. -/
def serviceSign (key : Nat) : Except String Int := .ok ((key : Int) - 2)

/-- The same preparation can serve pure, mutable, linear and receiver views. -/
def splitServices (rows : List (Nat × Ledger)) :=
  prepareOrderedSplit serviceSign (some (20, callback)) (fun _ => .ok ()) rows

/-- Functions retain their identity in both successors and the pivot payload. -/
example : splitServices splitServiceRows =
    .ok ([(1, (10, callback))], some (20, callback), [(3, (30, callback))]) := rfl

/-- Linear routing consumes once, after all results have been prepared. -/
example : styleSplit .linear (some splitServiceRows) splitServices =
    (none, .ok ([(1, (10, callback))], some (20, callback), [(3, (30, callback))])) := rfl

/-- A right-side refinement refusal retains the original owner for a fresh retry. -/
example : styleSplit .linear (some splitServiceRows)
    (prepareOrderedSplit serviceSign (some (20, callback)) (fun rows =>
      if rows.any (fun row => row.1 = 3) then .error "right service unavailable" else .ok ())) =
      (some splitServiceRows, .error (.callback "right service unavailable")) := rfl

/-- Stored false stays present; it is never confused with an absent pivot. -/
example : prepareOrderedSplit (E := String) (fun (k : Nat) => .ok ((k : Int) - 2))
    (some false) (fun _ => .ok ()) [(1, true), (2, false), (3, true)] =
      .ok ([(1, true)], some false, [(3, true)]) := rfl

/-- A transported order can reverse host key order without changing partition laws. -/
example : prepareOrderedSplit (E := String) (fun (k : Int) => .ok (-k - 2))
    (some 20) (fun _ => .ok ()) [(-1, 10), (-2, 20), (-3, 30)] =
      .ok ([(-1, 10)], some 20, [(-3, 30)]) := rfl

/-- The right service snapshot contributes an overlap and a new callback-bearing row. -/
def rightMergeView (key : Nat) : Option Ledger :=
  if key = 2 then some (5, callback) else if key = 3 then some (30, callback) else none

/-- Original-root lookup prepares one resolver opportunity at each union key. -/
def mergeServiceRequests (before : List (Nat × Ledger)) :=
  mergeRequests [1, 2, 3]
    (fun key => (before.find? (fun row => row.1 == key)).map Prod.snd) rightMergeView

/-- Overlaps combine budgets while retaining the exact left Function payload. -/
def mergeServiceChoice (_key : Nat) (left right : Option Ledger) : Except String (Option Ledger) :=
  match left, right with
  | some (budget, fn), some (extra, _) => .ok (some (budget + extra, fn))
  | _, _ => .ok (leftJoinOption left right)

/-- This admission observes only the final total, after all resolver decisions. -/
def admitMergedServices (rows : List (Nat × Ledger)) : Except String Unit :=
  if rows.foldl (fun total row => total + row.2.1) 0 ≤ 60 then .ok ()
  else .error "shared budget exceeded"

/-- Original roots carry checked Functions; merging never rewraps them. -/
def beforeMergeServices : List (Nat × Ledger) := [(1, (10, callback)), (2, (20, callback))]

/-- A full merge adds the right-exclusive service and retains opaque callbacks. -/
example : mergeBindings mergeServiceChoice (mergeServiceRequests beforeMergeServices) =
    .ok [(1, (10, callback)), (2, (25, callback)), (3, (30, callback))] := rfl

/-- Late global refusal preserves the original linear owner for explicit retry. -/
example : styleMergeBindings .linear (some beforeMergeServices) mergeServiceRequests
    mergeServiceChoice admitMergedServices =
      (some beforeMergeServices, .error (.callback "shared budget exceeded")) := rfl

/-- A fresh request drops the optional new service, retaining the right snapshot. -/
example : styleMergeBindings .linear (some beforeMergeServices) mergeServiceRequests
    (fun key a b => if key = 3 then .ok none else mergeServiceChoice key a b)
    admitMergedServices = (none, .ok [(1, (10, callback)), (2, (25, callback))]) := rfl

/-- Two uniqueness-preserving replacements install against their final state. -/
example : prepareBindingMerge (fun (key : Nat) _ _ => .ok (some (if key = 1 then 20 else 10)))
    admitUniqueRows [(1, some 10, none), (2, some 20, none)] = .ok [(1, 20), (2, 10)] := rfl

/-- A genuine final collision exposes no merged root. -/
example : prepareBindingMerge (fun (_key : Nat) _ _ => .ok (some 30))
    admitUniqueRows [(1, some 10, none), (2, some 20, none)] = .error "unique conflict" := rfl

/-- First-source priority distinguishes missing from a stored false. -/
example : mergeBindings (E := String) (fun (_key : Nat) a b => .ok (leftJoinOption a b))
    [(1, some false, some true), (2, none, some false)] = .ok [(1, false), (2, false)] := rfl

/-- One-sided union bypasses an overlap resolver that would refuse invocation. -/
example : unionDecision (fun (_key : Nat) (_a _b : Bool) => .error "overlap refused")
    1 (some false) none = .ok (some false) := rfl

/-- The existing batch fold puts each later source on the left of binary join. -/
example : ([some false, some true] : List (Option Bool)).foldl
    (fun accumulated next => leftJoinOption next accumulated) none = some true := rfl

/-- A later stored false wins by presence; it is not confused with absence. -/
example : ([some true, some false] : List (Option Bool)).foldl
    (fun accumulated next => leftJoinOption next accumulated) none = some false := rfl

/-- Four shared callback-bearing services are routed from one immutable snapshot. -/
def cohortServices : List (Nat × Ledger) :=
  [(1, (10, callback)), (2, (20, callback)), (3, (30, callback)), (4, (40, callback))]

/-- Only complete pairs of services are valid. Odd intermediate states need not
be admitted; the persistent installer recognizes the final branch only. -/
def admitCohort (rows : List (Nat × Ledger)) : Except String (List (Nat × Ledger)) :=
  if rows.length % 2 = 0 then .ok rows else .error "incomplete cohort"

/-- An invalid one/three split retains the predecessor and exposes no partial IO input. -/
example : stylePartition .linear (some cohortServices)
    (prepareSelection admitCohort (fun row => .ok (row.2.1 ≤ 10))) =
      (some cohortServices, .error (.callback "incomplete cohort")) := rfl

/-- Fresh two/two staging succeeds without requiring an admitted empty seed or
admitted one-row intermediate roots. Every original checked callback is retained. -/
example : stylePartition .linear (some cohortServices)
    (prepareSelection admitCohort (fun row => .ok (row.2.1 ≤ 20))) =
      (none, .ok ([(1, (10, callback)), (2, (20, callback))],
        [(3, (30, callback)), (4, (40, callback))])) := rfl

/-- Approval can reject just the second prepared branch after the first succeeds. -/
def admitRouting (rows : List (Nat × Ledger)) : Except String (List (Nat × Ledger)) :=
  if rows.map Prod.fst = [3, 4] then .error "approval unavailable" else .ok rows

/-- Late joint refusal retains the linear predecessor, including opaque Functions. -/
example : stylePartition .linear (some cohortServices)
    (prepareSelection admitRouting (fun row => .ok (row.2.1 ≤ 20))) =
      (some cohortServices, .error (.callback "approval unavailable")) := rfl

/-- A fresh routing request may succeed after the refused request without reviving
an already consumed reference or replaying its old classifier. -/
example : stylePartition .linear (some cohortServices)
    (prepareSelection admitRouting (fun row => .ok (row.1 % 2 = 1))) =
      (none, .ok ([(1, (10, callback)), (3, (30, callback))],
        [(2, (20, callback)), (4, (40, callback))])) := rfl

/-- Selection deletion observations preserve closure identity without needing
DecidableEq on the closure-bearing row type. -/
example : eraseSelection (fun key : Nat => if key = 1 then some (10, callback) else none)
    [2, 4] 1 = some (10, callback) := rfl

/-- Two declared caches deliberately use different payload Types. -/
inductive CohortIndex where
  | badge | team
  deriving DecidableEq, Repr

/-- A service keeps its badge, team and shared opaque checked callback. -/
abbrev CohortRow := Nat × Nat × (Nat → Nat)

/-- Every row carries this same callback; recognition never invokes or compares it. -/
def cohortCallback (n : Nat) : Nat := n + 1

/-- The original two teams contain two services each. -/
def stableCohort : List (Nat × CohortRow) :=
  [(1, (101, 10, cohortCallback)), (2, (102, 10, cohortCallback)),
   (3, (103, 20, cohortCallback)), (4, (104, 20, cohortCallback))]

/-- One moved service leaves both team buckets invalid despite a valid primary. -/
def incompleteCohort : List (Nat × CohortRow) :=
  [(1, (101, 20, cohortCallback)), (2, (102, 10, cohortCallback)),
   (3, (103, 20, cohortCallback)), (4, (104, 20, cohortCallback))]

/-- One atomic badge/team exchange restores complete cohorts without rewrapping. -/
def exchangedCohort : List (Nat × CohortRow) :=
  [(1, (103, 20, cohortCallback)), (2, (102, 10, cohortCallback)),
   (3, (101, 10, cohortCallback)), (4, (104, 20, cohortCallback))]

/-- Unique badge owners and complete grouped primary rows have different Types. -/
def CohortCache : CohortIndex → Type
  | .badge => List (Nat × Nat)
  | .team => List (Nat × List (Nat × CohortRow))

/-- These finite prepared views are supplied by the already correlated installer. -/
def cohortCaches (rows : List (Nat × CohortRow)) : ∀ name, Except String (CohortCache name)
  | .badge => .ok (rows.map (fun row => (row.2.1, row.1)))
  | .team => .ok [(10, rows.filter (fun row => row.2.2.1 == 10)),
                  (20, rows.filter (fun row => row.2.2.1 == 20))]

/-- A grouped cache must recognize each whole source-table bucket, not just the
cache carrier and projected team key. Partial intermediate buckets are private. -/
def admitCohortCache : ∀ name, CohortCache name → Except String Unit
  | .badge, owners => if owners.length % 2 = 0 then .ok () else .error "badge cohort incomplete"
  | .team, groups => if groups.all (fun group => group.2.length % 2 == 0) then .ok ()
      else .error "team cohort incomplete"

/-- The predecessor contains both correlated admitted caches, not an empty
placeholder. Function-bearing grouped payloads remain the exact original rows. -/
def stableCohortCaches : List (Sigma CohortCache) :=
  [⟨.badge, [(101, 1), (102, 2), (103, 3), (104, 4)]⟩,
   ⟨.team, [(10, stableCohort.take 2), (20, stableCohort.drop 2)]⟩]

/-- Establish the predecessor's complete-cache admission before using it in the
failure/retry example. No equality procedure for callbacks is introduced. -/
example : stageIndexCaches (cohortCaches stableCohort) admitCohortCache [.badge, .team] =
    .ok stableCohortCaches := rfl

/-- Late grouped-cache refusal keeps the complete old linear snapshot for retry. -/
example : styleStep .linear (some (stableCohort, stableCohortCaches))
    (fun _ => publishIndexCaches incompleteCohort [.badge, .team]
      (cohortCaches incompleteCohort) admitCohortCache) =
    (some (stableCohort, stableCohortCaches), .error (.callback "team cohort incomplete")) := rfl

/-- Explicit restaging of a complete exchange succeeds with exactly the proposed
primary and callback identities. No equality instance for closures is needed. -/
example : (publishIndexCaches exchangedCohort [.badge, .team]
    (cohortCaches exchangedCohort) admitCohortCache).map Prod.fst = .ok exchangedCohort := rfl

/-- Restoring the original primary passes the same complete cache recognizers. -/
example : (publishIndexCaches stableCohort [.badge, .team]
    (cohortCaches stableCohort) admitCohortCache).map Prod.fst = .ok stableCohort := rfl

/-- A unique-claim failure suppresses its own final admission and later recipes. -/
example : stageIndexCaches (fun name => match name with
    | .badge => .error "unique claim conflict" | .team => .error "later recipe")
    admitCohortCache [.badge, .team] = .error "unique claim conflict" := rfl

/-- External keys reverse sign, while the exact checked service/callback survives. -/
def translateCohortEntry (entry : Nat × CohortRow) : Except String (Int × CohortRow) :=
  translateCursorEntry (fun key => .ok (-(Int.ofNat key))) (fun value => .ok value) entry

/-- Conversion is demanded only at the first pull, before any IO consumer. -/
example : (mappedTablePull translateCohortEntry [2, 5] [2, 5] stableCohort).1.2 =
    .ok (some (-1, (101, 10, cohortCallback))) := rfl

/-- A new owner publication changes its head, not an issued cursor's old snapshot. -/
example :
    let next := receiverStep (E := String) ⟨7, .classy, 1, some stableCohort⟩ 2
      (fun _ => .ok exchangedCohort)
    (next.1.value, (mappedTablePull translateCohortEntry [2, 5] [2, 5] stableCohort).1.2) =
      (some exchangedCohort, .ok (some (-1, (101, 10, cohortCallback)))) := rfl

/-- Metadata refusal preserves the complete unread stream and invokes no mapping. -/
example : mappedTablePull translateCohortEntry [2, 5] [2, 6] stableCohort =
    ((stableCohort, .error .stale), (0, 0)) := rfl

/-- A transient failure at the second service occurs after that source row is pulled. -/
def translateAvailableCohort (entry : Nat × CohortRow) : Except String (Int × CohortRow) :=
  if entry.1 = 2 then .error "conversion unavailable" else translateCohortEntry entry

/-- The failed row is not automatically replayed by the same mutable Iterator. -/
example : mappedTablePull translateAvailableCohort [2, 5] [2, 5] (stableCohort.drop 1) =
    ((stableCohort.drop 2, .error (.backend "conversion unavailable")), (1, 1)) := rfl

/-- A fresh request restarts at the original snapshot after conversion is repaired. -/
example : (mappedTablePull translateCohortEntry [2, 5] [2, 5] stableCohort).1.1 =
    stableCohort.drop 1 := rfl

/-- Even an exhausted cursor must refuse newly invalidated metadata. -/
example : mappedTablePull translateCohortEntry [2, 5] [2, 6] [] =
    (([], .error .stale), (0, 0)) := rfl

/-- A present false result is not confused with the EOF sentinel. -/
example : mappedTablePull (fun (_row : Nat × Bool) => (Except.ok false : Except String Bool))
    [0] [0] [(1, false)] = (([], .ok (some false)), (1, 1)) := rfl


/-- Finite admitted callback identities are decidable; arbitrary function equality
is not. Scheme tests separately retain the actual checked procedure object. -/
inductive FoldCallback where
  | increment | addTwo
  deriving DecidableEq

/-- Interpretation is supplied by the admitted callback directory. -/
def FoldCallback.run (identity : FoldCallback) (argument : Nat) : Nat :=
  match identity with | .increment => callback argument | .addTwo => argument + 2

/-- The finite table model keeps callback identity rather than comparing closures. -/
abbrev FoldLedgerRow := Nat × FoldCallback

/-- The original finite ledger shares the same admitted callback identity. -/
def foldLedgerBefore (key : Nat) : Option FoldLedgerRow :=
  if key = 0 then some (10, FoldCallback.increment) else if key = 1 then some (20, FoldCallback.increment) else none

/-- The explicit finite inventory supplies a decidable whole-table refinement. -/
def admitEvenLedger (root : Nat → Option FoldLedgerRow) : Except String Unit :=
  if ([0, 1, 2].filter fun key => (root key).isSome).length % 2 = 0
    then .ok () else .error "even ledger required"

/-- Contribution reads the budget and never executes or normalizes the Function. -/
def foldLedgerScore (_key : Nat) (row : FoldLedgerRow) : Int := Int.ofNat row.1

/-- Removal followed by insertion is one final-state publication, not two admissions. -/
def foldLedgerEdits (budget : Nat) : List (Change Nat FoldLedgerRow) :=
  [⟨0, some (10, FoldCallback.increment), none⟩, ⟨2, none, some (budget, FoldCallback.increment)⟩]

/-- A compatible unrefined request cannot admit an odd refined source successor. -/
example : checkedFold foldLedgerScore admitEvenLedger
    [⟨0, some (10, FoldCallback.increment), none⟩] foldLedgerBefore 30 =
    .error (.inr "even ledger required") := rfl

/-- The intermediate odd root is private; only the accepted final root reaches the aggregate. -/
example : (checkedFold foldLedgerScore admitEvenLedger (foldLedgerEdits 40)
    foldLedgerBefore 30).map (fun result => (result.1 0, result.1 1, result.1 2, result.2)) =
    .ok (none, some (20, FoldCallback.increment), some (40, FoldCallback.increment), 60) := rfl

/-- The independent target refinement sums the same finite service inventory. -/
def admitLedgerBudget (root : Nat → Option FoldLedgerRow) : Except String Unit :=
  if foldView [0, 1, 2] foldLedgerScore root ≤ 50 then .ok () else .error "target budget exceeded"

/-- Lawful identity representation still cannot bypass a target-only root constraint. -/
example : admitFoldTransfer
    (checkedFold foldLedgerScore admitEvenLedger (foldLedgerEdits 40) foldLedgerBefore 30)
    (fun root => .ok root)
    (fun root => (admitLedgerBudget root).mapError Sum.inr) =
    .error (.inr "target budget exceeded") := rfl

/-- A fresh repaired request reuses the source aggregate and the exact Function leaf. -/
example : (admitFoldTransfer
    (checkedFold foldLedgerScore admitEvenLedger (foldLedgerEdits 25) foldLedgerBefore 30)
    (fun root => .ok root)
    (fun root => (admitLedgerBudget root).mapError Sum.inr)).map
    (fun result => (result.2, (result.1 2).map (fun row => row.2.run 7))) = .ok (45, some 8) := rfl

/-- Checked inverse recovery separately admits the recovered source and restores its sum. -/
example : checkedFold foldLedgerScore admitEvenLedger (inverseChanges (foldLedgerEdits 25))
    (writeChanges (foldLedgerEdits 25) foldLedgerBefore)
    (foldChanges foldLedgerScore (foldLedgerEdits 25) 30) = .ok (foldLedgerBefore, 30) := by
  apply checkedFold_inverse foldLedgerScore admitEvenLedger (foldLedgerEdits 25)
    foldLedgerBefore _ 30
  · rfl
  · rfl


/-- A finite service directory models two distinct admitted callbacks without
assuming decidable equality of arbitrary functions. -/
structure ServiceLedgerRow where
  badge : Nat
  endpoint : Nat
  team : Nat
  callback : FoldCallback
  deriving DecidableEq

/-- The same explicit sign representation as the Scheme boxed ordered view. -/
def serviceLedgerKeys : Prototype.DictionaryBridge Int Int :=
  ⟨Neg.neg, Neg.neg, fun key => Int.neg_neg key, fun key => Int.neg_neg key⟩

/-- Three admitted services share one team while the last remains untouched. -/
def serviceLedgerBefore (key : Int) : Option ServiceLedgerRow :=
  if key = 1 then some ⟨101, 1001, 10, .increment⟩
  else if key = 2 then some ⟨102, 1002, 10, .addTwo⟩
  else if key = 9 then some ⟨109, 1009, 90, .increment⟩ else none

/-- Both unique identifiers swap, both services move teams, and callbacks persist. -/
def serviceLedgerEdits : List (Change Int ServiceLedgerRow) :=
  [⟨1, serviceLedgerBefore 1, some ⟨102, 1002, 20, .increment⟩⟩,
   ⟨2, serviceLedgerBefore 2, some ⟨101, 1001, 20, .addTwo⟩⟩]

/-- Mapping produces only key/replacement requests; the overlay supplies expectations. -/
def serviceLedgerWrites : List (Int × Option ServiceLedgerRow) :=
  (transportChanges serviceLedgerKeys (Prototype.DictionaryBridge.identity ServiceLedgerRow)
    serviceLedgerEdits).map (fun edit => (edit.key, edit.after))

/-- The issued paired snapshot is independent of a later owner's head. -/
def serviceLedgerTarget : Int → Option ServiceLedgerRow :=
  transportView serviceLedgerKeys (Prototype.DictionaryBridge.identity ServiceLedgerRow) serviceLedgerBefore

/-- One atomic traced install agrees with the transported source, not a sequence
of separately approved identifier/index snapshots. -/
example : applyChanges (traceBindings serviceLedgerWrites serviceLedgerTarget (fun _ => none))
    serviceLedgerTarget = .ok (transportView serviceLedgerKeys
      (Prototype.DictionaryBridge.identity ServiceLedgerRow) (writeChanges serviceLedgerEdits serviceLedgerBefore)) := by
  apply traceBindings_transport serviceLedgerKeys (Prototype.DictionaryBridge.identity ServiceLedgerRow)
    serviceLedgerEdits serviceLedgerBefore _ serviceLedgerTarget rfl
  rfl

/-- A single intermediate identifier update would fail uniqueness. -/
example : uniqueIndexRows (fun (_key : Int) (row : ServiceLedgerRow) => row.badge)
    [(-1, ⟨102, 1002, 20, .increment⟩), (-2, ⟨102, 1002, 10, .addTwo⟩)] = false := rfl

/-- The complete exchanged identifiers are independently accepted by both indexes. -/
example :
    let rows : List (Int × ServiceLedgerRow) :=
      [(-1, ⟨102, 1002, 20, .increment⟩), (-2, ⟨101, 1001, 20, .addTwo⟩)]
    (uniqueIndexRows (fun _ row => row.badge) rows,
     uniqueIndexRows (fun _ row => row.endpoint) rows) = (true, true) := rfl

/-- The target delta preserves the distinct admitted callback through team migration. -/
example : (applyChanges (traceBindings serviceLedgerWrites serviceLedgerTarget (fun _ => none))
    serviceLedgerTarget).map (fun root => (root (-2)).map (fun row => row.callback.run 7)) =
      .ok (some 9) := rfl

/-- The existing two-phase grouped index now observes the complete final team. -/
example : (reviseIndex (serviceLedgerWrites.map Prod.fst)
    (fun (_key : Int) (row : ServiceLedgerRow) => row.team)
    (writeBindings serviceLedgerWrites serviceLedgerTarget)
    (indexView (fun (_key : Int) (row : ServiceLedgerRow) => row.team) serviceLedgerTarget) 20 (-2)).map
      ServiceLedgerRow.badge = some 101 := rfl

/-- Key-space registry payloads need not have the business row's layout or Type. -/
example : keySpaceView serviceLedgerKeys (fun (key : Int) => if key = 2 then some (99 : Nat) else none)
    (-2) = some 99 := rfl

/-- A known removal supplies none as the next expected value, unlike untouched state. -/
example : (traceBindings [(0, none), (0, some false)]
    (fun (key : Nat) => if key = 0 then some false else none) (fun _ => none)).map Change.before =
    [some false, none] := rfl

/-- Two writes emit two overlay entries and convert only the two present replacements. -/
example : traceBindingsWork serviceLedgerWrites = (2, 2) := rfl

/-- Four approval principals give a decidable cohort universe for the example. -/
def cohortMembers (view : Membership Nat) : List Nat := [1, 2, 3, 4].filter view

/-- Approval publication requires whole pairs; no closure of this predicate under
arbitrary union/intersection/membership updates is assumed. -/
def admitAccessCohort (view : Membership Nat) : Except String Unit :=
  if (cohortMembers view).length % 2 = 0 then .ok () else .error "incomplete cohort"

/-- An explicit finite membership view uses the same equality as the list oracle. -/
def cohortView (members : List Nat) : Membership Nat := fun key => members.contains key

/-- Both operands are valid, but their union has three principals and must refuse. -/
example :
    (admitSetOperation [cohortView [1, 2], cohortView [2, 3]] admitAccessCohort
      (fun _ => .ok (combineSet .union (cohortView [1, 2]) (cohortView [2, 3])))).map
      cohortMembers = .error "incomplete cohort" := by rfl

/-- Repair publishes all four principals after complete admission. -/
example :
    (admitSetOperation [cohortView [1, 2], cohortView [3, 4]] admitAccessCohort
      (fun _ => .ok (combineSet .union (cohortView [1, 2]) (cohortView [3, 4])))).map
      cohortMembers = .ok [1, 2, 3, 4] := by rfl

/-- A one-member update is outside this refinement's lawful lens domain. -/
example :
    (admitSetOperation [cohortView [1, 2]] admitAccessCohort
      (fun _ => .ok (setMembership (cohortView [1, 2]) 3 true))).map cohortMembers =
      .error "incomplete cohort" := by rfl

/-- Cold construction admits the complete pair without requiring a singleton
intermediate. Backend atomic construction remains an explicit implementation law. -/
example : (admitSetOperation [] admitAccessCohort (fun _ => .ok (cohortView [3, 4]))).map
    cohortMembers = .ok [3, 4] := by rfl

/-- Refusal preserves an owner in each style; the existing style failure law also
covers posh/classy after receiver erasure. No callback effects are rolled back. -/
example (style : TableStyle) :
    styleStep style (some (cohortView [1, 2])) (fun before =>
      admitSetOperation [before, cohortView [2, 3]] admitAccessCohort
        (fun _ => .ok (combineSet .union before (cohortView [2, 3])))) =
      (some (cohortView [1, 2]), .error (.callback "incomplete cohort")) := by
  apply styleStep_failure
  rfl

/-- Captured Set/Table/dependency revisions refuse an expired focus before running
a new recognizer or membership operation, using the existing observation guard. -/
example : observeStyle [0, 0, 0] [1, 0, 0] (some (cohortView [1, 2]))
    (some (fun before => admitSetOperation [before] admitAccessCohort
      (fun _ => .ok (setMembership before 3 true)))) = .error .stale := by
  apply observeStyle_stale
  decide

/-- A refused original cohort wins over a simultaneous bad argument and lookup.
The same boundary handles insertion, removal and a seedless complete constructor. -/
example : admitSetMethod [cohortView [1]] admitAccessCohort (3 : Nat)
    (fun _ => .error "bad principal") (fun _ => .error "bad delegate") =
      .error "incomplete cohort" := by rfl

/-- Recognizing a Function-valued argument can preserve its exact identity;
no equality or normalization of the closure is needed for delegation. -/
example (f : Nat → Nat) (method : (Nat → Nat) → Except String (Membership Nat)) :
    admitSetMethod [] admitAccessCohort f Except.ok (fun _ => .ok method) =
      admitSetOperation [] admitAccessCohort (fun _ => method f) := by
  apply admitSetMethod_delegation <;> rfl

/-- Explicit entry projection changes keys and keeps opaque checked callbacks;
it does not need a source/target isomorphism or equality on Functions. -/
example (f g : Nat → Nat) :
    mapEntries (E := String) (fun key callback => .ok (some (key + 10, callback)))
      [(1, f), (2, g)] [] = .ok [(11, f), (12, g)] := by rfl

/-- The first primary collision precedes a later callback failure. -/
example : mapEntries (fun (key : Nat) (value : Nat) =>
    if key = 3 then .error "late callback" else .ok (some (10, value)))
      [(1, 100), (2, 200), (3, 300)] [] = .error (.inr 10) := by rfl

/-- Optional projection retains a false payload, rather than confusing it with
an absent Option or silently changing the target key. -/
example : mapEntries (E := String) (fun (key : Nat) (_ : Nat) =>
    .ok (if key = 2 then some (key + 10, false) else none))
      [(1, 100), (2, 200)] [] = .ok [(12, false)] := by rfl

/-- Whole-target constraints admit the complete cohort, not singleton prefixes. -/
example : prepareEntryMap (fun (key : Nat) (value : Nat) => .ok (some (key + 10, value)))
    (fun _ => .ok ()) (Except.ok : List (Nat × Nat) → Except String (List (Nat × Nat)))
    (fun rows => if rows.length = 2 then .ok () else .error "incomplete cohort")
    [(1, 100), (2, 200)] = .ok [(11, 100), (12, 200)] := by rfl

/-- A source observation can return a different target type without consuming or
rewriting the source reference. Existing stale/consumed laws remain applicable. -/
example : observeStyle [0] [0] (some [(1, 100), (2, 200)])
    (some (fun rows => mapEntries (E := String)
      (fun (key : Nat) (value : Nat) => .ok (some (key + 10, decide (value > 100)))) rows [])) =
      .ok [(11, false), (12, true)] := by rfl

/-- Cached service callbacks remain opaque; only their logical output keys move. -/
def serviceProjection (_key : Nat) (row : Nat × (Nat → Nat)) :
    Except String (Option (Nat × (Nat → Nat))) := .ok (some (row.1, row.2))

/-- A batched final-state swap refreshes two services while the shared third
callback remains the exact predecessor value, independent of function equality. -/
example (f g h : Nat → Nat) :
    (refreshEntryCache serviceProjection
      (fun key => if key = 1 then some (20, f) else if key = 2 then some (10, g) else none)
      [1, 2] (fun key => if key = 3 then some (30, h) else none)).map
      (fun cache => cache 3) = .ok (some (30, h)) := by
  simp [refreshEntryCache, projectedEntry, serviceProjection, replace, Except.bind, Except.map]

/-- Releasing both old owners permits a final swap; retained key 30 still blocks
collisions. Payloads are Functions, so these checks cannot use payload equality. -/
example (f g h : Nat → Nat) :
    reserveProjection serviceProjection [(30, h)] [(1, (20, f)), (2, (10, g))] =
      .ok [(30, h), (20, f), (10, g)] := by
  simp [reserveProjection, mapEntries, serviceProjection, Except.map]

/-- A new service cannot overwrite an untouched shared output, even with the
same Function. Failure contains no target or cached successor. -/
example (f : Nat → Nat) :
    reserveProjection serviceProjection [(30, f)] [(1, (30, f))] = .error (.inr 30) := by
  simp [reserveProjection, mapEntries, serviceProjection, Except.map]

/-- Deletion closes without demanding a callback that would otherwise refuse. -/
example : (refreshEntryCache (fun (_ : Nat) (_ : Nat) =>
      (.error "must not run" : Except String (Option (Nat × Nat))))
      (fun _ => none) [1] (fun _ => some (10, 100))).map (fun cache => cache 1) = .ok none := by
  simp [refreshEntryCache, projectedEntry, replace, Except.bind, Except.map]

/-- Direct delivery carries an opaque cache and the original finite edit list;
no equality on the Function state or inventory for diff discovery is required. -/
example (cache : Nat → Nat) (edits : List (Change Nat Bool)) :
    deliverProjection (.ok (cache, edits))
      (fun next delta => .ok (next, delta) :
        (Nat → Nat) → List (Change Nat Bool) → Except String ((Nat → Nat) × List (Change Nat Bool))) =
      .ok (cache, edits) := rfl

/-- A changed public target refuses the delivered old expectation before returning
any new source/cache state, even though private projection preparation succeeded. -/
example (cache : Nat → Nat) :
    publishProjectionDelivery (.ok (cache, [⟨1, some 10, some 30⟩]) :
      Except Nat ((Nat → Nat) × List (Change Nat Nat))) .linear
      (some (fun _ => some 99)) (fun root delta => applyChanges delta root) =
        (some (fun _ => some 99), .error (.callback 1)) := by
  simp [publishProjectionDelivery, styleStep, applyChanges, Except.map]

/-- Explicit target inversion recovers the actual published base, including any
unrelated rows retained by changed-key rebasing, using an opaque prepared cache. -/
example (cache : Nat → Nat) (edits : List (Change Nat Bool))
    (before after : Nat → Option Bool) (ready : applyChanges edits before = .ok after) :
    publishProjectionDelivery (.ok (cache, inverseChanges edits) :
      Except Nat ((Nat → Nat) × List (Change Nat Bool))) .linear
      (some after) (fun root delta => applyChanges delta root) =
        (none, .ok (cache, inverseChanges edits, before)) :=
  publishProjectionDelivery_inverse cache .linear edits before after ready

/-- Owners 1 and 4 share a region; owner 2 belongs to another region. -/
def regionalGrants : Nat → Option Unit := fun key =>
  if key = 1 ∨ key = 4 ∨ key = 2 then some () else none

/-- The stable region map is independent of the stored Unit payload. -/
def grantRegion (key : Nat) (_row : Unit) : Nat := key % 3

/-- Losing owner 1 retains region 1 because owner 4 survives. -/
example : setImage [1, 2, 4] (indexView grantRegion
    (fun key => if key = 1 then none else regionalGrants key)) 1 = true := by decide

/-- Losing every owner of region 1 removes it without affecting region 2. -/
example : setImage [1, 2, 4] (indexView grantRegion
    (fun key => if key = 1 ∨ key = 4 then none else regionalGrants key)) 1 = false := by decide

/-- Coalesced grouped repair and complete rebuilding give the same new image. -/
example : setImage [1, 2, 4, 6] (reviseIndex [1, 2, 6] grantRegion
    (fun key => if key = 4 ∨ key = 6 then some () else none)
    (indexView grantRegion regionalGrants)) 0 = true := by decide

/-- The inverse source delta restores all owners and their deduplicated regions. -/
example : (applyChanges (inverseChanges
    [{key := 1, before := some (), after := none},
     {key := 4, before := some (), after := none}])
    (fun key => if key = 2 then some () else none)).map
    (fun restored => setImage [1, 2, 4] (indexView grantRegion restored) 1) = .ok true := by
  simp [inverseChanges, applyChanges, replace, Except.map, setImage, indexView, grantRegion]

/-- Two services supply granted and revoked identities independently. -/
def grantedBefore (key : Nat) : Bool := decide (key = 1 ∨ key = 2)

/-- The first round denies identity 2. -/
def revokedBefore (key : Nat) : Bool := decide (key = 2)

/-- The next grant revision replaces identity 1 with identity 3. -/
def grantedAfter (key : Nat) : Bool := decide (key = 2 ∨ key = 3)

/-- A simultaneous revocation revision denies identity 3 instead. -/
def revokedAfter (key : Nat) : Bool := decide (key = 3)

/-- Effective access moves from identity 1 to identity 2 under both revisions. -/
example : (combineSet .diff grantedBefore revokedBefore 1,
    combineSet .diff grantedAfter revokedAfter 2,
    combineSet .diff grantedAfter revokedAfter 3) = (true, true, false) := by decide

/-- Only edited keys are required to install the entire effective access view. -/
example : applyChanges (diffChanges [1, 2, 3]
    (membershipTable (combineSet .diff grantedBefore revokedBefore))
    (membershipTable (combineSet .diff grantedAfter revokedAfter)))
    (membershipTable (combineSet .diff grantedBefore revokedBefore)) =
    .ok (membershipTable (combineSet .diff grantedAfter revokedAfter)) := by
  apply setCombination_delta .diff _ _ _ _ [1, 2, 3] (by decide)
  · intro key outside
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
    simp [grantedBefore, grantedAfter, outside.1, outside.2.1, outside.2.2]
  · intro key outside
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
    simp [revokedBefore, revokedAfter, outside.2.1, outside.2.2]

/-- Moving one union owner between services requires no target replacement. -/
example : reviseSetCombination [1] .union
    (fun _ : Nat => false) (fun key => key == 1)
    (combineSet .union (fun key => key == 1) (fun _ => false)) 1 = true := by decide

/-- An immutable catalog grants multiple permissions per service; repeated
permission 20 is one membership, and service 4 deliberately grants nothing. -/
def servicePermissions (service : Nat) (_ : Unit) : List Nat :=
  match service with
  | 1 => [10, 20, 20]
  | 2 => [20, 30]
  | 3 => [30, 40]
  | _ => []

/-- The inventory covers all owners in both revisions, including the empty grant. -/
def permissionOwners : List Nat := [1, 2, 3, 4]

/-- Services 1 and 2 independently own permission 20 in the initial snapshot. -/
def permissionServicesBefore (key : Nat) : Option Unit :=
  if key = 1 ∨ key = 2 then some () else none

/-- A complete service migration retains audit 30 and newly grants permission 40. -/
def permissionServicesAfter (key : Nat) : Option Unit :=
  if key = 3 ∨ key = 4 then some () else none

/-- The mathematical flattened image matches the catalog, with duplicates erased. -/
example : [10, 20, 30, 40].map
    (setImage permissionOwners (indexKeysView servicePermissions permissionServicesBefore)) =
      [true, true, true, false] := rfl

/-- Removing only the first service retains the second owner's shared permission. -/
example : setImage permissionOwners (indexKeysView servicePermissions
    (replace permissionServicesBefore 1 none)) 20 = true := rfl

/-- Complete index repair preserves the shared audit grant while removing the
last owners of 10/20 and inserting 40; no partial public result is observed. -/
example : [10, 20, 30, 40].map
    (setImage permissionOwners (reviseIndexKeys [1, 2, 3, 4] servicePermissions
      permissionServicesAfter (indexKeysView servicePermissions permissionServicesBefore))) =
      [false, false, true, true] := rfl

/-- The retained audit membership emits no target edit despite owner migration. -/
example : setImageEdit 30
    (setImage permissionOwners (indexKeysView servicePermissions permissionServicesBefore) 30)
    (setImage permissionOwners (indexKeysView servicePermissions permissionServicesAfter) 30) = [] := rfl

/-- An explicit source inverse restores every image bucket, including empty and
duplicate grant rows. This is relation recovery rather than inferred inversion. -/
example (edits : List (Change Nat Unit))
    (ready : applyChanges edits permissionServicesBefore = .ok permissionServicesAfter) :
    (applyChanges (inverseChanges edits) permissionServicesAfter).map
      (fun restored => setImage permissionOwners (indexKeysView servicePermissions restored)) =
      .ok (setImage permissionOwners (indexKeysView servicePermissions permissionServicesBefore)) :=
  setImage_keys_inverse permissionOwners servicePermissions edits _ _ ready

/-- Nonempty finite cohort construction accepts only the complete even group. -/
def buildCohort (rows : List Nat) : Except String (List Nat) :=
  if rows.isEmpty || rows.length % 2 != 0 then .error "invalid-cohort" else .ok rows

/-- Cold construction needs no business empty or singleton intermediate. -/
example : materializeIndexBucket buildCohort none (some [1, 2]) = .ok (some [1, 2]) := rfl

/-- Removing a complete group does not ask the nonempty builder for an empty value. -/
example : materializeIndexBucket buildCohort (some [1, 2]) (some []) = .ok none := rfl

/-- Simultaneous migration joins the final cohort instead of admitting odd stages. -/
example : materializeIndexBucket buildCohort (some [3, 4]) (some [1, 2, 3, 4]) =
    .ok (some [1, 2, 3, 4]) := rfl

/-- A failed one-row migration refuses; an explicit complete retry succeeds. -/
example : materializeIndexBucket buildCohort none (some [1]) = .error "invalid-cohort" ∧
    materializeIndexBucket buildCohort none (some [1, 2]) = .ok (some [1, 2]) := ⟨rfl, rfl⟩

/-- The existing ordered family staging exposes no partial bucket after refusal. -/
example : stageIndexCaches
    (Cache := fun _ : Bool => Option (List Nat))
    (fun name => materializeIndexBucket buildCohort none
      (some (if name then [3] else [1, 2])))
    (fun _ _ => (Except.ok () : Except String Unit)) [false, true] =
      .error "invalid-cohort" := rfl

/-- Unaffected Function payloads retain the exact original bucket handle. -/
example (functions : List (Nat → Nat)) :
    materializeIndexBucket (fun _ : List Nat => (Except.error "unused" : Except String (List (Nat → Nat))))
      (some functions) none = .ok (some functions) := rfl

end LeanPoo.Examples.CollectionStyles
