import LeanPoo.Functional.TableObservation
import LeanPoo.Functional.TableFocus
import LeanPoo.Functional.TableMapping
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

end LeanPoo.Examples.CollectionStyles
