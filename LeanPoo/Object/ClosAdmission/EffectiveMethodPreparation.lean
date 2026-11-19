-- SPDX-License-Identifier: Apache-2.0 AND LGPL-2.1-or-later
import LeanPoo.Object.ClosAdmission

namespace LeanPoo.Object.ClosAdmission.EffectiveMethodPreparation

open IndexedRank (Attempt scan)

variable {A B Entry Method Qualifier S E O Hook Carrier Payload : Type}

abbrev Action (A S E O : Type) := S → Except E A × S × List O

/-- Effects before a refusal remain visible. A later action sees the state
    left by the earlier read, including changes made by its observer. -/
def thenRead (first : Action A S E O) (next : A → Action B S E O) :
    Action B S E O := fun state =>
  match first state with
  | (.error refusal, after, reads) => (.error refusal, after, reads)
  | (.ok value, after, reads) =>
    let (result, final, later) := next value after
    (result, final, reads ++ later)

def returnValue (value : A) : Action A S E O :=
  fun state => (.ok value, state, [])

/-- The old pass selects private ranked entries, then projects their method
    identities. Method identity is the fixed car of each private rank pair. -/
def filterThenProject (select : Entry → Attempt S E O Entry) (method : Entry → Method)
    (ranked : List Entry) : Action (List Method) S E O := fun state =>
  let (result, after, reads) := scan select ranked state
  (result.map (List.map method), after, reads)

/-- Project the identity when a row is accepted. Qualifier demand,
    normalization, comparison and any refusal still run inside select. -/
def selectMethod (select : Entry → Attempt S E O Entry) (method : Entry → Method)
    (ranked : List Entry) : Action (List Method) S E O :=
  scan (fun row state =>
    let (result, after, reads) := select row state
    (result.map (Option.map method), after, reads)) ranked

theorem project_during_selection (select : Entry → Attempt S E O Entry)
    (method : Entry → Method) (ranked : List Entry) :
    selectMethod select method ranked = filterThenProject select method ranked := by
  funext state
  induction ranked generalizing state with
  | nil => rfl
  | cons row rest ih =>
    cases observed : select row state with
    | mk result tail =>
      rcases tail with ⟨after, reads⟩
      cases result with
      | error refusal => simp [filterThenProject, selectMethod, scan, observed, Except.map]
      | ok accepted =>
        have later := ih after
        simp only [selectMethod, filterThenProject, scan, observed, Except.map] at later ⊢
        rw [later]
        rcases scan select rest after with ⟨result, final, events⟩
        cases result <;> cases accepted <;> rfl

/-- Schedule passes in qualifier order, with ranked method order within
    each pass. This also describes the first refusal in any pass. -/
def passes (read : Qualifier → Action (List Method) S E O) :
    List Qualifier → Action (List (List Method)) S E O
  | [] => returnValue []
  | group :: later => thenRead (read group) fun members =>
      thenRead (passes read later) fun rest => returnValue (members :: rest)

theorem projection_preserves_every_pass
    (select : Qualifier → Entry → Attempt S E O Entry)
    (method : Entry → Method) (ranked : List Entry) (groups : List Qualifier) :
    passes (fun group => selectMethod (select group) method ranked) groups =
      passes (fun group => filterThenProject (select group) method ranked) groups := by
  have same : (fun group => selectMethod (select group) method ranked) =
      fun group => filterThenProject (select group) method ranked := by
    funext group
    exact project_during_selection (select group) method ranked
  rw [same]

inductive StandardGroup where
  | around | before | primary | after
  deriving DecidableEq

def standardGroups : List StandardGroup := [.around, .before, .primary, .after]

/-- A callback during the first read can leave a different live qualifier
    for subsequent reads. One result per method cannot represent both groups. -/
private def changedQualifier (group : StandardGroup) (_ : Unit) :
    Attempt Nat Unit StandardGroup Unit := fun seen =>
  let live := if seen = 0 then StandardGroup.around else StandardGroup.primary
  (.ok (if group = live then some () else none), seen + 1, [group])

example :
    passes (fun group => filterThenProject (changedQualifier group) id [()])
      standardGroups 0 = (.ok [[()], [], [()], []], 4, standardGroups) := rfl

private def refusesBefore (group : StandardGroup) (_ : Unit) :
    Attempt Unit StandardGroup StandardGroup Unit := fun state =>
  (.error group, state, [group])

example :
    passes (fun group => selectMethod
      (if group = .before then refusesBefore group else fun _ state => (.ok none, state, [group]))
      id [()]) standardGroups () = (.error .before, (), [.around, .before]) := rfl

inductive Route (Hook Carrier : Type) where
  | direct (result : Carrier)
  | ordinary
  | hook (callback : Hook)

/-- The staged default closure only retains the payload. Selecting an open
    hook still opens the read region before making the checked default, and
    the hook's returned object still needs the original postcheck. -/
def useStaged (route : Route Hook Carrier) (admit : Unit → Action Carrier S E O)
    (openRegion : Action Unit S E O) (runHook : Hook → Carrier → Action Carrier S E O)
    (checkOrdinary checkHook : Carrier → Action Carrier S E O) : Action Carrier S E O :=
  match route with
  | .direct result => returnValue result
  | .ordinary => thenRead (admit ()) checkOrdinary
  | .hook hook =>
    thenRead openRegion fun _ =>
      thenRead (admit ()) fun default =>
        thenRead (runHook hook default) checkHook

def usePayload (route : Route Hook Carrier) (payload : Payload)
    (materialize : Payload → Action Carrier S E O)
    (openRegion : Action Unit S E O) (runHook : Hook → Carrier → Action Carrier S E O)
    (checkOrdinary checkHook : Carrier → Action Carrier S E O) : Action Carrier S E O :=
  match route with
  | .direct result => returnValue result
  | .ordinary => thenRead (materialize payload) checkOrdinary
  | .hook hook =>
    thenRead openRegion fun _ =>
      thenRead (materialize payload) fun default =>
        thenRead (runHook hook default) checkHook

/-- Eliding the closure does not move preparation across protocol lookup.
    The same captured payload goes to a fresh constructor in the ordinary
    and hook branches. The direct branch need not materialize the default. -/
theorem omit_staging_after_preparation (prepare : Action Payload S E O)
    (route : Action (Route Hook Carrier) S E O)
    (materialize : Payload → Action Carrier S E O)
    (openRegion : Action Unit S E O) (runHook : Hook → Carrier → Action Carrier S E O)
    (checkOrdinary checkHook : Carrier → Action Carrier S E O) :
    (thenRead prepare fun payload =>
      thenRead route fun path =>
        useStaged path (fun () => materialize payload) openRegion runHook checkOrdinary checkHook) =
    (thenRead prepare fun payload =>
      thenRead route fun path =>
        usePayload path payload materialize openRegion runHook checkOrdinary checkHook) := by
  have same (payload : Payload) :
      (fun path =>
        useStaged path (fun () => materialize payload) openRegion runHook checkOrdinary checkHook) =
      (fun path => usePayload path payload materialize openRegion runHook checkOrdinary checkHook) := by
    funext path
    cases path <;> rfl
  apply congrArg (thenRead prepare)
  funext payload
  exact congrArg (thenRead route) (same payload)

end LeanPoo.Object.ClosAdmission.EffectiveMethodPreparation
