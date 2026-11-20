-- SPDX-License-Identifier: Apache-2.0 AND LGPL-2.1-or-later
import LeanPoo.Object.PublishedReadPreorder

namespace LeanPoo.Object.PackedReadRoutes

abbrev Lookup := Nat → Option Nat

structure Route where
  reads : Lookup
  indices : Lookup
  cells : Nat → Nat
  missing : Nat
  instanceId : Nat
  revision : Nat

inductive Field where
  | unopened | fallback | lookup (f : Lookup) | cellVector (f : Nat → Nat) | token (value : Nat)

abbrev Bank := Nat → Field

def address (receiver lane : Nat) : Nat := 6 * receiver + lane

theorem address_bound (receivers receiver lane : Nat)
    (index : receiver < receivers) (width : lane < 6) :
    address receiver lane < 6 * receivers := by
  unfold address
  omega

theorem disjoint (a b i j : Nat) (hi : i < 6) (hj : j < 6)
    (different : a ≠ b) : address a i ≠ address b j := by
  unfold address
  omega

def routeField (route : Route) : Nat → Field
  | 0 => .lookup route.reads
  | 1 => .lookup route.indices
  | 2 => .cellVector route.cells
  | 3 => .token route.missing
  | 4 => .token route.instanceId
  | 5 => .token route.revision
  | _ => .unopened

def putRoute (bank : Bank) (i : Nat) (route : Route) : Bank :=
  fun j => if 6 * i ≤ j ∧ j < 6 * i + 6 then routeField route (j - 6 * i) else bank j

def putFallback (bank : Bank) (i : Nat) : Bank :=
  fun j => if j = address i 0 then .fallback else bank j

def getRoute (bank : Bank) (i : Nat) : Option Route :=
  match bank (address i 0), bank (address i 1), bank (address i 2),
        bank (address i 3), bank (address i 4), bank (address i 5) with
  | .lookup r, .lookup ix, .cellVector c, .token m, .token s, .token v =>
    some ⟨r, ix, c, m, s, v⟩
  | _, _, _, _, _, _ => none

theorem get_put_same (bank : Bank) (i : Nat) (route : Route) :
    getRoute (putRoute bank i route) i = some route := by
  have within (k : Nat) (hk : k < 6) : putRoute bank i route (address i k) = routeField route k := by
    unfold putRoute address
    have low : 6 * i ≤ 6 * i + k := by omega
    have high : 6 * i + k < 6 * i + 6 := by omega
    have offset : 6 * i + k - 6 * i = k := by omega
    simp [low, high, offset]
  simp [getRoute, within, routeField]

theorem get_put_other (bank : Bank) (a b : Nat) (route : Route) (different : a ≠ b) :
    getRoute (putRoute bank a route) b = getRoute bank b := by
  have outside (k : Nat) (hk : k < 6) : putRoute bank a route (address b k) = bank (address b k) := by
    unfold putRoute address
    have no : ¬(6 * a ≤ 6 * b + k ∧ 6 * b + k < 6 * a + 6) := by omega
    simp [no]
  simp [getRoute, outside]

theorem get_fallback (bank : Bank) (i : Nat) : getRoute (putFallback bank i) i = none := by
  simp [getRoute, putFallback]

inductive Key where
  | bootstrap | miss (slot : Nat) | structural (query : Nat) | ordinary (slot : Nat)

structure Claim where
  identity : Nat
  key : Key
  value : Option Nat
  instanceId : Nat
  revision : Nat

def readValue (route : Route) (name : Nat) : Nat :=
  ((route.indices name).map route.cells).getD route.missing

def vectorCurrent (route : Route) (claim : Claim) : Bool :=
  route.revision == claim.revision && route.instanceId == claim.instanceId &&
    match claim.key with
    | .bootstrap => false
    | .miss slot => readValue route slot == route.missing
    | .structural query => route.reads query == some claim.identity
    | .ordinary slot =>
      let value := readValue route slot
      route.reads slot == some claim.identity &&
        (if value == route.missing then none else some value) == claim.value

/-- Bootstrap and non-vector stores use the ordinary currentness procedure. -/
def current (route : Option Route) (claim : Claim) (ordinary : Bool) : Bool :=
  match claim.key, route with
  | .bootstrap, _ | _, none => ordinary
  | _, some fields => vectorCurrent fields claim

theorem packed_live (bank : Bank) (i : Nat) (route : Route) (claim : Claim) (ordinary : Bool) :
    current (getRoute (putRoute bank i route) i) claim ordinary =
      current (some route) claim ordinary := by rw [get_put_same]

theorem packed_fallback (bank : Bank) (i : Nat) (claim : Claim) (ordinary : Bool) :
    current (getRoute (putFallback bank i) i) claim ordinary = ordinary := by
  rw [get_fallback]
  cases claim with
  | mk identity key value instanceId revision => cases key <;> rfl

open ReadRouteRuns PublishedReadPreorder

/-- Issuer, key and live route guards come from the current replay window.
Fresh banks may borrow different values on either side of an effect. -/
theorem window_preserves_refusal (route guard : Nat → Except Refusal Unit)
    (i : Nat → Nat) (claims : Nat → Claim) (ordinary : Nat → Bool) (native : Nat → Route)
    (rows : List Nat) :
    replay (fun r => (guard r).bind fun _ => (route r).bind fun _ =>
      if current (getRoute (putRoute (fun _ => .unopened) (i r) (native r)) (i r))
                 (claims r) (ordinary r) then .ok () else .error .stale) rows =
    replay (fun r => (guard r).bind fun _ => (route r).bind fun _ =>
      if current (some (native r)) (claims r) (ordinary r) then .ok () else .error .stale) rows := by
  simp only [get_put_same]

private def exampleRoute : Route :=
  ⟨fun n => if n = 3 then some 7 else none, fun n => if n = 3 then some 0 else none,
    fun _ => 0, 9, 4, 2⟩

#guard vectorCurrent exampleRoute ⟨7, .ordinary 3, some 0, 4, 2⟩
#guard vectorCurrent exampleRoute ⟨7, .miss 5, none, 4, 2⟩
#guard !vectorCurrent exampleRoute ⟨7, .miss 3, none, 4, 2⟩
#guard !vectorCurrent exampleRoute ⟨7, .ordinary 3, some 0, 4, 3⟩
#guard !vectorCurrent exampleRoute ⟨7, .ordinary 3, some 0, 8, 2⟩

end LeanPoo.Object.PackedReadRoutes
