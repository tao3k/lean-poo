-- SPDX-License-Identifier: Apache-2.0 AND LGPL-2.1-or-later
import LeanPoo.Object.ClosAdmission.CandidateOrder
import Init.Data.List.Lex

/-! CLOS distinguishes logical classes, POO prototypes, and value identity.
The shape and admitted argument precedence determine static distances.
An eql candidate stays in the declared order, conditional on the live
comparison to its target. -/
namespace LeanPoo.Object.ClosAdmission.CandidateShape

inductive Atom (Key Value : Type) where
  | eql (target : Value)
  | class (target : Key)
  | prototype (target : Key)
  | any

structure Shape (Key : Type) where
  classOrder : List Key
  prototypeOrder : List Key
  universalSpan : Nat

def staticDistance [BEq Key] (shape : Shape Key) : Atom Key Value → Option Nat
  | .eql _ => some 0
  | .class target =>
    (shape.classOrder.findIdx? (· == target)).map (· + 1)
  | .prototype target =>
    (shape.prototypeOrder.findIdx? (· == target)).map (· + 1)
  | .any => some (shape.universalSpan + 2)

def acceptsValue (eqv : Value → Value → Bool) (value : Value) : Atom Key Value → Bool
  | .eql target => eqv value target
  | _ => true

def liveDistance [BEq Key] (eqv : Value → Value → Bool)
    (value : Value) (shape : Shape Key) (atom : Atom Key Value) : Option Nat :=
  match atom with
  | .eql target => if eqv value target then some 0 else none
  | .class target => (shape.classOrder.findIdx? (· == target)).map (· + 1)
  | .prototype target => (shape.prototypeOrder.findIdx? (· == target)).map (· + 1)
  | .any => some (shape.universalSpan + 2)

theorem live_distance_factors [BEq Key] (eqv : Value → Value → Bool) (value : Value)
    (shape : Shape Key) (atom : Atom Key Value) :
    liveDistance eqv value shape atom =
      if acceptsValue eqv value atom then staticDistance shape atom else none := by
  cases atom <;> simp [liveDistance, staticDistance, acceptsValue] <;> rfl

/-- This is the pure suffix of distance computation, after the original
observations of every specializer. The arity-aligned zipper is shared. -/
abbrev Required (Key Value : Type) := List (Value × Shape Key × Atom Key Value)

def staticVector [BEq Key] (required : List (Shape Key × Atom Key Value)) :
    Option (List Nat) := required.mapM fun (shape, atom) => staticDistance shape atom

def liveVector [BEq Key] (eqv : Value → Value → Bool) (required : Required Key Value) :
    Option (List Nat) := required.mapM fun (value, shape, atom) => liveDistance eqv value shape atom

theorem live_vector_factors [BEq Key] (eqv : Value → Value → Bool) (required : Required Key Value) :
    liveVector eqv required =
      if required.all (fun (value, _, atom) => acceptsValue eqv value atom) then
        staticVector (required.map Prod.snd)
      else none := by
  induction required with
  | nil => rfl
  | cons row rest ih =>
    rcases row with ⟨value, shape, atom⟩
    simp only [liveVector, staticVector, List.map_cons, List.mapM_cons, List.all_cons]
    rw [live_distance_factors]
    change (do
      let distance ← (if acceptsValue eqv value atom then staticDistance shape atom else none)
      let tail ← liveVector eqv rest
      pure (distance :: tail)) =
      if acceptsValue eqv value atom &&
          rest.all (fun (v, _, a) => acceptsValue eqv v a) then
        (do let distance ← staticDistance shape atom
            let tail ← staticVector (rest.map Prod.snd)
            pure (distance :: tail))
      else none
    rw [ih]
    cases acceptsValue eqv value atom <;>
      cases rest.all (fun (v, _, a) => acceptsValue eqv v a) <;>
      cases staticDistance shape atom <;> simp [Option.bind, bind, pure]

/-- An admitted permutation projects required-argument distances to the
Scheme comparator's argument order. Equality is left-biased by stable sort. -/
def precedenceKey (argumentOrder distances : List Nat) : List Nat :=
  argumentOrder.map fun index => distances[index]?.getD 0

def rankedLe (argumentOrder : List Nat) (a b : List Nat) : Bool :=
  decide (precedenceKey argumentOrder a ≤ precedenceKey argumentOrder b)

theorem candidate_filter_in_c4_order (argumentOrder : List Nat) (distance : Method → List Nat)
    (selected : Method → Bool) (rows : List Method) :
    (rows.mergeSort (fun a b => rankedLe argumentOrder (distance a) (distance b))).filter selected =
      (rows.filter selected).mergeSort (fun a b => rankedLe argumentOrder (distance a) (distance b)) := by
  apply CandidateOrder.filter_published_order
  · intro a b c ab bc
    exact decide_eq_true (List.le_trans (of_decide_eq_true ab) (of_decide_eq_true bc))
  · intro a b
    simp only [rankedLe, Bool.or_eq_true, decide_eq_true_eq]
    exact List.le_total _ _

/-- Same C4 shape, distinct live values. The eql candidate's static rank
does not change, while applicability does. -/
private def exampleShape : Shape Nat := ⟨[2, 5], [1, 5], 2⟩
#guard staticDistance exampleShape (.eql 7) == some 0
#guard liveDistance (· == ·) 7 exampleShape (.eql 7) == some 0
#guard liveDistance (· == ·) 8 exampleShape (.eql 7) == none
#guard staticDistance exampleShape (.class 5 : Atom Nat Nat) == some 2
#guard staticDistance exampleShape (.prototype 5 : Atom Nat Nat) == some 2


structure Candidate (Method Key Value : Type) where
  method : Method
  required : List (Shape Key × Atom Key Value)

def Candidate.guardAccepts (candidate : Candidate Method Key Value)
    (eqv : Value → Value → Bool) (actual : List Value) : Bool :=
  (actual.zip candidate.required).all (fun (value, _, atom) => acceptsValue eqv value atom)

private theorem admitted_zip_projection (actual : List A) (required : List B)
    (arity : required.length ≤ actual.length) :
    (actual.zip required).map Prod.snd = required := by
  induction required generalizing actual with
  | nil => simp
  | cons head rest ih =>
    cases actual with
    | nil => simp at arity
    | cons arg tail =>
      have enough : rest.length ≤ tail.length := by simpa using arity
      simp [ih tail enough]

def capturedRows [BEq Key] (candidates : List (Candidate Method Key Value)) :
    List (Candidate Method Key Value × List Nat) :=
  candidates.filterMap fun row => (staticVector row.required).map (row, ·)

def referenceRows [BEq Key] (eqv : Value → Value → Bool) (actual : List Value)
    (candidates : List (Candidate Method Key Value)) :
    List (Candidate Method Key Value × List Nat) :=
  candidates.filterMap fun row => (liveVector eqv (actual.zip row.required)).map (row, ·)

/-- A statically missing class/prototype and a live eql miss both disappear
from the ranked rows. The actual per-method/per-argument read schedule
is separate, and does not use this filter to suppress observations. -/
theorem reference_rows_eq_selected [BEq Key] (eqv : Value → Value → Bool)
    (actual : List Value) (candidates : List (Candidate Method Key Value))
    (arity : ∀ row ∈ candidates, row.required.length ≤ actual.length) :
    referenceRows eqv actual candidates =
      (capturedRows candidates).filter (fun row => row.1.guardAccepts eqv actual) := by
  induction candidates with
  | nil => rfl
  | cons row rest ih =>
    have enough := arity row (by simp)
    have tailArity : ∀ candidate ∈ rest, candidate.required.length ≤ actual.length :=
      fun candidate present => arity candidate (List.mem_cons_of_mem _ present)
    simp only [referenceRows, capturedRows, List.filterMap_cons] at ih ⊢
    have distance : liveVector eqv (actual.zip row.required) =
        if row.guardAccepts eqv actual then staticVector row.required else none := by
      unfold Candidate.guardAccepts
      rw [live_vector_factors, admitted_zip_projection actual row.required enough]
    rw [distance, ih tailArity]
    cases guarded : row.guardAccepts eqv actual <;>
      cases staticVector row.required <;> simp [guarded]

/-- The complete pure ranking moves to publication. Eql compares actual
values at dispatch and keeps the same stable order as cold Scheme. -/
theorem published_ranked_candidates_eq_cold [BEq Key] (eqv : Value → Value → Bool)
    (actual : List Value) (candidates : List (Candidate Method Key Value))
    (arity : ∀ row ∈ candidates, row.required.length ≤ actual.length) (precedence : List Nat) :
    ((capturedRows candidates).mergeSort (fun a b => rankedLe precedence a.2 b.2)).filter
        (fun row => row.1.guardAccepts eqv actual) =
      (referenceRows eqv actual candidates).mergeSort (fun a b => rankedLe precedence a.2 b.2) := by
  rw [reference_rows_eq_selected eqv actual candidates arity]
  exact candidate_filter_in_c4_order precedence Prod.snd
    (fun row => row.1.guardAccepts eqv actual) (capturedRows candidates)

end LeanPoo.Object.ClosAdmission.CandidateShape
