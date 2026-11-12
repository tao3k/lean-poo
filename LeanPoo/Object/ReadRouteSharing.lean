-- SPDX-License-Identifier: Apache-2.0 AND LGPL-2.1-or-later
import Init.Data.List.Pairwise
namespace LeanPoo.Object.ReadRouteSharing

-- A single pure sweep in one stable world. No writer or callback occurs in
-- key, route or live. Effect boundaries start another sweep with empty seen.
def original {Record Receiver Error : Type} (owner : Record → Receiver)
    (key : Record → Except Error Unit) (route : Receiver → Except Error Unit)
    (live : Record → Except Error Unit) : List Record → Except Error Unit
  | [] => .ok ()
  | read :: rest => do
    key read
    route (owner read)
    live read
    original owner key route live rest

def admittedRoute {Receiver Error : Type} [DecidableEq Receiver]
    (route : Receiver → Except Error Unit) (seen : List Receiver) (receiver : Receiver) :
    Except Error Unit := if receiver ∈ seen then .ok () else route receiver

def shared {Record Receiver Error : Type} [DecidableEq Receiver]
    (owner : Record → Receiver) (key : Record → Except Error Unit)
    (route : Receiver → Except Error Unit) (live : Record → Except Error Unit)
    (seen : List Receiver) : List Record → Except Error Unit
  | [] => .ok ()
  | read :: rest => do
    key read
    admittedRoute route seen (owner read)
    live read
    shared owner key route live (owner read :: seen) rest

theorem exact {Record Receiver Error : Type} [DecidableEq Receiver]
    (owner : Record → Receiver) (key : Record → Except Error Unit)
    (route : Receiver → Except Error Unit) (live : Record → Except Error Unit)
    (reads : List Record) (seen : List Receiver)
    (certified : ∀ receiver ∈ seen, route receiver = .ok ()) :
    shared owner key route live seen reads = original owner key route live reads := by
  induction reads generalizing seen with
  | nil => rfl
  | cons read rest ih =>
    have current : admittedRoute route seen (owner read) = route (owner read) := by
      unfold admittedRoute
      split
      · rename_i present
        rw [certified (owner read) present]
      · rfl
    cases admission : route (owner read) with
    | error cause =>
      simp [shared, original, current, admission, Bind.bind, Except.bind]
    | ok result =>
      cases result
      have next : ∀ receiver ∈ owner read :: seen, route receiver = .ok () := by
        intro receiver member
        cases List.mem_cons.mp member with
        | inl same => simpa [same] using admission
        | inr prior => exact certified receiver prior
      have tail := ih (owner read :: seen) next
      simp [shared, original, current, admission, tail, Bind.bind, Except.bind]

theorem fresh_exact {Record Receiver Error : Type} [DecidableEq Receiver]
    (owner : Record → Receiver) (key : Record → Except Error Unit)
    (route : Receiver → Except Error Unit) (live : Record → Except Error Unit)
    (reads : List Record) :
    shared owner key route live [] reads = original owner key route live reads :=
  exact owner key route live reads [] (by simp)

-- The first live error remains first even if the same receiver appears later.
example : shared (fun _ : Nat => 0) (fun _ => .ok ())
    (fun _ => .ok ()) (fun r => .error r) [] [1, 2] = .error 1 := rfl

-- Sharing cannot skip the key grammar, including later reads of the same owner.
example : shared (fun _ : Nat => 0)
    (fun r => if r = 2 then .error 13 else .ok ())
    (fun _ => .ok ()) (fun _ => .ok ()) [] [1, 2] = .error 13 := rfl

-- Reusing an old seen set after an edit is unsound; fresh admission refuses.
example : shared (fun _ : Nat => 0) (fun _ => .ok ())
    (fun _ => .error 7) (fun _ => .ok ()) [0] [1] = .ok () ∧
    original (fun _ : Nat => 0) (fun _ => .ok ())
      (fun _ => .error 7) (fun _ => .ok ()) [1] = .error 7 := by constructor <;> rfl

def routeMisses {Record Receiver : Type} [DecidableEq Receiver]
    (owner : Record → Receiver) (seen : List Receiver) : List Record → Nat
  | [] => 0
  | read :: rest =>
    if owner read ∈ seen then routeMisses owner (owner read :: seen) rest
    else (routeMisses owner (owner read :: seen) rest) + 1

theorem routeMisses_le_length {Record Receiver : Type} [DecidableEq Receiver]
    (owner : Record → Receiver) (reads : List Record) (seen : List Receiver) :
    routeMisses owner seen reads ≤ reads.length := by
  induction reads generalizing seen with
  | nil => exact Nat.le_refl 0
  | cons read rest ih =>
    simp only [routeMisses, List.length_cons]
    split
    · exact Nat.le_trans (ih _) (Nat.le_succ _)
    · exact Nat.succ_le_succ (ih _)

-- Refinement to the topology's dense receiver index. The domain consists of
-- admitted projection receivers. Each sweep owns fresh flags, not the index.
def mark (flags : Nat → Bool) (index : Nat) : Nat → Bool :=
  fun position => if position = index then true else flags position

theorem mark_certified {Receiver Error : Type}
    (index : Receiver → Nat)
    (distinct : ∀ a b, index a = index b → a = b)
    (route : Receiver → Except Error Unit) (flags : Nat → Bool)
    (certified : ∀ receiver, flags (index receiver) = true → route receiver = .ok ())
    (receiver : Receiver) (accepted : route receiver = .ok ()) :
    ∀ query, mark flags (index receiver) (index query) = true → route query = .ok () := by
  intro query marked
  by_cases same : index query = index receiver
  · have equality := distinct query receiver same
    simpa [equality] using accepted
  · exact certified query (by simpa [mark, same] using marked)

theorem empty_certified {Receiver Error : Type} (index : Receiver → Nat)
    (route : Receiver → Except Error Unit) :
    ∀ receiver, (fun _ : Nat => false) (index receiver) = true → route receiver = .ok () := by
  simp

-- Bootstrap has no receiver-table route. Its semantic routing identity is
-- None, not Some owner; it cannot certify that owner's later ordinary route.
def optionalRoute {Receiver Error : Type} (route : Receiver → Except Error Unit) :
    Option Receiver → Except Error Unit
  | none => .ok ()
  | some receiver => route receiver

example : shared (fun normal : Bool => if normal then some (0 : Nat) else none)
    (fun _ => .ok ()) (optionalRoute (fun _ => .error 7)) (fun _ => .ok ())
    [] [false, true] = .error 7 := rfl

-- A failed descriptor admission delegates to the exact original checker;
-- it does not query even the receiver index on that path.
def guardedSweep {Record Receiver Error : Type} [DecidableEq Receiver]
    (supported : Bool) (owner : Record → Receiver)
    (key : Record → Except Error Unit) (route : Receiver → Except Error Unit)
    (live : Record → Except Error Unit) (reads : List Record) : Except Error Unit :=
  if supported then shared owner key route live [] reads
  else original owner key route live reads

theorem guarded_exact {Record Receiver Error : Type} [DecidableEq Receiver]
    (supported : Bool) (owner : Record → Receiver)
    (key : Record → Except Error Unit) (route : Receiver → Except Error Unit)
    (live : Record → Except Error Unit) (reads : List Record) :
    guardedSweep supported owner key route live reads = original owner key route live reads := by
  cases supported <;> simp [guardedSweep, fresh_exact]

def newRoutes {Record Receiver : Type} [DecidableEq Receiver]
    (owner : Record → Receiver) (seen : List Receiver) : List Record → List Receiver
  | [] => []
  | read :: rest =>
    if owner read ∈ seen then newRoutes owner (owner read :: seen) rest
    else owner read :: newRoutes owner (owner read :: seen) rest

theorem newRoutes_fresh {Record Receiver : Type} [DecidableEq Receiver]
    (owner : Record → Receiver) (reads : List Record) (seen : List Receiver) :
    ∀ receiver ∈ newRoutes owner seen reads, receiver ∉ seen := by
  induction reads generalizing seen with
  | nil => simp [newRoutes]
  | cons read rest ih =>
    intro receiver member
    by_cases known : owner read ∈ seen
    · simp only [newRoutes, known, ↓reduceIte] at member
      exact fun prior => ih _ receiver member (List.mem_cons_of_mem _ prior)
    · simp only [newRoutes, known, ↓reduceIte] at member
      cases List.mem_cons.mp member with
      | inl same => simpa [same] using known
      | inr later =>
        exact fun prior => ih _ receiver later (List.mem_cons_of_mem _ prior)

theorem newRoutes_nodup {Record Receiver : Type} [DecidableEq Receiver]
    (owner : Record → Receiver) (reads : List Record) (seen : List Receiver) :
    (newRoutes owner seen reads).Nodup := by
  induction reads generalizing seen with
  | nil => simp [newRoutes]
  | cons read rest ih =>
    by_cases known : owner read ∈ seen
    · simpa [newRoutes, known] using ih (owner read :: seen)
    · simp only [newRoutes, known, ↓reduceIte, List.nodup_cons]
      constructor
      · intro member
        exact newRoutes_fresh owner rest (owner read :: seen) (owner read) member (by simp)
      · exact ih _

theorem routeMisses_eq_unique_routes {Record Receiver : Type} [DecidableEq Receiver]
    (owner : Record → Receiver) (reads : List Record) (seen : List Receiver) :
    routeMisses owner seen reads = (newRoutes owner seen reads).length := by
  induction reads generalizing seen with
  | nil => rfl
  | cons read rest ih =>
    simp only [routeMisses, newRoutes]
    split <;> simp [ih]

theorem newRoutes_mem_iff {Record Receiver : Type} [DecidableEq Receiver]
    (owner : Record → Receiver) (reads : List Record) (seen : List Receiver)
    (receiver : Receiver) :
    receiver ∈ newRoutes owner seen reads ↔
      receiver ∉ seen ∧ ∃ read ∈ reads, owner read = receiver := by
  induction reads generalizing seen with
  | nil => simp [newRoutes]
  | cons read rest ih =>
    by_cases same : receiver = owner read
    · subst receiver
      by_cases known : owner read ∈ seen <;> simp [newRoutes, known, ih]
    · by_cases known : owner read ∈ seen <;>
        simp [newRoutes, known, ih, same, Ne.symm same]

-- Bind routing positions during the existing authenticated topology build.
-- This is structural index data, not a cached route/currentness verdict.
def bindPositions {Record Receiver : Type} (owner : Record → Receiver)
    (index : Receiver → Nat) (reads : List Record) : List Nat :=
  reads.map (fun read => index (owner read))

theorem bound_position_exact {Record Receiver : Type}
    (owner : Record → Receiver) (index : Receiver → Nat)
    (reads : List Record) (position : Nat) (within : position < reads.length) :
    (bindPositions owner index reads)[position]'(by simpa [bindPositions] using within) =
      index (owner reads[position]) := by simp [bindPositions]

theorem reverse_binding_exact {Record Receiver : Type}
    (owner : Record → Receiver) (index : Receiver → Nat) (reads : List Record) :
    bindPositions owner index reads.reverse = (bindPositions owner index reads).reverse := by
  simp [bindPositions]

theorem extended_index_preserves_bindings {Record Receiver : Type}
    (owner : Record → Receiver) (before after : Receiver → Nat) (reads : List Record)
    (preserved : ∀ read ∈ reads, after (owner read) = before (owner read)) :
    bindPositions owner after reads = bindPositions owner before reads := by
  apply List.map_congr_left
  exact preserved

theorem descending_fill_exact {Record Receiver : Type}
    (owner : Record → Receiver) (index : Receiver → Nat)
    (reversedReads : List Record) (position : Nat) (within : position < reversedReads.length) :
    (bindPositions owner index reversedReads.reverse)[position]'(by
      simpa [bindPositions] using within) =
    index (owner (reversedReads[reversedReads.length - 1 - position]'
      (Nat.sub_one_sub_lt_of_lt within))) := by
  simp only [bindPositions, List.getElem_map, List.getElem_reverse]

end LeanPoo.Object.ReadRouteSharing
