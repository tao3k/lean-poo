import LeanPoo.Functional.OrderedDictionary
import LeanPoo.Functional.Codec

/-! Checked transfers between dynamically addressed resources. A pure
multi-key proposal commits through the actual inherited AVL insertion method;
refused requests retain the exact last completed dictionary snapshot. -/
namespace LeanPoo.Examples.KeyedRebalance
open Functional Prototype

abbrev Resources := OrderedDictionary OrderOps.integer (· < ·) Nat
structure Transfer where
  source : Int
  target : Int
  amount : Nat
  deriving BEq, Repr

inductive Error where
  | sameKey | missing (key : Int) | insufficient (available requested : Nat)
  deriving BEq, Repr

def schema : Codec {request : Transfer // request.source ≠ request.target} Transfer Error :=
  (Codec.identity Transfer Error).refine (fun request => request.source ≠ request.target) .sameKey

def lookup (view : Int → Option Nat) (key : Int) : Except Error Nat :=
  match view key with
  | none => .error (.missing key)
  | some value => .ok value

def propose (view : Int → Option Nat) (request : Transfer) : Except Error (List (Int × Nat)) := do
  let approved ← schema.decode request
  let available ← lookup view approved.val.source
  let destination ← lookup view approved.val.target
  if request.amount ≤ available then
    return [(request.source, available - request.amount), (request.target, destination + request.amount)]
  else throw (.insufficient available request.amount)

def step (state : Resources) (request : Transfer) := state.transact propose request
def run (state : Resources) (requests : List Transfer) := state.transactBatch propose requests

theorem same_key_refused (state : Resources) (request : Transfer)
    (same : request.source = request.target) : step state request = (.error .sameKey, state) := by
  apply state.transact_error
  simp [propose, schema, Codec.refine, Codec.identity, same, bind, Except.bind]

theorem proposed (state : Resources) (request : Transfer) (source target : Nat)
    (distinct : request.source ≠ request.target) (sourceFound : state.get request.source = some source)
    (targetFound : state.get request.target = some target) (enough : request.amount ≤ source) :
    propose state.get request = .ok [(request.source, source - request.amount),
      (request.target, target + request.amount)] := by
  simp [propose, lookup, schema, Codec.refine, Codec.identity, bind, Except.bind,
    distinct, sourceFound, targetFound, enough, pure, Except.pure]

theorem transfer_values (state : Resources) (request : Transfer) (source target : Nat)
    (distinct : request.source ≠ request.target) (sourceFound : state.get request.source = some source)
    (targetFound : state.get request.target = some target) (enough : request.amount ≤ source) :
    (step state request).2.get request.source = some (source - request.amount) ∧
      (step state request).2.get request.target = some (target + request.amount) := by
  have accepted := proposed state request source target distinct sourceFound targetFound enough
  simp [step, OrderedDictionary.transact, accepted, OrderedDictionary.get_writeMany,
    OrderedDictionary.writeView, distinct]

/-- The two addressed quantities conserve their total, for arbitrary keys,
states and admitted amounts. This is not a finite sample assertion. -/
theorem transfer_conserves (state : Resources) (request : Transfer) (source target : Nat)
    (distinct : request.source ≠ request.target) (sourceFound : state.get request.source = some source)
    (targetFound : state.get request.target = some target) (enough : request.amount ≤ source) :
    ((step state request).2.get request.source).getD 0 +
      ((step state request).2.get request.target).getD 0 = source + target := by
  obtain ⟨first, second⟩ := transfer_values state request source target distinct sourceFound targetFound enough
  rw [first, second]
  simp only [Option.getD_some]
  omega

theorem transfer_frame (state : Resources) (request : Transfer) (source target : Nat)
    (distinct : request.source ≠ request.target) (sourceFound : state.get request.source = some source)
    (targetFound : state.get request.target = some target) (enough : request.amount ≤ source)
    (key : Int) (notSource : key ≠ request.source) (notTarget : key ≠ request.target) :
    (step state request).2.get key = state.get key := by
  have accepted := proposed state request source target distinct sourceFound targetFound enough
  simp [step, OrderedDictionary.transact, accepted, OrderedDictionary.get_writeMany,
    OrderedDictionary.writeView, notSource, notTarget]

theorem refused_snapshot (state : Resources) (request : Transfer) (error : Error)
    (refused : propose state.get request = .error error) :
    step state request = (.error error, state) := state.transact_error propose request error refused

theorem reference_batch (state : Resources) (requests : List Transfer) :
    ((run state requests).1, (run state requests).2.get) =
      Validation.traverseState (fun view request => OrderedDictionary.transactView view propose request)
        state.get requests := state.transactBatch_view propose requests

def initial : Resources := (OrderedDictionary.empty _ _ OrderOps.integer_laws).writeMany
  [(1, 10), (2, 2), (3, 4), (4, 0)]
def staged := run initial [⟨1, 2, 3⟩, ⟨2, 3, 6⟩, ⟨3, 4, 1⟩]
def resumed := run staged.2 [⟨2, 3, 2⟩, ⟨3, 4, 1⟩]

#guard staged.1.toOption.isNone
#guard [1, 2, 3, 4].map staged.2.get == [some 7, some 5, some 4, some 0]
#guard [1, 2, 3, 4].map resumed.2.get == [some 7, some 3, some 5, some 1]
#guard [1, 2, 3, 4].map initial.get == [some 10, some 2, some 4, some 0]
#eval IO.println s!"keyed transfers refused={repr staged.1}, resumed={repr ([1, 2, 3, 4].map resumed.2.get)}"

end LeanPoo.Examples.KeyedRebalance
