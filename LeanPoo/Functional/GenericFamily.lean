import LeanPoo.Functional.GeneralizedMOP
import LeanPoo.Object.DispatchTable
import Std.Data.DHashMap.Lemmas

/-! Checked heterogeneous generic families reuse DispatchTable and each generic's
existing construction, negative watches, invocation and cache laws. Future work. -/
namespace LeanPoo.Functional.GenericFamily
open Object DispatchExtension

structure Model (G Policy Cooked : Type) (Args Method Result : G → Type) where
  keys : List G
  seed : (key : G) → Policy → Cooked → Multimethod (Args key) (Method key) (Result key)
  seedEmpty : ∀ key policy cooked, (seed key policy cooked).cache = {}
  methods : (key : G) → Policy → Cooked → List (Edit (Args key) (Method key))
  watches : (key : G) → List (Watch (Args key))

variable {G Policy Cooked : Type} {Args Method Result : G → Type}
variable [DecidableEq G] [BEq G] [LawfulBEq G] [Hashable G]
variable (model : Model G Policy Cooked Args Method Result) (policy : Policy) (cooked : Cooked)

structure Certified (key : G) (generic : Multimethod (Args key) (Method key) (Result key)) where
  origin : ∃ cold, patch (model.seed key policy cooked) (model.methods key policy cooked) = .ok cold ∧
    GeneralizedMOP.definition generic = GeneralizedMOP.definition cold
  negative : Certificate generic (model.watches key)
  sound : generic.CacheSound

structure Partial where
  table : DispatchTable G Args Method Result
  certified : ∀ key generic, table.get? key = some generic → Certified model policy cooked key generic

/-- Retain exact receipts for every requested generic and no missing signatures. -/
structure Family extends Partial model policy cooked where
  complete : ∀ key ∈ model.keys, (table.get? key).isSome = true

inductive Failure where
  | registration (key : G) (error : MultimethodError)
  | negative (key : G) (generic : Multimethod (Args key) (Method key) (Result key))
      (conflict : Conflict generic (model.watches key))
  | incomplete

def Partial.empty : Partial model policy cooked :=
  ⟨DispatchTable.empty,by intro key generic found; simp [DispatchTable.get?,DispatchTable.empty] at found⟩

def Partial.install (prior : Partial model policy cooked) (key : G)
    (generic : Multimethod (Args key) (Method key) (Result key)) (receipt : Certified model policy cooked key generic) :
    Partial model policy cooked where
  table := prior.table.install key generic
  certified := by
    intro query next found
    by_cases same : key = query
    · subst query
      simp [DispatchTable.get?,DispatchTable.install] at found
      cases found
      exact receipt
    · apply prior.certified query next
      simpa [DispatchTable.get?,DispatchTable.install,Std.DHashMap.get?_insert,same,Ne.symm same] using found

def Partial.build (prior : Partial model policy cooked) (key : G) :
    Except (Failure model) (Partial model policy cooked) :=
  if (prior.table.get? key).isSome then .ok prior else
  match applied : patch (model.seed key policy cooked) (model.methods key policy cooked) with
  | .error error => .error (.registration key error)
  | .ok generic => match check generic (model.watches key) with
    | .error conflict => .error (.negative key generic conflict)
    | .ok negative => .ok (prior.install model policy cooked key generic
        ⟨⟨generic,applied,rfl⟩,negative,patch_sound _ _ _
          ((model.seed key policy cooked).cacheSound_of_empty (model.seedEmpty key policy cooked)) applied⟩)

def build : Except (Failure model) (Family model policy cooked) :=
  let rec go (prior : Partial model policy cooked) : List G → Except (Failure model) (Family model policy cooked)
    | [] => if complete : model.keys.all (fun key => (prior.table.get? key).isSome) = true then
        .ok ⟨prior,by intro key member; exact List.all_eq_true.mp complete key member⟩
      else .error .incomplete
    | key :: rest => match prior.build model policy cooked key with
      | .error error => .error error
      | .ok next => go next rest
  go (Partial.empty model policy cooked) model.keys

/-- A call warms one actual table entry. All receipts remain tied to the same
policy/cooked construction; other signatures retain their exact generic. -/
def Family.invoke (family : Family model policy cooked) (key : G) (args : Args key) :
    Except (DispatchTableError G) (Result key × Family model policy cooked) :=
  match found : family.table.get? key with
  | none => .error (.missing key)
  | some generic => match called : generic.call args with
    | .error error => .error (.dispatch error)
    | .ok (result,updated) =>
      let old := family.certified key generic found
      let receipt : Certified model policy cooked key updated := {
        origin := by
          obtain ⟨cold,generated,same⟩ := old.origin
          exact ⟨cold,generated,(GeneralizedMOP.call_definition generic updated args result called).trans same⟩
        negative := old.negative.afterCall args result updated called
        sound := generic.call_preserves old.sound args result updated called }
      let installed :=  family.toPartial.install model policy cooked key updated receipt
      .ok (result,⟨installed,by
        intro query member
        by_cases same : key = query
        · subst query; simp [installed,Partial.install,DispatchTable.get?,DispatchTable.install]
        · simpa [installed,Partial.install,DispatchTable.get?,DispatchTable.install,
            Std.DHashMap.get?_insert,same,Ne.symm same] using family.complete query member⟩)

/-- The wrapper uses the existing heterogeneous table call exactly. -/
theorem Family.invoke_table (family : Family model policy cooked) (key : G) (args : Args key) :
    (family.invoke model policy cooked key args).map (fun (result,next) => (result,next.table)) =
      family.table.call key args := by
  unfold Family.invoke
  split
  · rename_i found
    simp [DispatchTable.call,DispatchTable.lookup,found,bind,Except.bind,Except.map]
  · rename_i generic found
    split
    · rename_i error called
      simp [DispatchTable.call,DispatchTable.lookup,found,called,bind,Except.bind,Except.map,Except.mapError]
    · rename_i result updated called
      simp [DispatchTable.call,DispatchTable.lookup,found,called,bind,Except.bind,
        Except.map,Except.mapError,pure,Except.pure,Partial.install]

theorem Family.invoke_other (family : Family model policy cooked) (key : G) (args : Args key)
    (result : Result key) (next : Family model policy cooked)
    (called : family.invoke model policy cooked key args = .ok (result,next))
    (other : G) (different : key ≠ other) : next.table.get? other = family.table.get? other := by
  unfold Family.invoke at called
  split at called
  · contradiction
  · split at called
    · contradiction
    · cases called
      simp [Partial.install,DispatchTable.get?,DispatchTable.install,Std.DHashMap.get?_insert,
        different]

omit [DecidableEq G] in
theorem Family.call_correct (family : Family model policy cooked) (key : G)
    (generic : Multimethod (Args key) (Method key) (Result key))
    (found : family.table.get? key = some generic) (args : Args key) :
    (generic.call args).map Prod.fst = generic.referenceCall args :=
  generic.call_correct (family.certified key generic found).sound args

end LeanPoo.Functional.GenericFamily
