import LeanPoo.Object.Instance

/-!
An explicitly ranked dependency discipline supplies a total fixed point for
open-recursive slots. The locality proof is about resolved values, so a slot
may use inherited methods as long as its self reads have lower rank.
-/

namespace LeanPoo.Object

universe u v

/-- A plan whose result at each key depends on self only at smaller ranks. -/
structure Ranked (Key : Type u) (Value : Key → Type v)
    (plan : Plan Key Value) where
  rank : Key → Nat
  dependsOnLower : ∀ key (left right : Self Key Value),
    (∀ dependency, rank dependency < rank key →
      left dependency = right dependency) →
    plan.resolve key left = plan.resolve key right

private def Ranked.eval {Key : Type u} {Value : Key → Type v}
    {plan : Plan Key Value} (ranked : Ranked Key Value plan)
    (key : Key) : Option (Value key) :=
  plan.resolve key (fun dependency =>
    if _smaller : ranked.rank dependency < ranked.rank key then
      ranked.eval dependency
    else none)
termination_by ranked.rank key
decreasing_by exact _smaller

/-- Instantiate an open-recursive plan by well-founded slot evaluation. -/
def Ranked.instantiate {Key : Type u} {Value : Key → Type v}
    {plan : Plan Key Value} (ranked : Ranked Key Value plan) :
    Instance Key Value plan :=
  { state := ranked.eval
    agrees := by
      intro key
      have same := ranked.dependsOnLower key ranked.eval
        (fun dependency =>
          if smaller : ranked.rank dependency < ranked.rank key then
            ranked.eval dependency
          else none)
        (by
          intro dependency smaller
          simp [smaller])
      rw [same]
      exact (Ranked.eval.eq_1 ranked key).symm }

/-- Explicit self-dependency claims with finite support. The locality
proof makes the declaration authoritative even though Lean functions are
otherwise opaque to dependency inspection. -/
structure Dependencies (Key : Type u) (Value : Key → Type v)
    (plan : Plan Key Value) where
  keys : List Key
  reads : Key → List Key
  supported : ∀ key dependency, dependency ∈ reads key → key ∈ keys
  dependsOnlyOn : ∀ key (left right : Self Key Value),
    (∀ dependency, dependency ∈ reads key →
      left dependency = right dependency) →
    plan.resolve key left = plan.resolve key right

inductive DependencyError (Key : Type u) where
  | unknownDependency (key dependency : Key)
  | blocked (remaining : List Key)
  | invalidOrder (order : List Key)
  deriving Repr

/-- A dependency-first schedule with the edge ordering needed for induction
over resolved values. -/
structure Scheduled {Key : Type u} {Value : Key → Type v}
    {plan : Plan Key Value} (spec : Dependencies Key Value plan) where
  order : List Key
  ranked : Ranked Key Value plan
  edgeLower : ∀ key dependency, dependency ∈ spec.reads key →
    ranked.rank dependency < ranked.rank key

/-- A bounded dependency-first scheduler. A blocked remainder contains a
cycle or a dependency absent from the supplied finite key list. -/
private def Dependencies.schedule [BEq Key] [LawfulBEq Key] [Hashable Key]
    (keys : List Key) (reads : Key → List Key) :
    Except (DependencyError Key) (List Key) :=
  go keys [] {} keys.length
where
  go (remaining done : List Key) (doneSet : Std.HashSet Key) : Nat →
      Except (DependencyError Key) (List Key)
    | 0 =>
        if remaining.isEmpty then .ok done.reverse
        else .error (.blocked remaining)
    | fuel + 1 =>
        if remaining.isEmpty then .ok done.reverse
        else
          match remaining.find? (fun key =>
              (reads key).all fun dependency => doneSet.contains dependency) with
          | none => .error (.blocked remaining)
          | some key =>
              go (remaining.filter (fun candidate => candidate != key))
                (key :: done) (doneSet.insert key) fuel

/-- Infer a rank from declared dependencies, then check every edge before
producing a proof-bearing ranked plan. An absent source identifies its reader;
after that check, a blocked remainder contains a dependency cycle. -/
def Dependencies.scheduleRanked {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    {plan : Plan Key Value} (spec : Dependencies Key Value plan) :
    Except (DependencyError Key) (Scheduled spec) := do
  for key in spec.keys do
    for dependency in spec.reads key do
      unless spec.keys.contains dependency do
        throw (.unknownDependency key dependency)
  let order ← Dependencies.schedule spec.keys spec.reads
  let rank := fun key => order.idxOf key
  if checked : spec.keys.all (fun key =>
      (spec.reads key).all (fun dependency =>
        decide (rank dependency < rank key))) = true then
    have edgeLower : ∀ key dependency, dependency ∈ spec.reads key →
        rank dependency < rank key := by
      intro key dependency membership
      have keyChecked := List.all_eq_true.mp checked key
        (spec.supported key dependency membership)
      have edgeChecked :=
        List.all_eq_true.mp keyChecked dependency membership
      exact of_decide_eq_true edgeChecked
    return {
      order
      ranked := {
        rank
        dependsOnLower := by
          intro key left right lower
          apply spec.dependsOnlyOn key left right
          intro dependency membership
          exact lower dependency (edgeLower key dependency membership) }
      edgeLower }
  else
    throw (.invalidOrder order)

/-- Forget the schedule while retaining its fixed-point construction. -/
def Dependencies.inferRanked {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    {plan : Plan Key Value} (spec : Dependencies Key Value plan) :
    Except (DependencyError Key) (Ranked Key Value plan) :=
  spec.scheduleRanked.map Scheduled.ranked

/-- Construct a fixed-point instance directly from a checked finite
dependency declaration. The returned state satisfies the original plan's
resolver equation. -/
def Dependencies.instantiate {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    {plan : Plan Key Value} (spec : Dependencies Key Value plan) :
    Except (DependencyError Key) (Instance Key Value plan) :=
  spec.scheduleRanked.map (fun scheduled => scheduled.ranked.instantiate)

end LeanPoo.Object
