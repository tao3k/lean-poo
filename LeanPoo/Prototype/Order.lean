import LeanPoo.Prototype.Delayed

/-! POOF §2: orders are prototypes; compare reads the final self's predicates. -/
namespace LeanPoo.Prototype

structure OrderOps (α : Type) where
  less : α → α → Bool
  equal : α → α → Bool
  greater : α → α → Bool
  compare : α → α → Except String Ordering

def OrderOps.empty : OrderOps α :=
  ⟨fun _ _ => false, fun _ _ => false, fun _ _ => false,
    fun _ _ => .error "order comparison unavailable"⟩

def OrderOps.predicates (less equal greater : α → α → Bool) :
    DelayedProto (OrderOps α) (OrderOps α) (OrderOps α) :=
  fun _ inherited => { inherited.get with less, equal, greater }

private def compareUsing (self : Thunk (OrderOps α)) (x y : α) : Except String Ordering :=
  if self.get.less x y then .ok .lt
  else if self.get.greater x y then .ok .gt
  else if self.get.equal x y then .ok .eq
  else .error "incomparable"

/-- The mixin reads final-self methods, so later predicate overrides apply. -/
def OrderOps.compareMixin : DelayedProto (OrderOps α) (OrderOps α) (OrderOps α) :=
  fun self inherited => { inherited.get with compare := compareUsing self }

def OrderOps.number : DelayedProto (OrderOps Int) (OrderOps Int) (OrderOps Int) :=
  OrderOps.predicates (fun x y => decide (x < y)) (· == ·) (fun x y => decide (x > y))

def OrderOps.string : DelayedProto (OrderOps String) (OrderOps String) (OrderOps String) :=
  OrderOps.predicates (fun x y => decide (x < y)) (· == ·) (fun x y => decide (x > y))

/-- A typed symbol-name carrier; no Scheme interning or wire-format claim. -/
structure Symbol where
  name : String
deriving BEq, DecidableEq, Repr

/-- Symbol comparisons delegate all four operations to the supplied string order. -/
def OrderOps.symbol (strings : OrderOps String) :
    DelayedProto (OrderOps Symbol) (OrderOps Symbol) (OrderOps Symbol) :=
  fun _ inherited => { inherited.get with
    less := fun x y => strings.less x.name y.name
    equal := fun x y => strings.equal x.name y.name
    greater := fun x y => strings.greater x.name y.name
    compare := fun x y => strings.compare x.name y.name }

unsafe def OrderOps.instantiate
    (prototype : DelayedProto (OrderOps α) (OrderOps α) (OrderOps α)) : OrderOps α :=
  (DelayedProto.instantiate prototype (Thunk.pure OrderOps.empty)).get

end LeanPoo.Prototype
