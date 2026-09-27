import Std

/-! A small persistent LRU cache for complete multiple-dispatch shapes.
The hash map keeps lookups independent of the number of cached shapes; the
eight-entry recency list makes eviction bounded. -/

namespace LeanPoo.Object

abbrev DispatchShape := List (List String)

structure ShapeCache (Value : Type) where
  values : Std.HashMap DispatchShape Value := {}
  recent : List DispatchShape := []

namespace ShapeCache

def capacity : Nat := 8

def size (cache : ShapeCache Value) : Nat := cache.values.size

def get? (cache : ShapeCache Value) (shape : DispatchShape) : Option Value :=
  cache.values.get? shape

/-- Insert or refresh a shape and evict the least recently used entry after
the eighth shape. Existing immutable cache values are unchanged. -/
def remember (cache : ShapeCache Value) (shape : DispatchShape)
    (value : Value) : ShapeCache Value := Id.run do
  let order := shape :: cache.recent.filter (· != shape)
  let mut values := cache.values.insert shape value
  for stale in order.drop capacity do
    values := values.erase stale
  return { values, recent := order.take capacity }

/-- A hit on the most recent shape needs no new cache allocation. -/
def touch (cache : ShapeCache Value) (shape : DispatchShape) : ShapeCache Value :=
  if cache.recent.head? == some shape then cache
  else match cache.get? shape with
    | some value => cache.remember shape value
    | none => cache

end ShapeCache
end LeanPoo.Object
