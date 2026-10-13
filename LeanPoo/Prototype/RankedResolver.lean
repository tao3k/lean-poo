import LeanPoo.Prototype.Record

/-! Well-founded closure of an open keyed resolver. Locality is checked
against the actual resolver, independently of its C3/C4 representation. -/
namespace LeanPoo.Prototype
universe u v

structure RankedResolver {Key : Type u} {Value : Key → Type v}
    (resolve : (key : Key) → ((key : Key) → Option (Value key)) → Option (Value key)) where
  rank : Key → Nat
  dependsOnLower : ∀ key left right,
    (∀ dependency, rank dependency < rank key → left dependency = right dependency) →
    resolve key left = resolve key right

namespace RankedResolver
variable {Key : Type u} {Value : Key → Type v}
  {resolve : (key : Key) → ((key : Key) → Option (Value key)) → Option (Value key)}

def close (spec : RankedResolver resolve) (key : Key) : Option (Value key) :=
  resolve key fun dependency =>
    if _smaller : spec.rank dependency < spec.rank key then spec.close dependency else none
termination_by spec.rank key
decreasing_by exact _smaller

theorem closed (spec : RankedResolver resolve) (key : Key) :
    resolve key spec.close = spec.close key := by
  have same := spec.dependsOnLower key spec.close
    (fun dependency => if smaller : spec.rank dependency < spec.rank key then spec.close dependency else none)
    (by intro dependency smaller; simp [smaller])
  rw [same]
  exact (close.eq_1 spec key).symm

/-- The locality discipline determines one fixed point, including absent slots. -/
theorem unique (spec : RankedResolver resolve) (other : (key : Key) → Option (Value key))
    (closed : ∀ key, resolve key other = other key) (key : Key) : other key = spec.close key := by
  have lower : ∀ dependency, spec.rank dependency < spec.rank key → other dependency = spec.close dependency := by
    intro dependency smaller
    exact unique spec other closed dependency
  rw [← closed key, spec.dependsOnLower key other spec.close lower, spec.closed key]
termination_by spec.rank key
decreasing_by exact smaller

end RankedResolver
end LeanPoo.Prototype
