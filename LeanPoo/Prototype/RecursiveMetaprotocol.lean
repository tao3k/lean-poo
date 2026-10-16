import LeanPoo.Prototype.MetaBootstrap
import LeanPoo.Functional.PositiveEquations

/-! Finite positive recursive metalevel components, then constant-base bootstrap.
The cook function receives the exact least solution, never a caller's warm seed.
Arbitrary recursive procedures and callback termination remain outside this model. -/
namespace LeanPoo.Prototype.MetaPrototype
open Functional.PositiveEquations
/-- A closed metadata system and the hook kernel cooked from its least solution. -/
structure RecursiveRoot (equations : Equations n)
    (cook : Bits n → Bootstrap Context Key Name α) where
  facts : Bits n
  fixed : step equations facts = facts
  least : ∀ other, step equations other = other → Below facts other
  kernel : Bootstrap Context Key Name α
  cooked : kernel = cook facts
/-- The existing finite-height solver constructs the recursive metalevel root. -/
def closePositive (equations : Equations n) (cook : Bits n → Bootstrap Context Key Name α) :
    RecursiveRoot equations cook :=
  ⟨(close equations).value, (close equations).fixed, least equations, cook (close equations).value, rfl⟩
/-- The result satisfies every declared metadata equation simultaneously. -/
theorem closePositive_fixed (equations : Equations n) (cook : Bits n → Bootstrap Context Key Name α) :
    step equations (closePositive equations cook).facts = (closePositive equations cook).facts :=
  (closePositive equations cook).fixed
/-- Unsupported cyclic facts cannot be chosen merely because they are a fixed point. -/
theorem closePositive_least (equations : Equations n) (cook : Bits n → Bootstrap Context Key Name α)
    (other : Bits n) (fixed : step equations other = other) :
    Below (closePositive equations cook).facts other := (closePositive equations cook).least other fixed
/-- The kernel is derived from the same closed facts, not an earlier revision. -/
theorem closePositive_cooked (equations : Equations n) (cook : Bits n → Bootstrap Context Key Name α) :
    (closePositive equations cook).kernel = cook (closePositive equations cook).facts := rfl
/-- Metadata recursion closes before the kernel's terminating anchor reflection. -/
theorem closePositive_reflect (equations : Equations n) (cook : Bits n → Bootstrap Context Key Name α)
    (self : Context) (source : Key → Except String α) :
    bootstrapReflect (closePositive equations cook).kernel self source =
      .ok (cook (closePositive equations cook).facts) := bootstrapReflect_fixed _ _ _
/-- The automatic metadata solver needs at most one strict advance per Boolean fact.
This is not a bound on cook callbacks, allocation, or the native runtime. -/
theorem closePositive_bound (equations : Equations n) : (close equations).depth ≤ n := updates_bound equations
end LeanPoo.Prototype.MetaPrototype
