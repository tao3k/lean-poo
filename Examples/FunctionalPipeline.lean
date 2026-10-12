import LeanPoo.Functional.RegistryPatch
import LeanPoo.Functional.Requirements

/-! Build a small capability dictionary, prepare a consumer once, and reuse it
at different contexts. A derived provider keeps the original reusable. -/
namespace LeanPoo.Examples.FunctionalPipeline
open Functional

structure Basket where
  units : Nat

inductive Capability where
  | merchandise | shipping
  deriving DecidableEq, BEq, Repr

abbrev Values := fun (_ : Basket) (_ : Capability) => Nat
abbrev Capabilities := Provider Basket Capability Values

def base : Capabilities :=
  Provider.patchKey
    (Provider.patchKey (fun _ => none) .merchandise (some (fun basket => basket.units * 10)))
    .shipping (some (fun basket => if basket.units ≥ 5 then 0 else 5))

def discount : Capabilities :=
  Provider.patchKey (fun _ => none) .merchandise (some (fun basket => basket.units * 8))

def sale : Capabilities := Provider.compose discount base

structure Quote where
  merchandise : Nat
  shipping : Nat
  total : Nat
  deriving Repr

def prepare (provider : Capabilities) : Except Capability (Factory Basket (fun _ => Quote)) :=
  Requirements.prepareWith provider [.merchandise, .shipping] fun _ data =>
    ⟨data.1, data.2.1, data.1 + data.2.1⟩

def totals (provider : Capabilities) : Except Capability (List Nat) := do
  let quote ← prepare provider
  let total := Factory.map (fun _ quote => quote.total) quote
  return [total ⟨2⟩, total ⟨6⟩]

#guard (totals base).toOption == some [25,60]
#guard (totals sale).toOption == some [21,48]
#guard (match prepare (Provider.patchKey base .shipping none) with
  | .error missing => missing == .shipping | .ok _ => false)

def run : IO Unit := do
  let .ok quote := prepare sale | throw (IO.userError "missing quote capability")
  -- Choose a follow-up factory using the first result; it gets the same basket.
  let label := Factory.bind quote fun _ quote =>
    if quote.total ≥ 40 then fun basket => s!"bulk ({basket.units} units)"
    else fun basket => s!"ordinary ({basket.units} units)"
  IO.println s!"retained base totals: {repr (totals base).toOption}"
  IO.println s!"derived sale totals: {repr (totals sale).toOption}"
  IO.println s!"prepared sale: {repr (quote ⟨6⟩)}, {label ⟨6⟩}"

#eval run
end LeanPoo.Examples.FunctionalPipeline
