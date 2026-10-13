import LeanPoo.Functional.FocusedUpdate
import LeanPoo.Functional.Codec

namespace LeanPoo.Examples.FocusedAllocation
open Functional Prototype

/-- The value's proof is indexed by the budget supplied to its factory. -/
structure Allocation (budget : Nat) where
  cpu : Nat
  io : Nat
  fits : cpu + io ≤ budget

structure Ledger (budget : Nat) where
  allocation : Allocation budget
  tenant : String
  revision : Nat

def allocation (budget : Nat) : Focus (Ledger budget) (Allocation budget) where
  get := Ledger.allocation
  set value ledger := { ledger with allocation := value }
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- Move at most the available source allocation; the total is conserved. -/
def toIO (amount : Nat) (old : Allocation budget) : Allocation budget :=
  let moved := min amount old.cpu
  have enough := Nat.min_le_right amount old.cpu
  ⟨old.cpu-moved, old.io+moved, by have := old.fits; omega⟩

def toCPU (amount : Nat) (old : Allocation budget) : Allocation budget :=
  let moved := min amount old.io
  have enough := Nat.min_le_right amount old.io
  ⟨old.cpu+moved, old.io-moved, by have := old.fits; omega⟩

theorem toIO_total (amount : Nat) (old : Allocation budget) :
    (toIO amount old).cpu + (toIO amount old).io = old.cpu + old.io := by
  dsimp [toIO]
  have := Nat.min_le_right amount old.cpu
  omega

theorem toCPU_total (amount : Nat) (old : Allocation budget) :
    (toCPU amount old).cpu + (toCPU amount old).io = old.cpu + old.io := by
  dsimp [toCPU]
  have := Nat.min_le_right amount old.io
  omega

def baseline : Factory Nat Ledger := fun budget => ⟨⟨budget, 0, by omega⟩, "tenant-A", 7⟩
def rebalance (amount : Nat) : Factory Nat Ledger :=
  Factory.focus allocation (fun budget => if budget % 2 == 0 then toIO amount else toCPU amount) baseline

theorem rebalance_fits (amount budget : Nat) :
    (rebalance amount budget).allocation.cpu + (rebalance amount budget).allocation.io ≤ budget :=
  (rebalance amount budget).allocation.fits

theorem rebalance_frame (amount budget : Nat) :
    (rebalance amount budget).tenant = "tenant-A" ∧ (rebalance amount budget).revision = 7 := ⟨rfl, rfl⟩

def schema (budget : Nat) : Codec (Allocation budget) (Nat × Nat) String :=
  (((Codec.identity Nat String).product (Codec.identity Nat String)).refine
    (fun values => values.1+values.2 ≤ budget) "budget").transport
    (fun values => ⟨values.val.1, values.val.2, values.property⟩)
    (fun value => ⟨(value.cpu,value.io), value.fits⟩) (fun value => by cases value; rfl)

/-- Admission retains the dependent budget proof; the actual delayed lens
installs a proof-bearing method result without touching ledger metadata. -/
def admitAndMove (budget amount : Nat) (wire : Nat × Nat) : Except String (Ledger budget) := do
  let admitted ← (schema budget).decode wire
  let original : Ledger budget := ⟨admitted, "tenant-A", 7⟩
  return (allocation budget).prototype toIO (Thunk.pure amount) (Thunk.pure original)

theorem admitted_total (budget amount : Nat) (wire : Nat × Nat) (approved : Allocation budget)
    (accepted : (schema budget).decode wire = .ok approved) :
    admitAndMove budget amount wire = .ok ⟨toIO amount approved, "tenant-A", 7⟩ := by
  unfold admitAndMove
  rw [accepted]
  rfl

def run : IO Unit := do
  let mut cases := 0
  for budget in List.range 8 do
    for cpu in List.range (budget+1) do
      for io in List.range (budget-cpu+1) do
        for amount in [0,1,3,9] do
          let original ← match (schema budget).decode (cpu,io) with
            | .error _ => throw (IO.userError "valid allocation refused")
            | .ok value => pure value
          -- Independent target-share control, rather than subtracting moved units.
          let total := cpu+io
          let targetIO := min total (io+amount)
          let targetCPU := min total (cpu+amount)
          let movedIO := toIO amount original
          let movedCPU := toCPU amount original
          unless movedIO.io == targetIO && movedIO.cpu == total-targetIO &&
              movedCPU.cpu == targetCPU && movedCPU.io == total-targetCPU do
            throw (IO.userError "allocation movement differs from target-share control")
          let installed ← match admitAndMove budget amount (cpu,io) with
            | .error _ => throw (IO.userError "admitted move refused")
            | .ok ledger => pure ledger
          unless installed.allocation.io == targetIO && installed.allocation.cpu == total-targetIO &&
              installed.tenant == "tenant-A" && installed.revision == 7 do
            throw (IO.userError "delayed proof-bearing focus changed allocation or metadata")
          cases := cases+2
    unless ((schema budget).decode (budget,1)).toOption.isNone do
      throw (IO.userError "over-budget allocation admitted")
    let built := rebalance 3 budget
    unless built.allocation.cpu+built.allocation.io == budget && built.tenant == "tenant-A" && built.revision == 7 do
      throw (IO.userError "dependent factory changed its context or metadata")
  unless cases == 960 do throw (IO.userError s!"allocation coverage drift: {cases}")
  IO.println s!"FOCUSED-ALLOCATION-OK directions={cases} invalid=8 factories=8"

#eval run

#print axioms toIO_total
#print axioms toCPU_total
#print axioms rebalance_fits
#print axioms admitted_total
end LeanPoo.Examples.FocusedAllocation
