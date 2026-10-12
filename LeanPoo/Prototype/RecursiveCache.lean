import LeanPoo.Prototype.RecursiveSemantics

/-! Safe call-by-need evaluation of explicit recursive interactions.
Every memo entry carries a kernel evaluation derivation for the exact program.
Active requests produce cycle diagnostics, separately from source errors and
finite-budget exhaustion. Completed source errors are memoized like values. -/
namespace LeanPoo.Prototype.Recursive.Cached

inductive Completed (α : Type) where
  | value (value : α)
  | error (message : String)
  deriving Repr, BEq

def Completed.observation : Completed α → Observation α
  | .value answer => .value answer
  | .error message => .error message

structure Receipt (program : Generator Input Output) (tree : Interaction Input Output α) where
  result : Completed α
  sound : Evaluates program tree result.observation

structure Entry (program : Generator Input Output) where
  input : Input
  receipt : Receipt program (program input)

structure Statistics where
  hits : Nat := 0
  misses : Nat := 0
  steps : Nat := 0
  deriving Repr, BEq

/-- The program index prevents reuse after a change of effective slot storage. -/
structure Cache (program : Generator Input Output) where
  entries : List (Entry program) := []
  statistics : Statistics := {}

def Cache.lookup [DecidableEq Input] (cache : Cache program) (input : Input) :
    Option (Receipt program (program input)) :=
  let rec lookup : List (Entry program) → Option (Receipt program (program input))
    | [] => none
    | entry :: rest =>
      if same : input = entry.input then
        some (by cases same; exact entry.receipt)
      else lookup rest
  lookup cache.entries

inductive Diagnostic (Input : Type) where
  | budgetExhausted
  | cycle (path : List Input)
  deriving Repr, BEq

mutual
  /-- The budget bounds machine recursion depth, including continuations.
  It is distinct from the source observer's recursive-self depth. -/
  def evaluate [DecidableEq Input] (program : Generator Input Output)
      (tree : Interaction Input Output α) (active : List Input) (cache : Cache program) :
      Nat → Except (Diagnostic Input) (Receipt program tree × Cache program)
    | 0 => .error .budgetExhausted
    | fuel + 1 =>
      let cache := { cache with statistics :=
        { cache.statistics with steps := cache.statistics.steps + 1 } }
      match tree with
      | .value value => .ok (⟨.value value, .value⟩, cache)
      | .error message => .ok (⟨.error message, .error⟩, cache)
      | .call input next => do
        let (head, cache) ← resolve program input active cache fuel
        match head with
        | ⟨.error message, proof⟩ => return (⟨.error message, .callError proof⟩, cache)
        | ⟨.value answer, proof⟩ =>
          let (tail, cache) ← evaluate program (next answer) active cache fuel
          return (⟨tail.result, .callValue proof tail.sound⟩, cache)

  def resolve [DecidableEq Input] (program : Generator Input Output)
      (input : Input) (active : List Input) (cache : Cache program) :
      Nat → Except (Diagnostic Input) (Receipt program (program input) × Cache program)
    | 0 => .error .budgetExhausted
    | fuel + 1 =>
      match cache.lookup input with
      | some receipt => .ok (receipt, { cache with statistics :=
          { cache.statistics with hits := cache.statistics.hits + 1 } })
      | none =>
        if input ∈ active then .error (.cycle (active.reverse ++ [input]))
        else do
          let cache := { cache with statistics :=
            { cache.statistics with misses := cache.statistics.misses + 1 } }
          let (receipt, cache) ← evaluate program (program input) (input :: active) cache fuel
          return (receipt, { cache with entries := ⟨input, receipt⟩ :: cache.entries })
end

def run [DecidableEq Input] (program : Generator Input Output) (input : Input)
    (budget : Nat) (cache : Cache program := {}) :
    Except (Diagnostic Input) (Receipt program (program input) × Cache program) :=
  resolve program input [] cache budget

/-- Every returned or memoized result has an observation at a finite source
depth. Diagnostics do not masquerade as source-language errors. -/
theorem Receipt.observed (receipt : Receipt program (program input)) :
    ∃ depth, solve program depth input = receipt.result.observation :=
  solve_complete receipt.sound

theorem Receipt.agrees (receipt : Receipt program (program input)) (depth : Nat)
    (known : solve program depth input ≠ .pending) :
    solve program depth input = receipt.result.observation := by
  obtain ⟨other, found⟩ := receipt.observed
  have left := (solve_refines program depth (max depth other) (Nat.le_max_left _ _) input).known known
  have right := (solve_refines program other (max depth other) (Nat.le_max_right _ _) input).known
    (by rw [found]; exact receipt.sound.known)
  exact left.trans (right.symm.trans found)

end LeanPoo.Prototype.Recursive.Cached
