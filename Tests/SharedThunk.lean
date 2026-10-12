import LeanPoo.Prototype.SharedThunkHeap
import LeanPoo.Prototype.Delayed

open LeanPoo.Prototype
open LeanPoo.Prototype.Recursive
open LeanPoo.Prototype.Recursive.Shared
namespace LeanPoo.Tests.SharedThunk

example (program : Recursive.Generator Input Output) (tree : Interaction Input Output α)
    (result : Observation α) :
    (∃ trace, Runs program tree ⟨result, trace⟩) ↔ Evaluates program tree result :=
  runs_iff_evaluates program tree result

example [DecidableEq Output] (program : Recursive.Generator Input Output) (input : Input)
    (candidate : Candidate Output)
    (accepted : ∃ receipt, admit program (program input) candidate = some receipt) :
    ∃ depth, solve program depth input = candidate.result :=
  admitted_observed program input candidate accepted

example [DecidableEq Output] (program : Recursive.Generator Input Output) (input : Input)
    (result : Observation Output) (evaluation : Evaluates program (program input) result) :
    ∃ depth receipt, (recordSolve program depth input).result = result ∧
      admit program (program input) (recordSolve program depth input) = some receipt :=
  evaluation_admitted program input result evaluation

example (program : Recursive.Generator Input Output) (input : Input) :
    Diverges program input ↔ ∀ candidate, ¬Runs program (program input) candidate :=
  diverges_iff_no_runs program input

example (code : Code) (events : List Knot.Event) (heap : Knot.Heap Code)
    (replayed : Knot.replay code {} events = some heap) (ready : heap.phase = .ready) :
    heap.code = some code ∧ heap.builds = 1 := Knot.one_build code events heap replayed ready

example [DecidableEq Output] {program : Recursive.Generator Input Output}
    (runtime : Runtime program) (input : Input)
    (receipt : Cached.Receipt program (program input)) (accepted : runtime.read input = .ok receipt) :
    ∃ depth, solve program depth input = (runtime.executor input).result :=
  runtime.read_observed input receipt accepted

private def triangular : Recursive.Generator Nat Nat
  | 0 => .value 0
  | n + 1 => .call n fun answer => .value (answer + n + 1)

private def factorial : Recursive.Generator Nat Nat
  | 0 => .value 1
  | n + 1 => .call n fun answer => .value (answer * (n + 1))

private def fibonacci : Recursive.Generator Nat Nat
  | 0 => .value 0
  | 1 => .value 1
  | n + 2 => .call (n + 1) fun first => .call n fun second => .value (first + second)

private def repeated : Recursive.Generator Nat Nat
  | 0 => .value 1
  | n + 1 => .call n fun first => .call n fun second => .value (first + second + 1)

private def errorChain : Recursive.Generator Nat Nat
  | 0 => .error "source-zero"
  | n + 1 => .call n fun answer => .value (answer + 100)

private def afterCallError : Recursive.Generator Nat Nat
  | 0 => .value 3
  | _ + 1 => .call 0 fun _ => .error "after-head"

private def selfLoop : Recursive.Generator Nat Nat := fun input => .call input .value
private def increasing : Recursive.Generator Nat Nat := fun input => .call (input + 1) .value

example (depth input : Nat) : solve selfLoop depth input = .pending := by
  induction depth with
  | zero => rfl
  | succ depth ih => simp [solve, selfLoop, Interaction.interpret, ih]

private def scalarFactorial : Nat → Nat
  | 0 => 1
  | n + 1 => scalarFactorial n * (n + 1)

private def scalarFibonacci : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => scalarFibonacci (n + 1) + scalarFibonacci n

private partial def diverge (n : Nat) : Nat := diverge (n + 1)

private unsafe def run : IO Unit := do
  let terminating := [triangular, factorial, fibonacci, repeated, errorChain, afterCallError]
  let programs := terminating ++ [selfLoop, increasing]
  let mut completed := 0
  let mut refusedCuts := 0
  let mut bounded := 0
  let mut unbounded := 0
  for program in programs do
    let native := compileBounded program
    for depth in List.range 13 do
      for input in List.range 11 do
        let candidate := native (depth, input)
        let reference := recordSolve program depth input
        unless candidate == reference && candidate.result == solve program depth input do
          throw (IO.userError "shared bounded trace/result differs from safe depth semantics")
        match candidate.result, admit program (program input) candidate with
        | .pending, none => refusedCuts := refusedCuts + 1
        | .value answer, some receipt =>
          unless receipt.result.observation == .value answer do throw (IO.userError "admitted value")
          completed := completed + 1
        | .error message, some receipt =>
          unless receipt.result.observation == .error message do throw (IO.userError "admitted error identity")
          completed := completed + 1
        | _, _ => throw (IO.userError "checker completeness or pending refusal")
        bounded := bounded + 1
  for program in terminating do
    let native := compile program
    let runtime := Runtime.new program
    for input in List.range 11 do
      let candidate := native input
      unless candidate == recordSolve program (input + 2) input do
        throw (IO.userError "unbounded shared execution trace differs")
      unless (admit program (program input) candidate).isSome do
        throw (IO.userError "actual unbounded execution was not admitted")
      match runtime.read input, Cached.run program input (4 * (input + 2)) with
      | .ok nativeReceipt, .ok (safeReceipt, cache) =>
        unless nativeReceipt.result.observation == candidate.result &&
            safeReceipt.result.observation == candidate.result do
          throw (IO.userError "checked native read disagrees with the safe shared evaluator")
        match Cached.run program input 1 cache with
        | .ok (hotReceipt, hotCache) =>
          unless hotReceipt.result.observation == candidate.result &&
              hotCache.statistics.hits == cache.statistics.hits + 1 do
            throw (IO.userError "safe shared hot read disagrees")
        | .error _ => throw (IO.userError "safe shared hot read refused")
      | _, _ => throw (IO.userError "completed native/safe read refused")
      unbounded := unbounded + 1
  let triangularNative := compile triangular
  let factorialNative := compile factorial
  let fibonacciNative := compile fibonacci
  let repeatedNative := compile repeated
  for input in List.range 11 do
    unless (triangularNative input).result == .value (input * (input + 1) / 2) &&
        (factorialNative input).result == .value (scalarFactorial input) &&
        (fibonacciNative input).result == .value (scalarFibonacci input) &&
        (repeatedNative input).result == .value (2 ^ (input + 1) - 1) do
      throw (IO.userError "independent scalar controls")
  let valueCandidate := triangularNative 4
  let errorCandidate := (compile errorChain) 4
  let changed : Recursive.Generator Nat Nat := fun input => (triangular input).map (· + 1)
  let attacks : List (Recursive.Generator Nat Nat × Nat × Candidate Nat) := [
    (triangular, 4, { valueCandidate with result := .value 999 }),
    (triangular, 4, { valueCandidate with result := .error "forged" }),
    (triangular, 4, { valueCandidate with result := .pending }),
    (triangular, 4, { valueCandidate with trace := .cut }),
    (triangular, 4, { valueCandidate with trace := .value }),
    (triangular, 4, { valueCandidate with trace := .callError .value }),
    (errorChain, 4, { errorCandidate with result := .error "wrong-source-error" }),
    (errorChain, 4, { errorCandidate with trace := .callValue errorCandidate.trace .value }),
    (changed, 4, valueCandidate),
    (triangular, 5, valueCandidate),
    (triangular, 0, ⟨.value 0, .callValue .value .value⟩),
    (errorChain, 0, ⟨.error "source-zero", .cut⟩)]
  for (program, input, candidate) in attacks do
    unless (admit program (program input) candidate).isNone do
      throw (IO.userError "forged or stale native candidate was admitted")
    let forged : Runtime program := ⟨FixedFunction.ofFun fun _ => candidate⟩
    match forged.read input with
    | .error .unfinished =>
      unless candidate.result == .pending do throw (IO.userError "forged read diagnostic")
    | .error .invalidTrace => pure ()
    | .ok _ => throw (IO.userError "forged executor acquired a safe receipt")
  let pendingRuntime := Runtime.bounded selfLoop 12
  match pendingRuntime.read 0 with
  | .error .unfinished => pure ()
  | _ => throw (IO.userError "bounded loop classified as a completed source error")
  let builds ← IO.mkRef (0 : Nat)
  let counted := LeanPoo.Prototype.instantiate
    (fun self (_ : Unit) => unsafeBaseIO do
      builds.modify (· + 1)
      return FixedFunction.ofFun fun input => record (fun query => self query) (triangular input)) ()
  for input in List.range 33 do
    unless (counted input).result == .value (input * (input + 1) / 2) do
      throw (IO.userError "counted shared closure")
  unless (← builds.get) == 1 do throw (IO.userError "native shared closure rebuilt")
  let shortCircuit : Recursive.Generator Nat Nat := fun input =>
    if input == 0 then .error "stop" else .call 0 fun _ => .value (diverge 0)
  let stopped := (compile shortCircuit) 1
  unless stopped.result == .error "stop" &&
      (admit shortCircuit (shortCircuit 1) stopped).isSome do
    throw (IO.userError "error forced its divergent continuation")
  let parent : Proto (Recursive.Generator Nat Nat) Nat (Recursive.Generator Nat Nat) :=
    fun self base input => if input == 0 then .value base else
      (self (input - 1)).map (· + input)
  let child : Proto (Recursive.Generator Nat Nat) (Recursive.Generator Nat Nat)
      (Recursive.Generator Nat Nat) := fun _ inherited input => (inherited input).map (· + 2)
  let mixed := Recursive.close (compose child parent) 5
  let mixedRuntime := Runtime.new mixed
  for input in List.range 11 do
    match mixedRuntime.read input with
    | .ok receipt =>
      unless receipt.result.observation == .value (7 + input * (input + 1) / 2 + 2 * input) &&
          receipt.result.observation == solve mixed (input + 2) input do
        throw (IO.userError "typed mix lost final self or inherited base")
    | _ => throw (IO.userError "typed mixed native read refused")
  let delayed := compileValue (.value 31 : Interaction Unit Nat Nat)
  let delayedError := compileValue (.error "delayed-error" : Interaction Unit Nat Nat)
  let valueProgram : Recursive.Generator Unit Nat := fun _ => .value 31
  let errorProgram : Recursive.Generator Unit Nat := fun _ => .error "delayed-error"
  for _ in List.range 32 do
    unless delayed.get.result == .value 31 && delayedError.get.result == .error "delayed-error" do
      throw (IO.userError "delayed nonfunction native result")
    unless (admit valueProgram (valueProgram ()) delayed.get).isSome &&
        (admit errorProgram (errorProgram ()) delayedError.get).isSome do
      throw (IO.userError "delayed nonfunction receipt")
  for reads in List.range 65 do
    let events := Knot.construction ++ List.replicate reads Knot.Event.cacheHit
    match Knot.replay "current-body" {} events with
    | none => throw (IO.userError "shared heap protocol refused valid reads")
    | some heap =>
      unless heap.phase == .ready && heap.builds == 1 && heap.reads == reads &&
          Knot.read heap == some "current-body" do
        throw (IO.userError "shared heap identity or build count")
  let invalid := [
    [Knot.Event.forceSelf], [.allocate, .forceSelf], [.allocate, .link, .forceSelf],
    [.allocate, .link, .beginBuild, .forceSelf],
    Knot.construction ++ [.beginBuild], Knot.construction ++ [.link]]
  for events in invalid do
    unless (Knot.replay "current-body" {} events).isNone do
      throw (IO.userError "early forcing or constructor replacement admitted")
  unless bounded == 1144 && unbounded == 66 && completed + refusedCuts == bounded do
    throw (IO.userError "shared execution control denominator")
  IO.println s!"POOF-SHARED-THUNK-OK bounded={bounded} unbounded={unbounded} completed={completed} cuts={refusedCuts} attacks={attacks.length} checkedReads=66 safeCold=66 safeHot=66 mixedReads=11 forgedExecutors=12 heapReads=65 heapRefusals=6 scalar=44 constructorBuilds=1 delayedReads=64 errorShortCircuit=true"

#eval run
#print axioms runs_iff_evaluates
#print axioms admit_iff_runs
#print axioms recordSolve_result
#print axioms evaluation_admitted
#print axioms diverges_iff_no_runs
#print axioms Knot.one_build
#print axioms Knot.invocation_iff
#print axioms Runtime.read_matches
#print axioms Runtime.read_observed
end LeanPoo.Tests.SharedThunk
