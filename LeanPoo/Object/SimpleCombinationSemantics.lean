import LeanPoo.Object.SimplePolicies
import LeanPoo.Object.MethodCombinationSemantics

/-! Ordered semantics for alternative combinations, including the exact
state at the first failure and the unexecuted short-circuit suffix. -/
namespace LeanPoo.Object.MethodCombination
variable {Item Acc Result : Type}

/-- Independent recursive specification of the complete effective method. -/
def simpleReference {Receiver : Type} {M : Type → Type} [Monad M]
    (policy : SimplePolicy Item Acc Result)
    (methods : SimpleMethods Receiver M Item Result) : Receiver → M Result :=
  wrapMethods methods.around fun receiver => do
    match methods.items with
    | [] => return policy.finish policy.empty
    | method :: rest =>
      let first ← method receiver
      let rec visit : Acc → List (Receiver → M Item) → M Result
        | acc, [] => pure (policy.finish acc)
        | acc, method :: rest => do
          if policy.stop acc then return policy.finish acc
          let value ← method receiver
          visit (policy.step value acc) rest
      visit (policy.first first) rest

theorem runSimpleTail_finish {Receiver : Type} {M : Type → Type} [Monad M] [LawfulMonad M]
    (policy : SimplePolicy Item Acc Result) (receiver : Receiver) (acc : Acc)
    (methods : List (Receiver → M Item)) :
    (do let final ← runSimpleTail policy receiver acc methods; pure (policy.finish final)) =
      simpleReference.visit policy receiver acc methods := by
  induction methods generalizing acc with
  | nil => simp [runSimpleTail, simpleReference.visit]
  | cons method rest ih =>
    simp only [runSimpleTail, simpleReference.visit]
    split <;> simp_all

theorem simpleEffective_reference {Receiver : Type} {M : Type → Type} [Monad M] [LawfulMonad M]
    (policy : SimplePolicy Item Acc Result) (methods : SimpleMethods Receiver M Item Result) :
    simpleEffective policy methods = simpleReference policy methods := by
  unfold simpleEffective simpleReference
  rw [callChain_eq_wrappers]
  congr 1
  funext receiver
  cases methods.items with
  | nil => rfl
  | cons first rest => dsimp only; congr 1; funext value; exact runSimpleTail_finish _ _ _ _

/-- Operational derivation: every continuation starts from the previous
method's actual returned state. A stopped group or failure has no suffix step. -/
inductive SimpleRun {Receiver Item Acc Result State Error : Type}
    (policy : SimplePolicy Item Acc Result) (receiver : Receiver) :
    Acc → List (Receiver → EStateM Error State Item) → State → EStateM.Result Error State Acc → Prop
  | nil : SimpleRun policy receiver acc [] state (.ok acc state)
  | stopped (stop : policy.stop acc = true) :
      SimpleRun policy receiver acc (method :: rest) state (.ok acc state)
  | failed (proceed : policy.stop acc = false) (call : (method receiver).run state = .error error retained) :
      SimpleRun policy receiver acc (method :: rest) state (.error error retained)
  | next (proceed : policy.stop acc = false) (call : (method receiver).run state = .ok value retained)
      (tail : SimpleRun policy receiver (policy.step value acc) rest retained outcome) :
      SimpleRun policy receiver acc (method :: rest) state outcome

theorem SimpleRun.sound {Receiver Item Acc Result State Error : Type}
    {policy : SimplePolicy Item Acc Result} {receiver : Receiver} {acc : Acc}
    {methods : List (Receiver → EStateM Error State Item)} {state : State} {outcome : EStateM.Result Error State Acc}
    (derivation : SimpleRun policy receiver acc methods state outcome) :
    (runSimpleTail policy receiver acc methods).run state = outcome := by
  induction derivation with
  | nil => rfl
  | stopped stop => simp [runSimpleTail, stop, EStateM.run, pure, EStateM.pure]
  | failed proceed call =>
    simp only [EStateM.run] at call
    simp [runSimpleTail, proceed, EStateM.run, bind, EStateM.bind, call]
  | next proceed call tail ih =>
    simp only [EStateM.run] at call ih
    simp [runSimpleTail, proceed, EStateM.run, bind, EStateM.bind, call, ih]

theorem SimpleRun.complete {Receiver Item Acc Result State Error : Type}
    (policy : SimplePolicy Item Acc Result) (receiver : Receiver) (acc : Acc)
    (methods : List (Receiver → EStateM Error State Item)) (state : State) :
    SimpleRun policy receiver acc methods state ((runSimpleTail policy receiver acc methods).run state) := by
  induction methods generalizing acc state with
  | nil => exact .nil
  | cons method rest ih =>
    cases stop : policy.stop acc with
    | true => simpa [runSimpleTail, stop, EStateM.run, pure, EStateM.pure] using
        (SimpleRun.stopped (method := method) (rest := rest) (state := state) stop)
    | false =>
      cases call : (method receiver).run state with
      | error error retained =>
        simp only [EStateM.run] at call
        simpa [runSimpleTail, stop, EStateM.run, bind, EStateM.bind, call] using
          (SimpleRun.failed (rest := rest) stop call)
      | ok value retained =>
        simp only [EStateM.run] at call
        simpa [runSimpleTail, stop, EStateM.run, bind, EStateM.bind, call] using
          (SimpleRun.next stop call (ih (policy.step value acc) retained))

theorem runSimpleTail_iff {Receiver Item Acc Result State Error : Type}
    (policy : SimplePolicy Item Acc Result) (receiver : Receiver) (acc : Acc)
    (methods : List (Receiver → EStateM Error State Item)) (state : State) (outcome : EStateM.Result Error State Acc) :
    (runSimpleTail policy receiver acc methods).run state = outcome ↔
      SimpleRun policy receiver acc methods state outcome :=
  ⟨fun same => same ▸ SimpleRun.complete policy receiver acc methods state, SimpleRun.sound⟩

/-- The first item always runs, even if `stop empty` is true. Its failure
retains its own state and executes neither the tail nor `finish`. -/
theorem simpleEffective_first_error {Receiver State Error : Type}
    (policy : SimplePolicy Item Acc Result) (receiver : Receiver)
    (first : Receiver → EStateM Error State Item) (rest : List (Receiver → EStateM Error State Item))
    (state retained : State) (error : Error) (failed : (first receiver).run state = .error error retained) :
    (simpleEffective policy { items := first :: rest } receiver).run state = .error error retained := by
  simp only [EStateM.run] at failed
  simp [simpleEffective, callChain, EStateM.run, bind, EStateM.bind, failed]

/-- Successful first execution enters the operational tail with the actual
returned state. `finish` changes only successful values, never error states. -/
theorem simpleEffective_tail {Receiver State Error : Type}
    (policy : SimplePolicy Item Acc Result) (receiver : Receiver)
    (first : Receiver → EStateM Error State Item) (rest : List (Receiver → EStateM Error State Item))
    (state retained : State) (value : Item) (outcome : EStateM.Result Error State Acc)
    (called : (first receiver).run state = .ok value retained)
    (tail : SimpleRun policy receiver (policy.first value) rest retained outcome) :
    (simpleEffective policy { items := first :: rest } receiver).run state =
      (match outcome with | .ok acc final => .ok (policy.finish acc) final | .error error final => .error error final) := by
  have evaluated := tail.sound
  simp only [EStateM.run] at called evaluated
  cases outcome <;> simp [simpleEffective, callChain, EStateM.run, bind, EStateM.bind, called, evaluated, pure, EStateM.pure]

theorem runSimpleTail_pure (policy : SimplePolicy Item Acc Result) (acc : Acc) (values : List Item) :
    runSimpleTail policy () acc (values.map (fun value _ => (pure value : Id Item))) =
      policy.reduceTail acc values := by
  induction values generalizing acc with
  | nil => rfl
  | cons value rest ih =>
    simp only [List.map_cons, runSimpleTail, SimplePolicy.reduceTail]
    cases stop : policy.stop acc with
    | true => rfl
    | false => exact ih (policy.step value acc)

theorem simpleEffective_pure (policy : SimplePolicy Item Acc Result) (values : List Item) :
    simpleEffective policy { items := values.map (fun value (_ : Unit) => (pure value : Id Item)) } () =
      policy.reduce values := by
  cases values with
  | nil => rfl
  | cons value rest =>
    change policy.finish (runSimpleTail policy () (policy.first value) (rest.map (fun value _ => (pure value : Id Item)))) = _
    rw [runSimpleTail_pure]
    rfl

theorem SimplePolicy.reduceTail_foldl (policy : SimplePolicy Item Acc Result)
    (never : ∀ acc, policy.stop acc = false) (values : List Item) (acc : Acc) :
    policy.reduceTail acc values = values.foldl (fun acc value => policy.step value acc) acc := by
  induction values generalizing acc with
  | nil => rfl
  | cons value rest ih => simpa [SimplePolicy.reduceTail, never, List.foldl] using ih (policy.step value acc)

theorem SimplePolicy.reduce_foldl (policy : SimplePolicy Item Acc Result)
    (never : ∀ acc, policy.stop acc = false)
    (first : ∀ value, policy.first value = policy.step value policy.empty) (values : List Item) :
    policy.reduce values = policy.finish (values.foldl (fun acc value => policy.step value acc) policy.empty) := by
  cases values with
  | nil => rfl
  | cons value rest =>
    unfold SimplePolicy.reduce
    dsimp only
    rw [SimplePolicy.reduceTail_foldl policy never, first]
    rfl

theorem SimplePolicy.append_order (values : List (List Item)) :
    (SimplePolicy.append Item).reduce values = values.foldl (· ++ ·) [] :=
  SimplePolicy.reduce_foldl _ (fun _ => rfl) (fun _ => rfl) values

theorem SimplePolicy.append_flatten (values : List (List Item)) :
    (SimplePolicy.append Item).reduce values = values.flatten := by
  rw [SimplePolicy.append_order]
  simpa using (List.foldl_append_eq_append (l := values) (f := id) (l' := []))

theorem SimplePolicy.maximum_values [Max Item] (values : List Item) :
    (SimplePolicy.maximum Item).reduce values = values.foldl
      (fun best value => some (best.map (max · value) |>.getD value)) none :=
  SimplePolicy.reduce_foldl _ (fun _ => rfl) (fun _ => rfl) values

theorem SimplePolicy.minimum_values [Min Item] (values : List Item) :
    (SimplePolicy.minimum Item).reduce values = values.foldl
      (fun best value => some (best.map (min · value) |>.getD value)) none :=
  SimplePolicy.reduce_foldl _ (fun _ => rfl) (fun _ => rfl) values

private theorem maximum_tail_bounds (values : List Nat) (start : Nat) :
    ∃ best, (SimplePolicy.maximum Nat).reduceTail (some start) values = some best ∧
      start ≤ best ∧ ∀ value ∈ values, value ≤ best := by
  induction values generalizing start with
  | nil => exact ⟨start, rfl, Nat.le_refl _, by simp⟩
  | cons value rest ih =>
    change ∃ best, (SimplePolicy.maximum Nat).reduceTail (some (max start value)) rest = some best ∧
      start ≤ best ∧ ∀ item ∈ value :: rest, item ≤ best
    obtain ⟨best, evaluated, bound, remaining⟩ := ih (max start value)
    refine ⟨best, evaluated, Nat.le_trans (Nat.le_max_left _ _) bound, ?_⟩
    intro item member
    rcases List.mem_cons.mp member with same | member
    · subst item; exact Nat.le_trans (Nat.le_max_right _ _) bound
    · exact remaining item member

theorem SimplePolicy.maximum_nat_bounds (first : Nat) (rest : List Nat) :
    ∃ best, (SimplePolicy.maximum Nat).reduce (first :: rest) = some best ∧
      ∀ value ∈ first :: rest, value ≤ best := by
  obtain ⟨best, evaluated, bound, remaining⟩ := maximum_tail_bounds rest first
  refine ⟨best, evaluated, ?_⟩
  intro value member
  rcases List.mem_cons.mp member with same | member
  · subst value; exact bound
  · exact remaining value member

private theorem minimum_tail_bounds (values : List Nat) (start : Nat) :
    ∃ best, (SimplePolicy.minimum Nat).reduceTail (some start) values = some best ∧
      best ≤ start ∧ ∀ value ∈ values, best ≤ value := by
  induction values generalizing start with
  | nil => exact ⟨start, rfl, Nat.le_refl _, by simp⟩
  | cons value rest ih =>
    change ∃ best, (SimplePolicy.minimum Nat).reduceTail (some (min start value)) rest = some best ∧
      best ≤ start ∧ ∀ item ∈ value :: rest, best ≤ item
    obtain ⟨best, evaluated, bound, remaining⟩ := ih (min start value)
    refine ⟨best, evaluated, Nat.le_trans bound (Nat.min_le_left _ _), ?_⟩
    intro item member
    rcases List.mem_cons.mp member with same | member
    · subst item; exact Nat.le_trans bound (Nat.min_le_right _ _)
    · exact remaining item member

theorem SimplePolicy.minimum_nat_bounds (first : Nat) (rest : List Nat) :
    ∃ best, (SimplePolicy.minimum Nat).reduce (first :: rest) = some best ∧
      ∀ value ∈ first :: rest, best ≤ value := by
  obtain ⟨best, evaluated, bound, remaining⟩ := minimum_tail_bounds rest first
  refine ⟨best, evaluated, ?_⟩
  intro value member
  rcases List.mem_cons.mp member with same | member
  · subst value; exact bound
  · exact remaining value member

private theorem last_tail (acc : Option Item) (values : List Item) :
    (SimplePolicy.last Item).reduceTail acc values = values.getLast?.or acc := by
  induction values generalizing acc with
  | nil => rfl
  | cons value rest ih =>
    change (SimplePolicy.last Item).reduceTail (some value) rest = (value :: rest).getLast?.or acc
    rw [ih]
    cases rest with
    | nil => rfl
    | cons head tail =>
      simp only [List.getLast?_cons_cons]
      cases found : (head :: tail).getLast? with
      | none => simp at found
      | some last => rfl

theorem SimplePolicy.last_values (values : List Item) :
    (SimplePolicy.last Item).reduce values = values.getLast? := by
  cases values with
  | nil => rfl
  | cons value rest =>
    change (SimplePolicy.last Item).reduceTail (some value) rest = (value :: rest).getLast?
    rw [last_tail]
    cases rest with
    | nil => rfl
    | cons head tail =>
      simp only [List.getLast?_cons_cons]
      cases found : (head :: tail).getLast? with
      | none => simp at found
      | some last => rfl

theorem SimplePolicy.sum_nat (values : List Nat) :
    (SimplePolicy.sum Nat).reduce values = values.foldl (· + ·) 0 := by
  cases values with
  | nil => rfl
  | cons value rest =>
    simp only [SimplePolicy.reduce, SimplePolicy.sum, id_eq, List.foldl_cons, Nat.zero_add]
    exact SimplePolicy.reduceTail_foldl _ (fun _ => rfl) _ _

private theorem collect_tail (acc values : List Item) :
    (SimplePolicy.collect Item).reduceTail acc values = values.reverse ++ acc := by
  induction values generalizing acc with
  | nil => rfl
  | cons value rest ih => 
    change (SimplePolicy.collect Item).reduceTail (value :: acc) rest = (value :: rest).reverse ++ acc
    rw [ih]
    simp [List.reverse_cons, List.append_assoc]

theorem SimplePolicy.collect_order (values : List Item) :
    (SimplePolicy.collect Item).reduce values = values := by
  cases values with
  | nil => rfl
  | cons value rest => 
    change ((SimplePolicy.collect Item).reduceTail [value] rest).reverse = value :: rest
    rw [collect_tail]
    simp [List.reverse_append]

private theorem all_tail (acc : Bool) (values : List Bool) :
    SimplePolicy.all.reduceTail acc values = (acc && values.all id) := by
  induction values generalizing acc with
  | nil => cases acc <;> rfl
  | cons value rest ih => 
    change (if !acc then acc else SimplePolicy.all.reduceTail (acc && value) rest) = (acc && (value :: rest).all id)
    cases acc <;> cases value <;> simp [ih]

theorem SimplePolicy.all_values (values : List Bool) :
    SimplePolicy.all.reduce values = values.all id := by
  cases values with
  | nil => rfl
  | cons value rest => 
    change SimplePolicy.all.reduceTail value rest = (value && rest.all id)
    exact all_tail value rest

private theorem any_tail (acc : Bool) (values : List Bool) :
    SimplePolicy.any.reduceTail acc values = (acc || values.any id) := by
  induction values generalizing acc with
  | nil => cases acc <;> rfl
  | cons value rest ih => 
    change (if acc then acc else SimplePolicy.any.reduceTail (acc || value) rest) = (acc || (value :: rest).any id)
    cases acc <;> cases value <;> simp [ih]

theorem SimplePolicy.any_values (values : List Bool) :
    SimplePolicy.any.reduce values = values.any id := by
  cases values with
  | nil => rfl
  | cons value rest => 
    change SimplePolicy.any.reduceTail value rest = (value || rest.any id)
    exact any_tail value rest

end LeanPoo.Object.MethodCombination
