import LeanPoo.Functional.ClosureCosts

/-! Local queue decisions preserve the exact flattened work order. Prices apply
to scheduling primitives only and are explicit backend premises. -/
namespace LeanPoo.Functional.HybridClosure
open PositiveEquations IncrementalClosure ChunkedClosure

structure Prices where
  copy : Nat
  suspend : Nat
  resume : Nat
  deriving Repr

def balanced : Prices := ⟨1,4,4⟩

structure Work where
  copied : Nat := 0
  frames : Nat := 0
  empty : Nat := 0
  shared : Nat := 0
  inlined : Nat := 0
  deriving Repr

def Work.add (a b : Work) : Work :=
  ⟨a.copied+b.copied,a.frames+b.frames,a.empty+b.empty,a.shared+b.shared,a.inlined+b.inlined⟩

def Work.fee (prices : Prices) (work : Work) := prices.copy*work.copied+(prices.suspend+prices.resume)*work.frames

def useCopy (prices : Prices) (degree : Nat) : Bool := degree*prices.copy ≤ prices.suspend+prices.resume

private def scheduleAt (prices : Prices) (degree : Nat) (watchers : List (Fin n)) (tail : Cursor n) : Cursor n × Work :=
  if watchers.isEmpty then (tail,{empty := 1})
  else if tail.current.isEmpty then (⟨watchers,tail.suspended⟩,{shared := 1})
  else if useCopy prices degree then
    (⟨watchers ++ tail.current,tail.suspended⟩,{copied := degree,inlined := 1})
  else (⟨watchers,tail.current :: tail.suspended⟩,{frames := 1})

def schedule (prices : Prices) (watchers : List (Fin n)) (tail : Cursor n) :=
  scheduleAt prices watchers.length watchers tail

theorem schedule_queue (prices : Prices) (watchers : List (Fin n)) (tail : Cursor n) :
    (schedule prices watchers tail).1.queue = watchers ++ tail.queue := by
  unfold schedule scheduleAt
  split
  · cases watchers <;> simp_all [Cursor.queue]
  · split
    · cases current : tail.current <;> simp_all [Cursor.queue]
    · split <;> simp [Cursor.queue,List.flatten_cons,List.append_assoc]

/-- Selected fee is below both copy-all and suspend/resume alternatives.
Empty/tail-sharing shortcuts have zero modeled scheduling allocation/control fee.
Common per-transition dispatch is outside this differential fee. -/
theorem local_minimum (prices : Prices) (watchers : List (Fin n)) (tail : Cursor n) :
    (schedule prices watchers tail).2.fee prices ≤ watchers.length*prices.copy ∧
    (schedule prices watchers tail).2.fee prices ≤ prices.suspend+prices.resume := by
  unfold schedule scheduleAt
  split <;> (try split) <;> (try split) <;>
    simp_all [Work.fee,useCopy,Nat.mul_comm] <;> omega

theorem local_pairs (prices : Prices) (watchers : List (Fin n)) (tail : Cursor n) :
    (schedule prices watchers tail).2.copied + (schedule prices watchers tail).2.frames ≤ watchers.length := by
  unfold schedule scheduleAt
  split
  · simp
  · have positive : 0 < watchers.length := by cases watchers <;> simp_all
    split <;> (try split) <;> simp_all <;> omega

structure Run (n : Nat) where
  store : Store n
  stats : Stats
  work : Work

def Run.core (result : Run n) := (result.store,result.stats)

def execute (fuel : Nat) (prices : Prices) (plan : Plan n) (store : Store n) (cursor : Cursor n)
    (stats : Stats) (work : Work) : Run n :=
  match fuel with
  | 0 => ⟨store,stats,work⟩
  | fuel+1 =>
    match next cursor.current cursor.suspended with
    | none => ⟨store,stats,work⟩
    | some (index,tail) =>
      let stats := {stats with pops := stats.pops+1}
      if values store index then execute fuel prices plan store tail stats work else
        let evaluated := evalCost store plan.equations[index.val]
        let stats := {stats with evaluations := stats.evaluations+1,nodes := stats.nodes+evaluated.2}
        if evaluated.1 then
          let degree := plan.degree index
          let scheduled := scheduleAt prices degree plan.watches[index.val] tail
          execute fuel prices plan (store.set index.val true index.isLt) scheduled.1
            {stats with writes := stats.writes+1,pushes := stats.pushes+degree} (work.add scheduled.2)
        else execute fuel prices plan store tail stats work

theorem execute_refines (fuel : Nat) (prices : Prices) (plan : Plan n) (store : Store n) (cursor : Cursor n)
    (stats : Stats) (work : Work) :
    (execute fuel prices plan store cursor stats work).core = IncrementalClosure.execute fuel plan store cursor.queue stats := by
  induction fuel generalizing store cursor stats work with
  | zero => rfl
  | succ fuel ih =>
    have queue := next_queue cursor.current cursor.suspended
    cases found : next cursor.current cursor.suspended with
    | none =>
      simp only [found] at queue
      simp [execute,found,IncrementalClosure.execute,Cursor.queue,queue,Run.core]
    | some entry =>
      rcases entry with ⟨index,tail⟩
      simp only [found] at queue
      change cursor.queue = index :: tail.queue at queue
      simp only [execute,found,queue,IncrementalClosure.execute,appendWatchers_eq]
      split
      · exact ih _ _ _ _
      · split
        · rw [ih]
          have scheduled := schedule_queue prices plan.watches[index.val] tail
          change (scheduleAt prices (plan.degree index) plan.watches[index.val] tail).1.queue = _ at scheduled
          rw [scheduled]
        · exact ih _ _ _ _

/-- Potential-style accounting avoids subtraction and covers arbitrary initial
counters. Differential scheduling fee is bounded by either fixed strategy;
requested pair cells never exceed append's actual scheduled edge count. -/
theorem execute_bounds (fuel : Nat) (prices : Prices) (plan : Plan n) (store : Store n) (cursor : Cursor n)
    (stats : Stats) (work : Work) :
    let result := execute fuel prices plan store cursor stats work
    result.work.fee prices + prices.copy*stats.pushes ≤ work.fee prices+prices.copy*result.stats.pushes ∧
    result.work.fee prices + (prices.suspend+prices.resume)*stats.writes ≤
      work.fee prices+(prices.suspend+prices.resume)*result.stats.writes ∧
    result.work.copied+result.work.frames+stats.pushes ≤ work.copied+work.frames+result.stats.pushes := by
  induction fuel generalizing store cursor stats work with
  | zero => simp [execute]
  | succ fuel ih =>
    cases found : next cursor.current cursor.suspended with
    | none => simp [execute,found]
    | some entry =>
      rcases entry with ⟨index,tail⟩
      simp only [execute,found]
      split
      · exact ih store tail {stats with pops := stats.pops+1} work
      · split
        · have bound := ih (store.set index.val true index.isLt)
            (schedule prices plan.watches[index.val] tail).1
            {stats with
              pops := stats.pops+1
              evaluations := stats.evaluations+1
              nodes := stats.nodes+(evalCost store plan.equations[index.val]).2
              writes := stats.writes+1
              pushes := stats.pushes+plan.degree index}
            (work.add (schedule prices plan.watches[index.val] tail).2)
          have selected := local_minimum prices plan.watches[index.val] tail
          have pairs := local_pairs prices plan.watches[index.val] tail
          dsimp only at bound ⊢
          simp only [Work.fee,Work.add,Nat.mul_add] at bound selected ⊢
          have degree : prices.copy*plan.degree index = plan.watches[index.val].length*prices.copy := by
            simp [Plan.degree,Nat.mul_comm]
          simp only [schedule] at bound selected pairs
          unfold Plan.degree at bound ⊢
          rw [Nat.mul_comm plan.watches[index.val].length] at selected
          omega
        · exact ih store tail {stats with
            pops := stats.pops+1
            evaluations := stats.evaluations+1
            nodes := stats.nodes+(evalCost store plan.equations[index.val]).2} work

theorem schedule_frame (prices : Prices) (watchers : List (Fin n)) (tail : Cursor n) :
    (schedule prices watchers tail).2.frames ≤ 1 := by
  unfold schedule scheduleAt
  split <;> (try split) <;> (try split) <;> simp

theorem execute_frames (fuel : Nat) (prices : Prices) (plan : Plan n) (store : Store n) (cursor : Cursor n)
    (stats : Stats) (work : Work) :
    (execute fuel prices plan store cursor stats work).work.frames+stats.writes ≤
      work.frames+(execute fuel prices plan store cursor stats work).stats.writes := by
  induction fuel generalizing store cursor stats work with
  | zero => simp [execute]
  | succ fuel ih =>
    cases found : next cursor.current cursor.suspended with
    | none => simp [execute,found]
    | some entry =>
      rcases entry with ⟨index,tail⟩
      simp only [execute,found]
      split
      · exact ih store tail {stats with pops := stats.pops+1} work
      · split
        · have bound := ih (store.set index.val true index.isLt)
            (schedule prices plan.watches[index.val] tail).1
            {stats with
              pops := stats.pops+1
              evaluations := stats.evaluations+1
              nodes := stats.nodes+(evalCost store plan.equations[index.val]).2
              writes := stats.writes+1
              pushes := stats.pushes+plan.degree index}
            (work.add (schedule prices plan.watches[index.val] tail).2)
          have selected := schedule_frame prices plan.watches[index.val] tail
          dsimp only [Work.add] at bound ⊢
          simp only [schedule] at bound selected
          unfold Plan.degree at bound ⊢
          omega
        · exact ih store tail {stats with
            pops := stats.pops+1
            evaluations := stats.evaluations+1
            nodes := stats.nodes+(evalCost store plan.equations[index.val]).2} work

/-- Exact sum of selected selected scheduling fees and copies/frames is collected
by the actual loop, with no reference evaluator in the runtime path. -/
def measured (prices : Prices) (plan : Plan n) : Run n :=
  execute (n+plan.edgeCount) prices plan (Vector.replicate n false) ⟨List.ofFn id,[]⟩ {} {}

theorem measured_bounds (prices : Prices) (plan : Plan n) :
    (measured prices plan).work.fee prices ≤ prices.copy*(measured prices plan).stats.pushes ∧
    (measured prices plan).work.fee prices ≤ (prices.suspend+prices.resume)*(measured prices plan).stats.writes ∧
    (measured prices plan).work.copied+(measured prices plan).work.frames ≤ (measured prices plan).stats.pushes := by
  simpa [measured,Work.fee] using
    execute_bounds (n+plan.edgeCount) prices plan (Vector.replicate n false) ⟨List.ofFn id,[]⟩ {} {}


/-- Each false fact carries its own possible scheduling fee, including a
per-write decision charge. Credit is consumed once when that fact becomes true. -/
def nodeFee (prices : Prices) (decision degree : Nat) :=
  decision + min (degree*prices.copy) (prices.suspend+prices.resume)

theorem execute_credit (fuel : Nat) (prices : Prices) (decision : Nat) (plan : Plan n)
    (store : Store n) (cursor : Cursor n) (stats : Stats) (work : Work) :
    let result := execute fuel prices plan store cursor stats work
    result.work.fee prices + decision*result.stats.writes ≤
      work.fee prices+decision*stats.writes+credit (fun index => nodeFee prices decision (plan.degree index)) (values store) := by
  induction fuel generalizing store cursor stats work with
  | zero => simp [execute]
  | succ fuel ih =>
    cases found : next cursor.current cursor.suspended with
    | none => simp [execute,found]
    | some entry =>
      rcases entry with ⟨index,tail⟩
      simp only [execute,found]
      split
      · exact ih store tail {stats with pops := stats.pops+1} work
      · rename_i absent
        have absent' : values store index = false := by cases h : values store index <;> simp_all
        split
        · have bound := ih (store.set index.val true index.isLt)
            (schedule prices plan.watches[index.val] tail).1
            {stats with
              pops := stats.pops+1
              evaluations := stats.evaluations+1
              nodes := stats.nodes+(evalCost store plan.equations[index.val]).2
              writes := stats.writes+1
              pushes := stats.pushes+plan.degree index}
            (work.add (schedule prices plan.watches[index.val] tail).2)
          have selected := local_minimum prices plan.watches[index.val] tail
          have spent := credit_set (fun index => nodeFee prices decision (plan.degree index)) (values store) index absent'
          rw [← values_set] at spent
          dsimp only at bound ⊢
          simp only [Work.fee,Work.add,Nat.mul_add,Nat.mul_succ] at bound selected ⊢
          simp only [nodeFee,Plan.degree] at spent
          simp only [schedule,Plan.degree] at bound selected ⊢
          simp only [nodeFee,Nat.mul_comm] at bound selected spent ⊢
          omega
        · exact ih store tail {stats with
            pops := stats.pops+1
            evaluations := stats.evaluations+1
            nodes := stats.nodes+(evalCost store plan.equations[index.val]).2} work

theorem measured_credit (prices : Prices) (decision : Nat) (plan : Plan n) :
    (measured prices plan).work.fee prices + decision*(measured prices plan).stats.writes ≤
      (List.ofFn (fun index => nodeFee prices decision (plan.degree index))).sum := by
  have bound := execute_credit (n+plan.edgeCount) prices decision plan (Vector.replicate n false) ⟨List.ofFn id,[]⟩ {} {}
  simpa [measured,Work.fee,credit,values,total_eq_list] using bound

theorem measured_core (prices : Prices) (plan : Plan n) :
    (measured prices plan).core = ((fastClose plan).store,(fastClose plan).stats) := by
  simpa [measured,Cursor.queue,fastClose] using
    execute_refines (n+plan.edgeCount) prices plan (Vector.replicate n false) ⟨List.ofFn id,[]⟩ {} {}

def close (prices : Prices) (plan : Plan n) : Result plan (Vector.replicate n false) (List.ofFn id) :=
  let actual := measured prices plan
  have same := measured_core prices plan
  {store := actual.store
   fixed := by rw [show actual.store = (fastClose plan).store from congrArg Prod.fst same]; exact (fastClose plan).fixed
   least := by rw [show actual.store = (fastClose plan).store from congrArg Prod.fst same]; exact (fastClose plan).least
   stats := actual.stats
   queue_balance := by rw [show actual.stats = (fastClose plan).stats from congrArg Prod.snd same]; exact (fastClose plan).queue_balance
   pushes_bound := by rw [show actual.stats = (fastClose plan).stats from congrArg Prod.snd same]; exact (fastClose plan).pushes_bound
   evaluations_bound := by rw [show actual.stats = (fastClose plan).stats from congrArg Prod.snd same]; exact (fastClose plan).evaluations_bound
   writes_bound := by rw [show actual.stats = (fastClose plan).stats from congrArg Prod.snd same]; exact (fastClose plan).writes_bound
   nodes_bound := by rw [show actual.stats = (fastClose plan).stats from congrArg Prod.snd same]; exact (fastClose plan).nodes_bound}

theorem canonical (prices : Prices) (plan : Plan n) :
    values (close prices plan).store = (PositiveEquations.close plan.source).value := by
  have same := congrArg Prod.fst (measured_core prices plan)
  change values (measured prices plan).store = _
  change (measured prices plan).store = (fastClose plan).store at same
  rw [same]; exact fast_canonical plan
theorem allocation_bound (prices : Prices) (plan : Plan n) :
    (measured prices plan).work.copied+(measured prices plan).work.frames ≤ plan.edgeCount := by
  have selected := (measured_bounds prices plan).2.2
  have caps := ClosureCosts.actual_ceiling plan
  rw [ChunkedClosure.close_stats] at caps
  have same := congrArg Prod.snd (measured_core prices plan)
  change (measured prices plan).stats = (fastClose plan).stats at same
  rw [same] at selected
  exact Nat.le_trans selected caps.pushes

theorem balanced_allocation (plan : Plan n) :
    (measured balanced plan).work.copied+(measured balanced plan).work.frames ≤ min plan.edgeCount (8*n) := by
  have selected := (measured_bounds balanced plan).2.1
  have caps := ClosureCosts.actual_ceiling plan
  rw [ChunkedClosure.close_stats] at caps
  have same := congrArg Prod.snd (measured_core balanced plan)
  change (measured balanced plan).stats = (fastClose plan).stats at same
  rw [← same] at caps
  simp only [balanced] at selected caps ⊢
  have writes := caps.writes
  simp only [ClosureCosts.ceiling] at writes
  simp only [Work.fee,Nat.one_mul] at selected
  exact Nat.le_min.mpr ⟨allocation_bound balanced plan,by omega⟩

theorem fee_bound (prices : Prices) (plan : Plan n) :
    (measured prices plan).work.fee prices ≤ min (prices.copy*plan.edgeCount) ((prices.suspend+prices.resume)*n) := by
  have selected := measured_bounds prices plan
  have caps := ClosureCosts.actual_ceiling plan
  rw [ChunkedClosure.close_stats] at caps
  have same := congrArg Prod.snd (measured_core prices plan)
  change (measured prices plan).stats = (fastClose plan).stats at same
  rw [← same] at caps
  exact Nat.le_min.mpr ⟨Nat.le_trans selected.1 (Nat.mul_le_mul_left _ caps.pushes),
    Nat.le_trans selected.2.1 (Nat.mul_le_mul_left _ caps.writes)⟩

theorem frame_bound (prices : Prices) (plan : Plan n) : (measured prices plan).work.frames ≤ n := by
  have selected := execute_frames (n+plan.edgeCount) prices plan (Vector.replicate n false) ⟨List.ofFn id,[]⟩ {} {}
  have caps := ClosureCosts.actual_ceiling plan
  rw [ChunkedClosure.close_stats] at caps
  have same := congrArg Prod.snd (measured_core prices plan)
  change (measured prices plan).stats = (fastClose plan).stats at same
  rw [← same] at caps
  change (measured prices plan).work.frames+0 ≤ 0+(measured prices plan).stats.writes at selected
  exact Nat.le_trans (by simpa using selected) caps.writes

/-- Requested words for an owned-byte, scalar-return solve and its private
publication snapshot. Setup, allocator metadata and instrumentation are separate. -/
def solveWords (layout : ClosureCosts.Layout) (snapshot : Bool) (n : Nat) (work : Work) :=
  layout.pairWords*(n+work.copied+work.frames) +
    (if snapshot then layout.bytesHeader+layout.byteWords n else 0)

theorem owned_allocation (prices : Prices) (plan : Plan n) (layout : ClosureCosts.Layout) (snapshot : Bool) :
    solveWords layout snapshot n (measured prices plan).work ≤
      layout.pairWords*(n+plan.edgeCount) + (if snapshot then layout.bytesHeader+layout.byteWords n else 0) := by
  apply Nat.add_le_add_right
  apply Nat.mul_le_mul_left
  have bound := allocation_bound prices plan
  omega

theorem balanced_words (plan : Plan n) (layout : ClosureCosts.Layout) (snapshot : Bool) :
    solveWords layout snapshot n (measured balanced plan).work ≤
      layout.pairWords*(n+min plan.edgeCount (8*n)) + (if snapshot then layout.bytesHeader+layout.byteWords n else 0) := by
  apply Nat.add_le_add_right
  apply Nat.mul_le_mul_left
  have bound := balanced_allocation plan
  omega

def assembleWith (prices : Prices) (equations : Equations n) (plan : Plan n) (source : plan.source = equations) :
    ConstructionCache.Cache (declaration equations) × Stats :=
  let result := close prices plan
  ({closed := ⟨raw (values result.store),by
      rw [GeneralizedGraph.Declaration.step_eq]
      funext index
      rw [PositiveEquations.resolve]
      have fixed : step equations (values result.store) = values result.store := by rw [← source]; exact result.fixed
      exact congrArg (fun value : Bool => some (Except.ok (ε := ComputationError (Fin n)) value)) (congrFun fixed index)⟩
    evaluated := []
    reused := []},result.stats)

def assemble (equations : Equations n) (plan : Plan n) (source : plan.source = equations) := assembleWith balanced equations plan source

theorem assemble_canonical (equations : Equations n) (plan : Plan n) (source : plan.source = equations) :
    (assemble equations plan source).1.closed.raw = raw (PositiveEquations.close equations).value := by
  change raw (values (close balanced plan).store) = _
  rw [canonical,source]

theorem assemble_pop_bound (equations : Equations n) (plan : Plan n) (source : plan.source = equations) :
    (assemble equations plan source).2.pops ≤ n+total plan.degree := by
  change (measured balanced plan).stats.pops ≤ _
  have same := congrArg Prod.snd (measured_core balanced plan)
  change (measured balanced plan).stats = (fastClose plan).stats at same
  rw [same]; exact fast_pop_bound plan

end LeanPoo.Functional.HybridClosure
