import LeanPoo.Functional.IncrementalClosure

/-! Allocation-oriented worklist refinement. Immutable watcher lists are shared;
a transition suspends one current tail instead of copying all outgoing edges. -/
namespace LeanPoo.Functional.ChunkedClosure
open PositiveEquations IncrementalClosure

structure Cursor (n : Nat) where
  current : List (Fin n)
  suspended : List (List (Fin n))

def Cursor.queue (cursor : Cursor n) := cursor.current ++ cursor.suspended.flatten

/-- Logical register return; a Scheme realization uses multiple values. -/
def next : List (Fin n) → List (List (Fin n)) → Option (Fin n × Cursor n)
  | index :: rest, pending => some (index,⟨rest,pending⟩)
  | [], [] => none
  | [], chunk :: pending => next chunk pending

theorem next_queue (current : List (Fin n)) (pending : List (List (Fin n))) :
    match next current pending with
    | none => current ++ pending.flatten = []
    | some (index,cursor) => current ++ pending.flatten = index :: cursor.queue := by
  induction pending generalizing current with
  | nil => cases current <;> rfl
  | cons chunk pending ih =>
    cases current with
    | nil => simpa only [next,List.nil_append,List.flatten_cons] using ih chunk
    | cons index rest => rfl

def execute (fuel : Nat) (plan : Plan n) (store : Store n) (cursor : Cursor n) (stats : Stats) : Store n × Stats :=
  match fuel with
  | 0 => (store,stats)
  | fuel+1 =>
    match next cursor.current cursor.suspended with
    | none => (store,stats)
    | some (index,tail) =>
      let stats := {stats with pops := stats.pops+1}
      if values store index then execute fuel plan store tail stats else
        let evaluated := evalCost store plan.equations[index.val]
        let stats := {stats with evaluations := stats.evaluations+1,nodes := stats.nodes+evaluated.2}
        if evaluated.1 then
          execute fuel plan (store.set index.val true index.isLt)
            ⟨plan.watches[index.val],tail.current :: tail.suspended⟩
            {stats with writes := stats.writes+1,pushes := stats.pushes+plan.degree index}
        else execute fuel plan store tail stats

/-- Every array and every existing work counter is identical to the original
runner. Only the queue representation and its allocation schedule change. -/
theorem execute_refines (fuel : Nat) (plan : Plan n) (store : Store n) (cursor : Cursor n) (stats : Stats) :
    execute fuel plan store cursor stats = IncrementalClosure.execute fuel plan store cursor.queue stats := by
  induction fuel generalizing store cursor stats with
  | zero => rfl
  | succ fuel ih =>
    have queue := next_queue cursor.current cursor.suspended
    cases found : next cursor.current cursor.suspended with
    | none =>
      simp only [found] at queue
      simp [execute,found,IncrementalClosure.execute,Cursor.queue,queue]
    | some entry =>
      rcases entry with ⟨index,tail⟩
      simp only [found] at queue
      change cursor.queue = index :: tail.queue at queue
      simp only [execute,found,queue,IncrementalClosure.execute,appendWatchers_eq]
      split
      · exact ih _ _ _
      · split
        · simpa only [Cursor.queue,List.flatten_cons,List.append_assoc] using
            ih (store.set index.val true index.isLt)
              ⟨plan.watches[index.val],tail.current :: tail.suspended⟩ _
        · exact ih _ _ _

/-- Ghost cost semantics follows exactly the executed branches. One suspension
cons is requested precisely when a fact changes; this is not a Lean heap count. -/
def frameAllocations (fuel : Nat) (plan : Plan n) (store : Store n) (cursor : Cursor n) : Nat :=
  match fuel with
  | 0 => 0
  | fuel+1 =>
    match next cursor.current cursor.suspended with
    | none => 0
    | some (index,tail) =>
      if values store index then frameAllocations fuel plan store tail else
        if (evalCost store plan.equations[index.val]).1 then
          1+frameAllocations fuel plan (store.set index.val true index.isLt)
            ⟨plan.watches[index.val],tail.current :: tail.suspended⟩
        else frameAllocations fuel plan store tail

theorem frameAllocations_writes (fuel : Nat) (plan : Plan n) (store : Store n) (cursor : Cursor n) (stats : Stats) :
    frameAllocations fuel plan store cursor + stats.writes = (execute fuel plan store cursor stats).2.writes := by
  induction fuel generalizing store cursor stats with
  | zero => simp [frameAllocations,execute]
  | succ fuel ih =>
    cases found : next cursor.current cursor.suspended with
    | none => simp [frameAllocations,execute,found]
    | some entry =>
      rcases entry with ⟨index,tail⟩
      simp only [frameAllocations,execute,found]
      split
      · exact ih store tail {stats with pops := stats.pops+1}
      · split
        · have bound := ih (store.set index.val true index.isLt)
            ⟨plan.watches[index.val],tail.current :: tail.suspended⟩
            {stats with
              pops := stats.pops+1
              evaluations := stats.evaluations+1
              nodes := stats.nodes+(evalCost store plan.equations[index.val]).2
              writes := stats.writes+1
              pushes := stats.pushes+plan.degree index}
          dsimp only at bound ⊢
          omega
        · exact ih store tail {stats with
            pops := stats.pops+1
            evaluations := stats.evaluations+1
            nodes := stats.nodes+(evalCost store plan.equations[index.val]).2}

theorem next_suspended (current : List (Fin n)) (pending : List (List (Fin n)))
    (found : next current pending = some (index,tail)) : tail.suspended.length ≤ pending.length := by
  induction pending generalizing current with
  | nil =>
    cases current with
    | nil => contradiction
    | cons head rest =>
      have equal : (head,Cursor.mk rest []) = (index,tail) := Option.some.inj found
      have same := congrArg Prod.snd equal
      change Cursor.mk rest [] = tail at same
      subst tail
      exact Nat.le_refl _
  | cons chunk pending ih =>
    cases current with
    | nil => exact Nat.le_trans (ih chunk found) (by simp)
    | cons head rest => cases found; exact Nat.le_refl _

/-- Maximum reachable suspension depth of the actual transition path. -/
def peakFrames (fuel : Nat) (plan : Plan n) (store : Store n) (cursor : Cursor n) : Nat :=
  match fuel with
  | 0 => cursor.suspended.length
  | fuel+1 =>
    match next cursor.current cursor.suspended with
    | none => cursor.suspended.length
    | some (index,tail) =>
      max cursor.suspended.length
        (if values store index then peakFrames fuel plan store tail else
          if (evalCost store plan.equations[index.val]).1 then
            peakFrames fuel plan (store.set index.val true index.isLt)
              ⟨plan.watches[index.val],tail.current :: tail.suspended⟩
          else peakFrames fuel plan store tail)

theorem peakFrames_bound (fuel : Nat) (plan : Plan n) (store : Store n) (cursor : Cursor n) :
    peakFrames fuel plan store cursor ≤ cursor.suspended.length+frameAllocations fuel plan store cursor := by
  induction fuel generalizing store cursor with
  | zero => simp [peakFrames,frameAllocations]
  | succ fuel ih =>
    cases found : next cursor.current cursor.suspended with
    | none => simp [peakFrames,frameAllocations,found]
    | some entry =>
      rcases entry with ⟨index,tail⟩
      have pending := next_suspended cursor.current cursor.suspended found
      have unchanged := ih store tail
      have changed := ih (store.set index.val true index.isLt)
        ⟨plan.watches[index.val],tail.current :: tail.suspended⟩
      simp only [peakFrames,frameAllocations,found]
      split <;> (try split) <;> dsimp only [List.length_cons] at changed ⊢ <;> omega

/-- Actual production arrays/counters come from the chunked tail runner.
All semantic and operation-bound fields are erased reference transports. -/
def close (plan : Plan n) : Result plan (Vector.replicate n false) (List.ofFn id) :=
  let actual := execute (n+plan.edgeCount) plan (Vector.replicate n false) ⟨List.ofFn id,[]⟩ {}
  have same : actual = ((fastClose plan).store,(fastClose plan).stats) := by
    simpa only [Cursor.queue,List.flatten_nil,List.append_nil,fastClose] using
      execute_refines (n+plan.edgeCount) plan (Vector.replicate n false) ⟨List.ofFn id,[]⟩ {}
  {store := actual.1
   fixed := by rw [congrArg Prod.fst same]; exact (fastClose plan).fixed
   least := by rw [congrArg Prod.fst same]; exact (fastClose plan).least
   stats := actual.2
   queue_balance := by rw [congrArg Prod.snd same]; exact (fastClose plan).queue_balance
   pushes_bound := by rw [congrArg Prod.snd same]; exact (fastClose plan).pushes_bound
   evaluations_bound := by rw [congrArg Prod.snd same]; exact (fastClose plan).evaluations_bound
   writes_bound := by rw [congrArg Prod.snd same]; exact (fastClose plan).writes_bound
   nodes_bound := by rw [congrArg Prod.snd same]; exact (fastClose plan).nodes_bound}

theorem close_store (plan : Plan n) : (close plan).store = (fastClose plan).store := by
  simpa only [close,fastClose,Cursor.queue,List.flatten_nil,List.append_nil] using congrArg Prod.fst (execute_refines (n+plan.edgeCount) plan (Vector.replicate n false) ⟨List.ofFn id,[]⟩ {})

theorem close_stats (plan : Plan n) : (close plan).stats = (fastClose plan).stats := by
  simpa only [close,fastClose,Cursor.queue,List.flatten_nil,List.append_nil] using congrArg Prod.snd (execute_refines (n+plan.edgeCount) plan (Vector.replicate n false) ⟨List.ofFn id,[]⟩ {})

theorem frame_allocation_bound (plan : Plan n) :
    frameAllocations (n+plan.edgeCount) plan (Vector.replicate n false) ⟨List.ofFn id,[]⟩ ≤ n := by
  have equal := frameAllocations_writes (n+plan.edgeCount) plan (Vector.replicate n false) ⟨List.ofFn id,[]⟩ {}
  have bound := (close plan).writes_bound
  change (execute _ _ _ _ _).2.writes ≤ _ at bound
  dsimp only at equal
  omega

theorem peak_frame_bound (plan : Plan n) :
    peakFrames (n+plan.edgeCount) plan (Vector.replicate n false) ⟨List.ofFn id,[]⟩ ≤ n := by
  exact Nat.le_trans (peakFrames_bound _ _ _ _) (by simpa using frame_allocation_bound plan)

def assemble (equations : Equations n) (plan : Plan n) (source : plan.source = equations) :
    ConstructionCache.Cache (declaration equations) × Stats :=
  let result := close plan
  ({closed := ⟨raw (values result.store),by
      rw [GeneralizedGraph.Declaration.step_eq]
      funext index
      rw [PositiveEquations.resolve]
      have fixed : step equations (values result.store) = values result.store := by rw [← source]; exact result.fixed
      exact congrArg (fun value : Bool => some (Except.ok (ε := ComputationError (Fin n)) value)) (congrFun fixed index)⟩
    evaluated := []
    reused := []},result.stats)

theorem assemble_canonical (equations : Equations n) (plan : Plan n) (source : plan.source = equations) :
    (assemble equations plan source).1.closed.raw = raw (PositiveEquations.close equations).value := by
  change raw (values (close plan).store) = _
  rw [close_store,fast_canonical,source]

theorem assemble_pop_bound (equations : Equations n) (plan : Plan n) (source : plan.source = equations) :
    (assemble equations plan source).2.pops ≤ n+total plan.degree := by
  change (close plan).stats.pops ≤ _
  rw [close_stats]; exact fast_pop_bound plan
end LeanPoo.Functional.ChunkedClosure
