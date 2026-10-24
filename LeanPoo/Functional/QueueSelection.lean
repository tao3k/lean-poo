import LeanPoo.Functional.HybridClosure

/-! Compile-time queue ceilings include the hybrid decision overhead. Choosing a
smaller proved ceiling does not predict the fastest machine execution. -/
namespace LeanPoo.Functional.QueueSelection
open PositiveEquations IncrementalClosure

inductive Queue where | append | chunked | hybrid
  deriving BEq, DecidableEq, Repr

structure Profile where
  prices : HybridClosure.Prices
  decision : Nat

/-- Reference relative charges, not hardware calibration. Scaling the existing
hybrid prices by four retains the same per-write degree threshold of eight. -/
def reference : Profile := ⟨⟨4,16,16⟩,1⟩

/-- The existing nonnegative compiler admission dominates both the cached
reference ceiling arithmetic and the old copy-price=1 range check. -/
theorem reference_capacity (n edges maximum limit : Nat)
    (admitted : 16*(1+n+edges+(n+edges)*maximum) ≤ limit) :
    edges ≤ limit ∧ n+4*edges ≤ limit := by omega

theorem reference_threshold (degree : Nat) :
    HybridClosure.useCopy reference.prices degree = HybridClosure.useCopy HybridClosure.balanced degree := by
  have relation : degree*4 ≤ 32 ↔ degree ≤ 8 := by omega
  simp [HybridClosure.useCopy,reference,HybridClosure.balanced,relation]

theorem reference_nodeFee (degree : Nat) :
    HybridClosure.nodeFee reference.prices reference.decision degree = 1+4*min degree 8 := by
  simp only [HybridClosure.nodeFee,reference]
  omega

structure Prepared (profile : Profile) (plan : Plan n) where
  appendCeiling : Nat
  hybridCeiling : Nat
  append_eq : appendCeiling = profile.prices.copy*plan.edgeCount
  hybrid_eq : hybridCeiling = (List.ofFn (fun index => HybridClosure.nodeFee profile.prices profile.decision (plan.degree index))).sum

variable {n : Nat} {profile : Profile} {plan : Plan n}

def prepare (profile : Profile) (plan : Plan n) : Prepared profile plan :=
  ⟨profile.prices.copy*plan.edgeCount,
    (List.ofFn (fun index => HybridClosure.nodeFee profile.prices profile.decision (plan.degree index))).sum,rfl,rfl⟩

def chunkCeiling (profile : Profile) (n : Nat) := (profile.prices.suspend+profile.prices.resume)*n

def Prepared.choose (prepared : Prepared profile plan) : Queue :=
  if prepared.appendCeiling ≤ chunkCeiling profile n ∧ prepared.appendCeiling ≤ prepared.hybridCeiling then .append
  else if chunkCeiling profile n ≤ prepared.hybridCeiling then .chunked else .hybrid

def Prepared.ceiling (prepared : Prepared profile plan) : Queue → Nat
  | .append => prepared.appendCeiling
  | .chunked => chunkCeiling profile n
  | .hybrid => prepared.hybridCeiling

theorem choose_minimum (prepared : Prepared profile plan) (candidate : Queue) :
    prepared.ceiling prepared.choose ≤ prepared.ceiling candidate := by
  unfold Prepared.choose
  split <;> (try split) <;> cases candidate <;> simp_all [Prepared.ceiling] <;> omega

private theorem bounded_sum (degrees : Fin n → Nat) (small : ∀ index, degrees index ≤ 8) :
    total (fun index => HybridClosure.nodeFee reference.prices reference.decision (degrees index)) =
      n+4*total degrees := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [total,reference_nodeFee,Nat.min_eq_left (small 0),ih _ (fun index => small index.succ)]
    simp only [total]
    omega

private theorem bounded_degrees (degrees : Fin n → Nat) (small : ∀ index, degrees index ≤ 8) :
    total degrees ≤ 8*n := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    have head := small 0
    have tail := ih (fun index => degrees index.succ) (fun index => small index.succ)
    simp only [total]
    omega

/-- All narrow topologies avoid per-write hybrid decisions. This applies by
cached metadata alone, independently of source literals or workload names. -/
theorem small_degrees_append (prepared : Prepared reference plan) (small : ∀ index, plan.degree index ≤ 8) :
    prepared.choose = .append := by
  have hybrid : prepared.hybridCeiling = n+4*plan.edgeCount := by
    rw [prepared.hybrid_eq,← total_eq_list,bounded_sum _ small,← plan.edgeCount_eq]
  have density := bounded_degrees plan.degree small
  rw [← plan.edgeCount_eq] at density
  unfold Prepared.choose
  rw [prepared.append_eq,hybrid]
  simp only [reference,chunkCeiling]
  have left : 4*plan.edgeCount ≤ (16+16)*n := by omega
  simp [left]

def Prepared.run (prepared : Prepared profile plan) : HybridClosure.Run n :=
  match prepared.choose with
  | .append => let result := fastClose plan
               ⟨result.store,result.stats,{copied := result.stats.pushes}⟩
  | .chunked => let result := ChunkedClosure.close plan
                ⟨result.store,result.stats,{frames := result.stats.writes}⟩
  | .hybrid => HybridClosure.measured profile.prices plan

/-- Share certified pure append/chunked executions across profiles using standard
memoizing thunks. Hybrid execution retains the current profile's actual prices.
Returned work describes the certified solve, not a measurement of cache-hit costs. -/
def Prepared.runCached (prepared : Prepared profile plan)
    (appended chunked : Thunk (Result plan (Vector.replicate n false) (List.ofFn id)))
    (_append_actual : appended.get = fastClose plan)
    (_chunked_actual : chunked.get = ChunkedClosure.close plan) : HybridClosure.Run n :=
  match prepared.choose with
  | .append => let result := appended.get
               ⟨result.store,result.stats,{copied := result.stats.pushes}⟩
  | .chunked => let result := chunked.get
                ⟨result.store,result.stats,{frames := result.stats.writes}⟩
  | .hybrid => HybridClosure.measured profile.prices plan

/-- Sharing changes evaluation reuse, not any selected store, statistic or work
counter. Supplied thunks require exact execution certificates, not just bounds. -/
theorem Prepared.runCached_eq (prepared : Prepared profile plan)
    (appended chunked : Thunk (Result plan (Vector.replicate n false) (List.ofFn id)))
    (append_actual : appended.get = fastClose plan)
    (chunked_actual : chunked.get = ChunkedClosure.close plan) :
    prepared.runCached appended chunked append_actual chunked_actual = prepared.run := by
  unfold Prepared.runCached Prepared.run
  split <;> simp only [append_actual, chunked_actual]

/-- Compute the differential charge of a supplied run without executing the
solver again. The caller must retain the actual selected run; arbitrary supplied
statistics do not inherit the selected-bound theorem. -/
def Prepared.chargeRun (prepared : Prepared profile plan) (result : HybridClosure.Run n) : Nat :=
  result.work.fee profile.prices +
    if prepared.choose == .hybrid then profile.decision*result.stats.writes else 0

/-- The ordinary cost observation executes the selected solver once. Consumers
that already hold its result can use chargeRun under chargeRun_eq. -/
def Prepared.charge (prepared : Prepared profile plan) : Nat :=
  prepared.chargeRun prepared.run

/-- Reusing the actual selected run preserves the exact original cost judgment;
it is not a claim that arbitrary externally supplied statistics are trustworthy. -/
theorem Prepared.chargeRun_eq (prepared : Prepared profile plan) (result : HybridClosure.Run n)
    (actual : result = prepared.run) : prepared.chargeRun result = prepared.charge := by
  subst result
  rfl

theorem run_core (prepared : Prepared profile plan) :
    prepared.run.core = ((fastClose plan).store,(fastClose plan).stats) := by
  unfold Prepared.run
  split
  · rfl
  · exact Prod.ext (ChunkedClosure.close_store plan) (ChunkedClosure.close_stats plan)
  · exact HybridClosure.measured_core _ _

theorem actual_bound (prepared : Prepared profile plan) :
    prepared.charge ≤ prepared.ceiling prepared.choose := by
  unfold Prepared.charge Prepared.chargeRun Prepared.run
  cases chosen : prepared.choose with
  | append =>
    simp only [Nat.add_zero,HybridClosure.Work.fee,Nat.mul_zero]
    change profile.prices.copy*(fastClose plan).stats.pushes ≤ prepared.appendCeiling
    rw [prepared.append_eq]
    have caps := ClosureCosts.actual_ceiling plan
    rw [ChunkedClosure.close_stats] at caps
    exact Nat.mul_le_mul_left _ caps.pushes
  | chunked =>
    simp only [(show (Queue.chunked == Queue.hybrid) = false from rfl),Bool.false_eq_true,ite_false,HybridClosure.Work.fee,Nat.mul_zero,Nat.zero_add]
    change (profile.prices.suspend+profile.prices.resume)*(ChunkedClosure.close plan).stats.writes+0 ≤ chunkCeiling profile n
    have caps := ClosureCosts.actual_ceiling plan
    simpa [chunkCeiling,ClosureCosts.ceiling] using Nat.mul_le_mul_left (profile.prices.suspend+profile.prices.resume) caps.writes
  | hybrid =>
    change _ ≤ prepared.hybridCeiling
    rw [prepared.hybrid_eq]
    exact HybridClosure.measured_credit _ _ _

/-- The actual selected differential charge is bounded by both candidates'
ceilings, including per-write hybrid decisions. It need not beat actual costs
of a candidate on an unseeded/partially active source. -/
theorem selected_bound (prepared : Prepared profile plan) (candidate : Queue) :
    prepared.charge ≤ prepared.ceiling candidate :=
  Nat.le_trans (actual_bound prepared) (choose_minimum prepared candidate)

theorem allocation_bound (prepared : Prepared profile plan) :
    prepared.run.work.copied+prepared.run.work.frames ≤ max plan.edgeCount n := by
  unfold Prepared.run
  split
  · have caps := ClosureCosts.actual_ceiling plan
    rw [ChunkedClosure.close_stats] at caps
    exact Nat.le_trans (by simpa [ClosureCosts.ceiling] using caps.pushes) (Nat.le_max_left _ _)
  · have caps := ClosureCosts.actual_ceiling plan
    exact Nat.le_trans (by simpa [ClosureCosts.ceiling] using caps.writes) (Nat.le_max_right _ _)
  · exact Nat.le_trans (HybridClosure.allocation_bound _ _) (Nat.le_max_left _ _)

theorem requested_words (prepared : Prepared profile plan) (layout : ClosureCosts.Layout) (snapshot : Bool) :
    HybridClosure.solveWords layout snapshot n prepared.run.work ≤
      layout.pairWords*(n+max plan.edgeCount n) + (if snapshot then layout.bytesHeader+layout.byteWords n else 0) := by
  apply Nat.add_le_add_right
  apply Nat.mul_le_mul_left
  have bound := allocation_bound prepared
  omega

/-- Common preparation charges are explicit and added to every candidate. A
backend must justify the cost of visiting degrees (and any list scans) itself. -/
theorem selected_with_setup (prepared : Prepared profile plan) (setup : Nat) (candidate : Queue) :
    setup+prepared.charge ≤ setup+prepared.ceiling candidate :=
  Nat.add_le_add_left (selected_bound prepared candidate) setup

def Prepared.solve (prepared : Prepared profile plan) : Result plan (Vector.replicate n false) (List.ofFn id) :=
  match prepared.choose with
  | .append => fastClose plan
  | .chunked => ChunkedClosure.close plan
  | .hybrid => HybridClosure.close profile.prices plan

theorem solve_core (prepared : Prepared profile plan) :
    ((prepared.solve).store,(prepared.solve).stats) = prepared.run.core := by
  unfold Prepared.solve Prepared.run
  split <;> rfl

theorem canonical (prepared : Prepared profile plan) :
    values prepared.solve.store = (PositiveEquations.close plan.source).value := by
  have same := congrArg Prod.fst ((solve_core prepared).trans (run_core prepared))
  change prepared.solve.store = (fastClose plan).store at same
  rw [same]; exact fast_canonical plan

/-- Literal-only revision transports both cached ceilings without another
traversal of watcher lists. Changed dependencies need fresh preparation. -/
def Prepared.reconfigure (prepared : Prepared profile plan) (equations : Equations n)
    (same : ∀ index, dependencies (equations index) = dependencies (plan.source index)) :
    Prepared profile (IncrementalClosure.reconfigure plan equations same) :=
  ⟨prepared.appendCeiling,prepared.hybridCeiling,prepared.append_eq,prepared.hybrid_eq⟩

theorem reconfigure_choice (prepared : Prepared profile plan) (equations : Equations n) (same) :
    (prepared.reconfigure equations same).choose = prepared.choose := rfl

/-- Reusing certified ceilings after a literal revision equals fresh preparation. -/
theorem prepare_reconfigure (profile : Profile) (plan : Plan n) (equations : Equations n)
    (same : ∀ index, dependencies (equations index) = dependencies (plan.source index)) :
    (prepare profile plan).reconfigure equations same =
      prepare profile (IncrementalClosure.reconfigure plan equations same) := rfl

private theorem plan_eq_of_tables (left right : Plan n)
    (table : left.equations = right.equations) (index : left.watches = right.watches) : left = right := by
  cases left
  cases right
  cases table
  cases index
  rfl

private theorem compile_index_eq (before after : Equations n)
    (same : ∀ index, dependencies (before index) = dependencies (after index)) :
    (compile before).watches = (compile after).watches := by
  simp only [compile, buildIndex, edges, collectDeps_correct, List.append_nil]
  simp only [Vector.getElem_ofFn, same]

/-- Reusing a canonical index after exact read-footprint preservation is the
same Plan as fresh compilation, including watcher order and multiplicities. -/
theorem reconfigure_compile (before after : Equations n)
    (same : ∀ index, dependencies (after index) = dependencies ((compile before).source index)) :
    IncrementalClosure.reconfigure (compile before) after same = compile after := by
  apply plan_eq_of_tables
  · rfl
  · apply compile_index_eq
    intro index
    simpa only [compile_source] using (same index).symm

def assemble (equations : Equations n) (plan : Plan n) (source : plan.source = equations) :
    ConstructionCache.Cache (declaration equations) × Stats :=
  let result := (prepare reference plan).solve
  ({closed := ⟨raw (values result.store),by
      rw [GeneralizedGraph.Declaration.step_eq]
      funext index
      rw [PositiveEquations.resolve]
      have fixed : step equations (values result.store) = values result.store := by rw [← source]; exact result.fixed
      exact congrArg (fun value : Bool => some (Except.ok (ε := ComputationError (Fin n)) value)) (congrFun fixed index)⟩
    evaluated := [],reused := []},result.stats)

theorem assemble_canonical (equations : Equations n) (plan : Plan n) (source : plan.source = equations) :
    (assemble equations plan source).1.closed.raw = raw (PositiveEquations.close equations).value := by
  change raw (values (prepare reference plan).solve.store) = _
  rw [canonical,source]

theorem assemble_pop_bound (equations : Equations n) (plan : Plan n) (source : plan.source = equations) :
    (assemble equations plan source).2.pops ≤ n+total plan.degree := by
  have same := congrArg Prod.snd ((solve_core (prepare reference plan)).trans (run_core (prepare reference plan)))
  change (prepare reference plan).solve.stats = (fastClose plan).stats at same
  change (prepare reference plan).solve.stats.pops ≤ _
  rw [same]; exact fast_pop_bound plan
end LeanPoo.Functional.QueueSelection
