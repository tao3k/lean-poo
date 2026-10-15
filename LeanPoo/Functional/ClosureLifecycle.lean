import LeanPoo.Functional.QueueSelection

/-! End-to-end finite closure costs: construction, optional selector preparation,
cached budgets, retained-index revision, solve and copied publication. -/
namespace LeanPoo.Functional.ClosureLifecycle
open PositiveEquations IncrementalClosure
abbrev Queue := QueueSelection.Queue

inductive Mode where | cold | adaptive | append | chunked | hybrid
  deriving BEq, DecidableEq, Repr

structure Prepared (plan : Plan n) where
  mode : Mode
  edges : Nat
  edges_eq : edges = plan.edgeCount
  hybridCeiling : Nat
  hybrid_eq : hybridCeiling = if mode = .adaptive then
    (List.ofFn (fun index => HybridClosure.nodeFee QueueSelection.reference.prices 1 (plan.degree index))).sum
    else n+min (4*edges) (32*n)
  reused : Bool := false

variable {n : Nat} {plan : Plan n}

def prepare (mode : Mode) (plan : Plan n) : Prepared plan :=
  let edges := plan.edgeCount
  ⟨mode,edges,rfl,if mode = .adaptive then
    (List.ofFn (fun index => HybridClosure.nodeFee QueueSelection.reference.prices 1 (plan.degree index))).sum
    else n+min (4*edges) (32*n),rfl,false⟩

def Prepared.upgrade (old : Prepared plan) : Prepared plan :=
  {mode := .adaptive,edges := old.edges,edges_eq := old.edges_eq
   hybridCeiling := (List.ofFn (fun index => HybridClosure.nodeFee QueueSelection.reference.prices 1 (plan.degree index))).sum
   hybrid_eq := rfl}

def Prepared.visits (prepared : Prepared plan) :=
  if prepared.mode = .adaptive ∧ prepared.reused = false then n else 0

def Prepared.ceiling (prepared : Prepared plan) : Queue → Nat
  | .append => 4*prepared.edges
  | .chunked => 32*n
  | .hybrid => prepared.hybridCeiling

def Prepared.choose (prepared : Prepared plan) : Queue :=
  match prepared.mode with
  | .append => .append
  | .chunked => .chunked
  | .hybrid => .hybrid
  | .cold => if 4*prepared.edges ≤ 32*n then .append else .chunked
  | .adaptive =>
    if 4*prepared.edges ≤ 32*n ∧ 4*prepared.edges ≤ prepared.hybridCeiling then .append
    else if 32*n ≤ prepared.hybridCeiling then .chunked else .hybrid

def Prepared.run (prepared : Prepared plan) : HybridClosure.Run n :=
  let fuel := n+prepared.edges
  let initial := Vector.replicate n false
  match prepared.choose with
  | .append => let result := IncrementalClosure.execute fuel plan initial (List.ofFn id) {}
               ⟨result.1,result.2,{copied := result.2.pushes}⟩
  | .chunked => let result := ChunkedClosure.execute fuel plan initial ⟨List.ofFn id,[]⟩ {}
                ⟨result.1,result.2,{frames := result.2.writes}⟩
  | .hybrid => HybridClosure.execute fuel QueueSelection.reference.prices plan initial ⟨List.ofFn id,[]⟩ {} {}

theorem run_core (prepared : Prepared plan) :
    prepared.run.core = ((fastClose plan).store,(fastClose plan).stats) := by
  unfold Prepared.run
  rw [prepared.edges_eq]
  split
  · rfl
  · simpa only [HybridClosure.Run.core,fastClose,ChunkedClosure.Cursor.queue,List.flatten_nil,List.append_nil] using
      ChunkedClosure.execute_refines (n+plan.edgeCount) plan (Vector.replicate n false) ⟨List.ofFn id,[]⟩ {}
  · exact HybridClosure.measured_core _ _

theorem run_append (prepared : Prepared plan) (chosen : prepared.choose = .append) :
    prepared.run.work = {copied := (fastClose plan).stats.pushes} := by
  simp only [Prepared.run,chosen,prepared.edges_eq]
  rfl

theorem run_chunked (prepared : Prepared plan) (chosen : prepared.choose = .chunked) :
    prepared.run.work = {frames := (ChunkedClosure.close plan).stats.writes} := by
  simp only [Prepared.run,chosen,prepared.edges_eq]
  rfl

theorem run_hybrid (prepared : Prepared plan) (chosen : prepared.choose = .hybrid) :
    prepared.run = HybridClosure.measured QueueSelection.reference.prices plan := by
  simp only [Prepared.run,chosen,prepared.edges_eq]
  rfl

def Prepared.charge (prepared : Prepared plan) :=
  prepared.run.work.fee QueueSelection.reference.prices +
    (match prepared.choose with | .hybrid => prepared.run.stats.writes | _ => 0)

theorem hybrid_aggregate (plan : Plan n) :
    (HybridClosure.measured QueueSelection.reference.prices plan).work.fee QueueSelection.reference.prices +
      (HybridClosure.measured QueueSelection.reference.prices plan).stats.writes ≤ n+min (4*plan.edgeCount) (32*n) := by
  have fee := HybridClosure.fee_bound QueueSelection.reference.prices plan
  have caps := ClosureCosts.actual_ceiling plan
  rw [ChunkedClosure.close_stats] at caps
  have same := congrArg Prod.snd (HybridClosure.measured_core QueueSelection.reference.prices plan)
  change (HybridClosure.measured QueueSelection.reference.prices plan).stats = (fastClose plan).stats at same
  rw [← same] at caps
  simp only [QueueSelection.reference] at fee caps ⊢
  have writes := caps.writes
  simp only [ClosureCosts.ceiling] at writes
  omega

theorem actual_bound (prepared : Prepared plan) : prepared.charge ≤ prepared.ceiling prepared.choose := by
  have caps := ClosureCosts.actual_ceiling plan
  have stats := congrArg Prod.snd (run_core prepared)
  change prepared.run.stats = (fastClose plan).stats at stats
  cases chosen : prepared.choose with
  | append =>
    unfold Prepared.charge
    rw [run_append prepared chosen]
    simp only [chosen,Nat.add_zero]
    change 4*(fastClose plan).stats.pushes ≤ 4*prepared.edges
    rw [prepared.edges_eq]
    rw [ChunkedClosure.close_stats] at caps
    exact Nat.mul_le_mul_left _ caps.pushes
  | chunked =>
    unfold Prepared.charge
    rw [run_chunked prepared chosen]
    simp only [chosen,Nat.add_zero]
    simp only [HybridClosure.Work.fee,Nat.mul_zero,Nat.zero_add,QueueSelection.reference]
    change 32*(ChunkedClosure.close plan).stats.writes ≤ 32*n
    exact Nat.mul_le_mul_left _ caps.writes
  | hybrid =>
    unfold Prepared.charge
    rw [run_hybrid prepared chosen]
    simp only [chosen]
    change _ ≤ prepared.hybridCeiling
    rw [prepared.hybrid_eq]
    split
    · simpa only [Nat.one_mul] using HybridClosure.measured_credit QueueSelection.reference.prices 1 plan
    · rw [prepared.edges_eq]; exact hybrid_aggregate plan

theorem choose_minimum (prepared : Prepared plan) (automatic : prepared.mode = .cold ∨ prepared.mode = .adaptive)
    (candidate : Queue) : prepared.ceiling prepared.choose ≤ prepared.ceiling candidate := by
  rcases automatic with cold | adaptive
  · have cap := prepared.hybrid_eq
    simp only [cold,Mode.noConfusion,reduceCtorEq,ite_false] at cap
    simp only [Prepared.choose,cold]
    split <;> cases candidate <;> simp_all [Prepared.ceiling] <;> omega
  · simp only [Prepared.choose,adaptive]
    split <;> (try split) <;> cases candidate <;> simp_all [Prepared.ceiling] <;> omega

/-- The cached-budget execution preserves the canonical store. -/
theorem run_store (prepared : Prepared plan) : prepared.run.store = (fastClose plan).store :=
  congrArg Prod.fst (run_core prepared)

/-- Reference computation is proof-only; data uses the cached V+E budget. -/
def Prepared.solve (prepared : Prepared plan) : Result plan (Vector.replicate n false) (List.ofFn id) :=
  let actual := prepared.run
  have same := run_core prepared
  {store := actual.store,stats := actual.stats
   fixed := by rw [show actual.store = (fastClose plan).store from congrArg Prod.fst same]; exact (fastClose plan).fixed
   least := by rw [show actual.store = (fastClose plan).store from congrArg Prod.fst same]; exact (fastClose plan).least
   queue_balance := by rw [show actual.stats = (fastClose plan).stats from congrArg Prod.snd same]; exact (fastClose plan).queue_balance
   pushes_bound := by rw [show actual.stats = (fastClose plan).stats from congrArg Prod.snd same]; exact (fastClose plan).pushes_bound
   evaluations_bound := by rw [show actual.stats = (fastClose plan).stats from congrArg Prod.snd same]; exact (fastClose plan).evaluations_bound
   writes_bound := by rw [show actual.stats = (fastClose plan).stats from congrArg Prod.snd same]; exact (fastClose plan).writes_bound
   nodes_bound := by rw [show actual.stats = (fastClose plan).stats from congrArg Prod.snd same]; exact (fastClose plan).nodes_bound}

theorem canonical (prepared : Prepared plan) :
    values prepared.solve.store = (PositiveEquations.close plan.source).value := by
  have same := congrArg Prod.fst (run_core prepared)
  change prepared.solve.store = (fastClose plan).store at same
  rw [same]; exact fast_canonical plan

/-- A literal/dependency-equal revision shares budget and selector metadata;
new source storage is separate and solving still starts from bottom. -/
def Prepared.reconfigure (old : Prepared plan) (equations : Equations n) (same) :
    Prepared (IncrementalClosure.reconfigure plan equations same) :=
  ⟨old.mode,old.edges,old.edges_eq,old.hybridCeiling,old.hybrid_eq,true⟩

theorem revision_visits (old : Prepared plan) (equations : Equations n) (same) :
    (old.reconfigure equations same).visits = 0 := by simp [Prepared.reconfigure,Prepared.visits]

structure Prices where
  equation : Nat
  node : Nat
  index : Nat
  context : Nat
  visitor : Nat
  degree : Nat
  scan : Nat
  publication : Nat
  pop : Nat := 0
  evaluation : Nat := 0
  descriptor : Nat := 0
  update : Nat := 0
  initialization : Nat := 0
  deriving Repr

/-- Declared source costs. Scheme provides descriptor visits and indexed-edge
counts; native allocation/GC and compiler instruction costs require a backend. -/
def construction (prices : Prices) (n astNodes edges : Nat) (revision : Bool) :=
  prices.equation*n+prices.node*astNodes+prices.context+
    if revision then 0 else prices.index*edges+prices.visitor*n

def preparation (prices : Prices) (prepared : Prepared plan) (cachedDegrees : Bool) :=
  prices.degree*prepared.visits + if cachedDegrees || prepared.visits == 0 then 0 else prices.scan*prepared.edges

/-- Common executed evaluator/store work. A descriptor price covers its tag,
scalar read/join/literal work; a backend supplies conservative primitive prices. -/
def core (prices : Prices) (n : Nat) (stats : Stats) :=
  prices.initialization*n + prices.pop*stats.pops + prices.evaluation*stats.evaluations +
    prices.descriptor*stats.nodes + prices.update*stats.writes

theorem core_bound (prices : Prices) (prepared : Prepared plan) :
    core prices n prepared.run.stats ≤ core prices n (ClosureCosts.ceiling plan) := by
  have same := congrArg Prod.snd (run_core prepared)
  change prepared.run.stats = (fastClose plan).stats at same
  have cap := ClosureCosts.actual_ceiling plan
  rw [ChunkedClosure.close_stats,← same] at cap
  unfold core
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.le_refl _)
    (Nat.mul_le_mul_left _ cap.pops)) (Nat.mul_le_mul_left _ cap.evaluations))
    (Nat.mul_le_mul_left _ cap.nodes)) (Nat.mul_le_mul_left _ cap.writes)

def total (prices : Prices) (prepared : Prepared plan) (astNodes uses : Nat) (revision cachedDegrees : Bool) :=
  construction prices n astNodes prepared.edges revision + preparation prices prepared cachedDegrees +
    uses*(prices.publication*n+core prices n prepared.run.stats+prepared.charge)

theorem total_bound (prices : Prices) (prepared : Prepared plan) (astNodes uses : Nat) (revision cachedDegrees : Bool)
    (automatic : prepared.mode = .cold ∨ prepared.mode = .adaptive) (candidate : Queue) :
    total prices prepared astNodes uses revision cachedDegrees ≤
      construction prices n astNodes prepared.edges revision + preparation prices prepared cachedDegrees +
        uses*(prices.publication*n+core prices n prepared.run.stats+prepared.ceiling candidate) := by
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul_left
  apply Nat.add_le_add_left
  exact Nat.le_trans (actual_bound prepared) (choose_minimum prepared automatic candidate)

theorem total_cost_bound (prices : Prices) (prepared : Prepared plan) (astNodes uses : Nat)
    (revision cachedDegrees : Bool) (automatic : prepared.mode = .cold ∨ prepared.mode = .adaptive)
    (candidate : Queue) :
    total prices prepared astNodes uses revision cachedDegrees ≤
      construction prices n astNodes prepared.edges revision + preparation prices prepared cachedDegrees +
        uses*(prices.publication*n+core prices n (ClosureCosts.ceiling plan)+prepared.ceiling candidate) := by
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul_left
  exact Nat.add_le_add (Nat.add_le_add_left (core_bound prices prepared) _)
    (Nat.le_trans (actual_bound prepared) (choose_minimum prepared automatic candidate))

/-- Comparison with a direct candidate admits the real selector-preparation
surcharge. It is not hidden as a free common term or claimed universally paid back. -/
theorem preparation_regret (prices : Prices) (prepared : Prepared plan) (astNodes uses : Nat) (cachedDegrees : Bool)
    (automatic : prepared.mode = .cold ∨ prepared.mode = .adaptive) (candidate : Queue) :
    total prices prepared astNodes uses false cachedDegrees ≤
      construction prices n astNodes prepared.edges false + uses*(prices.publication*n+core prices n prepared.run.stats+prepared.ceiling candidate) +
        preparation prices prepared cachedDegrees := by
  have bound := total_bound prices prepared astNodes uses false cachedDegrees automatic candidate
  omega

theorem cold_preparation (prices : Prices) (plan : Plan n) (cachedDegrees : Bool) :
    preparation prices (prepare .cold plan) cachedDegrees = 0 := by simp [preparation,Prepared.visits,prepare]

theorem retained_preparation (prices : Prices) (old : Prepared plan) (equations : Equations n) (same) (cachedDegrees : Bool) :
    preparation prices (old.reconfigure equations same) cachedDegrees = 0 := by rw [preparation,revision_visits]; simp

/-- A one-shot workload repeats construction and publication for every request. -/
def coldBatch (prices : Prices) (prepared : Prepared plan) (astNodes uses : Nat) :=
  uses * (construction prices n astNodes prepared.edges false + prepared.charge + core prices n prepared.run.stats + prices.publication*n)

theorem cold_batch_bound (prices : Prices) (plan : Plan n) (astNodes uses : Nat) (candidate : Queue) :
    coldBatch prices (prepare .cold plan) astNodes uses ≤
      uses*(construction prices n astNodes plan.edgeCount false +
        (prepare .cold plan).ceiling candidate + core prices n (prepare .cold plan).run.stats + prices.publication*n) := by
  apply Nat.mul_le_mul_left
  apply Nat.add_le_add_right
  apply Nat.add_le_add_right
  apply Nat.add_le_add_left
  exact Nat.le_trans (actual_bound _) (choose_minimum _ (Or.inl rfl) candidate)

/-- Retained topology still copies/checks the new syntax on every revision. -/
def revisionBatch (prices : Prices) (prepared : Prepared plan) (astNodes uses : Nat) :=
  uses*(construction prices n astNodes prepared.edges true + prepared.charge + core prices n prepared.run.stats + prices.publication*n)

theorem revision_batch_bound (prices : Prices) (old : Prepared plan) (equations : Equations n) (same)
    (astNodes uses : Nat) :
    revisionBatch prices (old.reconfigure equations same) astNodes uses ≤
      uses*(construction prices n astNodes old.edges true +
        (old.reconfigure equations same).ceiling (old.reconfigure equations same).choose + core prices n (old.reconfigure equations same).run.stats + prices.publication*n) := by
  apply Nat.mul_le_mul_left
  apply Nat.add_le_add_right
  apply Nat.add_le_add_right
  apply Nat.add_le_add_left
  exact actual_bound _

def assemble (equations : Equations n) (plan : Plan n) (source : plan.source = equations) :
    ConstructionCache.Cache (declaration equations) × Stats :=
  let result := (prepare .cold plan).solve
  ({closed := ⟨raw (values result.store),by
      rw [GeneralizedGraph.Declaration.step_eq]
      funext index
      rw [PositiveEquations.resolve]
      have fixed : step equations (values result.store) = values result.store := by rw [← source]; exact result.fixed
      exact congrArg (fun value : Bool => some (Except.ok (ε := ComputationError (Fin n)) value)) (congrFun fixed index)⟩
    evaluated := [],reused := []},result.stats)

theorem assemble_canonical (equations : Equations n) (plan : Plan n) (source : plan.source = equations) :
    (assemble equations plan source).1.closed.raw = raw (PositiveEquations.close equations).value := by
  change raw (values (prepare .cold plan).solve.store) = _
  rw [canonical,source]

theorem assemble_pop_bound (equations : Equations n) (plan : Plan n) (source : plan.source = equations) :
    (assemble equations plan source).2.pops ≤ n+IncrementalClosure.total plan.degree := by
  have same := congrArg Prod.snd (run_core (prepare .cold plan))
  change (prepare .cold plan).solve.stats = (fastClose plan).stats at same
  change (prepare .cold plan).solve.stats.pops ≤ _
  rw [same]; exact fast_pop_bound plan

end LeanPoo.Functional.ClosureLifecycle
