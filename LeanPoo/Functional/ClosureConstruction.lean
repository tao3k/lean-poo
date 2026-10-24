import LeanPoo.Functional.ClosureLifecycle

/-! Fused private copying/index construction and dependency-equal revision.
Generalized-protocol future work; source operation and layout costs only. -/
namespace LeanPoo.Functional.ClosureConstruction
open PositiveEquations IncrementalClosure
variable {n : Nat} {plan : Plan n}

structure Copied (n : Nat) where
  expression : Expr n
  watches : Watches n
  visited : Nat
  reads : Nat

def copyIndexed (expression : Expr n) (target : Fin n) (initial : Watches n) : Copied n :=
  match expression with
  | .literal value => ⟨.literal value,initial,1,0⟩
  | .read source => ⟨.read source,addEdge initial (source,target),1,1⟩
  | .both left right =>
    let first := copyIndexed left target initial
    let second := copyIndexed right target first.watches
    ⟨.both first.expression second.expression,second.watches,1+first.visited+second.visited,first.reads+second.reads⟩
  | .either left right =>
    let first := copyIndexed left target initial
    let second := copyIndexed right target first.watches
    ⟨.either first.expression second.expression,second.watches,1+first.visited+second.visited,first.reads+second.reads⟩

theorem copyIndexed_spec (expression : Expr n) (target : Fin n) (initial : Watches n) :
    copyIndexed expression target initial =
      ⟨expression,((dependencies expression).map (fun source => (source,target))).foldl addEdge initial,
        nodes expression,(dependencies expression).length⟩ := by
  induction expression generalizing initial <;>
    simp_all [copyIndexed,dependencies,nodes,List.map_append,List.foldl_append,List.length_append]

def fusedFold (items : List (Expr n × Fin n)) (initial : Watches n) :=
  items.foldl (fun watches item => (copyIndexed item.1 item.2 watches).watches) initial

theorem fusedFold_spec (items : List (Expr n × Fin n)) (initial : Watches n) :
    fusedFold items initial =
      (items.flatMap (fun item => (dependencies item.1).map (fun source => (source,item.2)))).foldl addEdge initial := by
  induction items generalizing initial with
  | nil => rfl
  | cons item rest ih =>
    simp only [fusedFold,List.foldl_cons,copyIndexed_spec] at *
    rw [ih]
    simp [List.flatMap_cons,List.foldl_append]

def fusedIndex (equations : Equations n) :=
  fusedFold (List.ofFn (fun target => (equations target,target))) (Vector.replicate n [])

theorem fusedIndex_eq (equations : Equations n) : fusedIndex equations = buildIndex equations := by
  rw [fusedIndex,fusedFold_spec]
  simp [buildIndex,edges,collectDeps_correct,List.flatMap,List.map_ofFn,Function.comp_def]

def compile (equations : Equations n) : Plan n :=
  let table := Vector.ofFn equations
  ⟨table,fusedIndex (fun index => table[index.val]),by
    intro source target member
    rw [fusedIndex_eq]
    exact index_complete _ source target member⟩

@[simp] theorem compile_source (equations : Equations n) : (compile equations).source = equations := by
  funext index
  simp [compile,Plan.source]

theorem compile_index (equations : Equations n) :
    (compile equations).watches = (IncrementalClosure.compile equations).watches := by
  simp [compile,IncrementalClosure.compile,fusedIndex_eq]

/-- No semantic equivalence is required: same ordered read occurrences permit
changed Boolean operators and reassociation, with a fresh solve from bottom. -/
def reshape (plan : Plan n) (equations : Equations n)
    (same : ∀ index, collectDeps (equations index) [] = collectDeps (plan.source index) []) :=
  IncrementalClosure.reconfigure plan equations (by
    intro index
    simpa only [collectDeps_correct,List.append_nil] using same index)

theorem reshape_index (plan : Plan n) (equations : Equations n) (same) :
    (reshape plan equations same).watches = plan.watches := rfl

theorem reshape_canonical (plan : Plan n) (equations : Equations n) (same) :
    values (ClosureLifecycle.prepare .cold (reshape plan equations same)).solve.store =
      (PositiveEquations.close equations).value := by
  rw [ClosureLifecycle.canonical]
  unfold reshape
  rw [reconfigure_source]

/-- Fused construction removes per-equation visitor closure packets. The larger
shared context is explicit; its size is a backend premise. -/
def constructionWords (layout : ClosureCosts.Layout) (n astNodes edges contextWords visitorWords : Nat) :=
  layout.metadataWords+3*(layout.vectorHeader+n)+layout.descriptorWords*astNodes+
    layout.pairWords*edges+contextWords+visitorWords*n

theorem fusion_saving (layout : ClosureCosts.Layout) (n astNodes edges oldContext contextGrowth visitorWords : Nat)
    (paid : contextGrowth ≤ visitorWords*n) :
    constructionWords layout n astNodes edges (oldContext+contextGrowth) 0 ≤
      constructionWords layout n astNodes edges oldContext visitorWords := by simp [constructionWords]; omega

def fusedCost (prices : ClosureLifecycle.Prices) (n astNodes edges : Nat) (revision : Bool) :=
  prices.equation*n+prices.node*astNodes+prices.context+(if revision then 0 else prices.index*edges)

theorem visitor_saving (prices : ClosureLifecycle.Prices) (n astNodes edges : Nat) (revision : Bool) :
    fusedCost prices n astNodes edges revision + (if revision then 0 else prices.visitor*n) =
      ClosureLifecycle.construction prices n astNodes edges revision := by
  cases revision <;> simp [fusedCost,ClosureLifecycle.construction,Nat.add_assoc]

/-- Repeated preparation of admitted adaptive metadata performs no new degree
visits. The second component counts this operation, not historical plan visits. -/
def ensureAdaptive (old : ClosureLifecycle.Prepared plan) : ClosureLifecycle.Prepared plan × Nat :=
  if old.mode = .adaptive then (old,0) else (old.upgrade,n)

theorem ensureAdaptive_cached (old : ClosureLifecycle.Prepared plan) (ready : old.mode = .adaptive) :
    ensureAdaptive old = (old,0) := by simp [ensureAdaptive,ready]

theorem ensureAdaptive_mode (old : ClosureLifecycle.Prepared plan) :
    (ensureAdaptive old).1.mode = .adaptive := by
  unfold ensureAdaptive
  split <;> simp_all [ClosureLifecycle.Prepared.upgrade]

theorem ensureAdaptive_idempotent (old : ClosureLifecycle.Prepared plan) :
    ensureAdaptive (ensureAdaptive old).1 = ((ensureAdaptive old).1,0) :=
  ensureAdaptive_cached _ (ensureAdaptive_mode old)

/-- Preparation is profitable in the declared ledger only when actual future
savings pay its price. This accepts a measured/calibrated price, not a free scan. -/
theorem preparation_paid (common preparation cold warm uses : Nat)
    (payback : preparation+uses*warm ≤ uses*cold) :
    common+preparation+uses*warm ≤ common+uses*cold := by omega

end LeanPoo.Functional.ClosureConstruction
