import LeanPoo.Functional.PositiveEquations
import Init.Data.Vector.Lemmas
import Init.Data.Vector.OfFn

/-! Array-backed positive closure with reverse-dependency propagation and an
explicit operation-count model. Correctness refines the least fixed point;
source operation bounds are independent of a particular Scheme backend. -/
namespace LeanPoo.Functional.IncrementalClosure
open PositiveEquations

abbrev Store (n : Nat) := Vector Bool n

def values (store : Store n) : Bits n := fun index => store[index.val]
def replace (source : Fin n → α) (index : Fin n) (value : α) : Fin n → α :=
  fun query => if query = index then value else source query

theorem values_set (store : Store n) (index : Fin n) :
    values (store.set index.val true index.isLt) = replace (values store) index true := by
  funext query
  simp [values,Vector.getElem_set,replace,Fin.ext_iff,eq_comm]

def total : {n : Nat} → (Fin n → Nat) → Nat
  | 0,_ => 0
  | _+1,source => source 0 + total (fun index => source index.succ)

theorem total_replace (source : Fin n → Nat) (index : Fin n) (value : Nat) :
    total (replace source index value) + source index = total source + value := by
  induction n with
  | zero => exact Fin.elim0 index
  | succ n ih =>
    refine Fin.cases ?_ (fun index => ?_) index
    · simp [total,replace,Fin.succ_ne_zero]; omega
    · have tail := ih (fun query => source query.succ) index
      have tails : (fun query : Fin n => replace source index.succ value query.succ) =
          replace (fun query => source query.succ) index value := by
        funext query
        simp [replace]
      change (replace source index.succ value 0 + total (fun query => replace source index.succ value query.succ)) +
        source index.succ = (source 0 + total (fun query => source query.succ)) + value
      rw [tails]
      have head : replace source index.succ value 0 = source 0 := by simp [replace,Ne.symm (Fin.succ_ne_zero index)]
      rw [head]
      omega

theorem total_eq_list (source : Fin n → Nat) : total source = (List.ofFn source).sum := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [total,List.ofFn_succ,List.sum_cons] using congrArg (source 0 + ·) (ih (fun index => source index.succ))

def credit (degrees : Fin n → Nat) (state : Bits n) : Nat :=
  total (fun index => if state index then 0 else degrees index)

theorem credit_set (degrees : Fin n → Nat) (state : Bits n) (index : Fin n) (absent : state index = false) :
    credit degrees (replace state index true) + degrees index = credit degrees state := by
  have same : (fun query => if replace state index true query then 0 else degrees query) =
      replace (fun query => if state query then 0 else degrees query) index 0 := by
    funext query
    by_cases equal : query = index <;> simp [replace,equal]
  unfold credit
  rw [same]
  simpa [absent] using total_replace (fun query => if state query then 0 else degrees query) index 0

def dependencies : Expr n → List (Fin n)
  | .literal _ => []
  | .read index => [index]
  | .both left right | .either left right => dependencies left ++ dependencies right

/-- Linear dependency collection; the append-based list above is specification
only, so skewed expression trees do not cause quadratic index compilation. -/
def collectDeps : Expr n → List (Fin n) → List (Fin n)
  | .literal _,tail => tail
  | .read index,tail => index :: tail
  | .both left right,tail | .either left right,tail => collectDeps left (collectDeps right tail)

theorem collectDeps_correct (expression : Expr n) (tail : List (Fin n)) :
    collectDeps expression tail = dependencies expression ++ tail := by
  induction expression generalizing tail <;> simp_all [collectDeps,dependencies,List.append_assoc]

def nodes : Expr n → Nat
  | .literal _ | .read _ => 1
  | .both left right | .either left right => 1+nodes left+nodes right

/-- An instrumented strict interpreter: both child results and their costs are
part of the source operation semantics. No old functional approximation is read. -/
def evalCost (store : Store n) : Expr n → Bool × Nat
  | .literal value => (value,1)
  | .read index => (store[index.val],1)
  | .both left right =>
    let l := evalCost store left
    let r := evalCost store right
    (l.1 && r.1,1+l.2+r.2)
  | .either left right =>
    let l := evalCost store left
    let r := evalCost store right
    (l.1 || r.1,1+l.2+r.2)

theorem run_correct (expression : Expr n) (store : Store n) :
    evalCost store expression = (expression.eval (values store),nodes expression) := by
  induction expression <;> simp_all [evalCost,Expr.eval,nodes,values]

theorem expressionLocality (expression : Expr n) (left right : Bits n)
    (same : ∀ index ∈ dependencies expression, left index = right index) : expression.eval left = expression.eval right := by
  induction expression with
  | literal value => rfl
  | read index => exact same index (by simp [dependencies])
  | both left right ihLeft ihRight =>
    rw [Expr.eval,Expr.eval,ihLeft (fun index member => same index (by simp [dependencies,member])),
      ihRight (fun index member => same index (by simp [dependencies,member]))]
  | either left right ihLeft ihRight =>
    rw [Expr.eval,Expr.eval,ihLeft (fun index member => same index (by simp [dependencies,member])),
      ihRight (fun index member => same index (by simp [dependencies,member]))]

abbrev Watches (n : Nat) := Vector (List (Fin n)) n

def addEdge (watches : Watches n) (edge : Fin n × Fin n) : Watches n :=
  watches.set edge.1.val (edge.2 :: watches[edge.1.val]) edge.1.isLt

theorem addEdge_members (watches : Watches n) (edge : Fin n × Fin n) (source target : Fin n) :
    target ∈ (addEdge watches edge)[source.val] ↔ target ∈ watches[source.val] ∨ edge = (source,target) := by
  by_cases same : edge.1 = source
  · rcases edge with ⟨first,second⟩
    dsimp at same
    subst first
    simp [addEdge,or_comm,eq_comm]
  · have different : edge ≠ (source,target) := fun equal => same (congrArg Prod.fst equal)
    simp [addEdge,show edge.1.val ≠ source.val from fun equal => same (Fin.ext equal),different]

def edges (equations : Equations n) : List (Fin n × Fin n) :=
  (List.ofFn fun target => (collectDeps (equations target) []).map (fun source => (source,target))).flatten

def buildIndex (equations : Equations n) : Watches n :=
  (edges equations).foldl addEdge (Vector.replicate n [])

theorem index_members (items : List (Fin n × Fin n)) (initial : Watches n) (source target : Fin n) :
    target ∈ (items.foldl addEdge initial)[source.val] ↔ target ∈ initial[source.val] ∨ (source,target) ∈ items := by
  induction items generalizing initial with
  | nil => simp
  | cons edge rest ih =>
    rw [List.foldl_cons,ih,addEdge_members]
    simp [or_assoc,eq_comm]

theorem index_complete (equations : Equations n) (source target : Fin n)
    (dependency : source ∈ dependencies (equations target)) : target ∈ (buildIndex equations)[source.val] := by
  rw [buildIndex,index_members]
  right
  simp only [edges,collectDeps_correct,List.append_nil]
  apply List.mem_flatten.mpr
  refine ⟨(dependencies (equations target)).map (fun dep => (dep,target)),?_,?_⟩
  · exact List.mem_ofFn.mpr ⟨target,rfl⟩
  · exact List.mem_map.mpr ⟨source,dependency,rfl⟩

theorem total_zero : total (fun _ : Fin n => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [total,Nat.zero_add] using ih

theorem edge_increases (watches : Watches n) (edge : Fin n × Fin n) :
    total (fun index : Fin n => (addEdge watches edge)[index.val].length) =
      total (fun index : Fin n => watches[index.val].length)+1 := by
  let degree := fun index : Fin n => watches[index.val].length
  have same : (fun index : Fin n => (addEdge watches edge)[index.val].length) =
      replace degree edge.1 (degree edge.1+1) := by
    funext index
    by_cases equal : index = edge.1
    · subst index; simp [addEdge,replace,degree]
    · simp [addEdge,replace,degree,Fin.ext_iff,show edge.1.val ≠ index.val from fun h => equal (Fin.ext h.symm),
        show index.val ≠ edge.1.val from fun h => equal (Fin.ext h)]
  rw [same]
  change total (replace degree edge.1 (degree edge.1+1)) = total degree+1
  have changed := total_replace degree edge.1 (degree edge.1+1)
  omega

theorem index_edge_count (items : List (Fin n × Fin n)) (initial : Watches n) :
    total (fun index : Fin n => (items.foldl addEdge initial)[index.val].length) =
      total (fun index : Fin n => initial[index.val].length)+items.length := by
  induction items generalizing initial with
  | nil => simp
  | cons edge rest ih => rw [List.foldl_cons,ih,edge_increases]; simp; omega

structure Plan (n : Nat) where
  equations : Vector (Expr n) n
  watches : Watches n
  complete : ∀ (source target : Fin n), source ∈ dependencies equations[target.val] → target ∈ watches[source.val]

/-- Reverse edges are compiled once by direct array insertion, retaining
occurrences rather than performing a quadratic all-pairs membership scan. -/
def compile (equations : Equations n) : Plan n :=
  let table := Vector.ofFn equations
  ⟨table,buildIndex (fun index => table[index.val]),by
    intro source target member
    exact index_complete (fun index => table[index.val]) source target member⟩


def Plan.source (plan : Plan n) : Equations n := fun index => plan.equations[index.val]
@[simp] theorem compile_source (equations : Equations n) : (compile equations).source = equations := by
  funext index
  simp [compile,Plan.source]

/-- Literal/policy changes with the same actual read topology retain the exact
reverse index. This requires a footprint equality proof, never a version label. -/
def reconfigure (prior : Plan n) (equations : Equations n)
    (same : ∀ index, dependencies (equations index) = dependencies (prior.source index)) : Plan n :=
  ⟨Vector.ofFn equations,prior.watches,by
    intro source target member
    apply prior.complete source target
    change source ∈ dependencies (prior.source target)
    rw [← same target]
    simpa using member⟩

@[simp] theorem reconfigure_source (prior : Plan n) (equations : Equations n) (same) :
    (reconfigure prior equations same).source = equations := by funext index; simp [reconfigure,Plan.source]

@[simp] theorem reconfigure_index (prior : Plan n) (equations : Equations n) (same) :
    (reconfigure prior equations same).watches = prior.watches := rfl

def Plan.degree (plan : Plan n) (index : Fin n) := plan.watches[index.val].length

def maxList : List Nat → Nat
  | [] => 0
  | first :: rest => max first (maxList rest)

theorem maxList_bound (items : List Nat) (value : Nat) (member : value ∈ items) : value ≤ maxList items := by
  induction items with
  | nil => simp at member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with same | member
    · subst first; exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih member) (Nat.le_max_right _ _)

def Plan.maxNodes (plan : Plan n) := maxList (List.ofFn fun index : Fin n => nodes plan.equations[index.val])

theorem Plan.nodes_bound (plan : Plan n) (index : Fin n) : nodes plan.equations[index.val] ≤ plan.maxNodes :=
  maxList_bound _ _ (List.mem_ofFn.mpr ⟨index,rfl⟩)

/-- The operational sum traverses finite indices directly. The recursively
shifted function sum is a proof specification and never runs in fastClose. -/
def Plan.edgeCount (plan : Plan n) := (List.ofFn plan.degree).sum

theorem Plan.edgeCount_eq (plan : Plan n) : plan.edgeCount = total plan.degree := (total_eq_list _).symm

structure Stats where
  pops : Nat := 0
  evaluations : Nat := 0
  nodes : Nat := 0
  writes : Nat := 0
  pushes : Nat := 0
  deriving Repr, BEq

/-- The queue excludes no unstable equation. Lower/rising certify monotone
asynchronous iteration, rather than admission by testing the final output. -/
structure Invariant (plan : Plan n) (store : Store n) (queue : List (Fin n)) : Prop where
  rising : Below (values store) (step plan.source (values store))
  lower : ∀ other, step plan.source other = other → Below (values store) other
  stable : ∀ index, index ∉ queue → step plan.source (values store) index = values store index

def potential (plan : Plan n) (store : Store n) (queue : List (Fin n)) := queue.length+credit plan.degree (values store)

structure Result (plan : Plan n) (initial : Store n) (queue : List (Fin n)) where
  store : Store n
  fixed : step plan.source (values store) = values store
  least : ∀ other, step plan.source other = other → Below (values store) other
  stats : Stats
  queue_balance : stats.pops = queue.length+stats.pushes
  pushes_bound : stats.pushes ≤ credit plan.degree (values initial)
  evaluations_bound : stats.evaluations ≤ stats.pops
  writes_bound : stats.writes ≤ n-weight (values initial)
  nodes_bound : stats.nodes ≤ stats.evaluations*plan.maxNodes


theorem replace_grows (state : Bits n) (index : Fin n) : Below state (replace state index true) := by
  intro query present
  by_cases same : query = index <;> simp [replace,same,present]

variable {n : Nat} {plan : Plan n} {store : Store n} {index : Fin n} {rest : List (Fin n)}

theorem Invariant.pop (invariant : Invariant plan store (index :: rest))
    (same : step plan.source (values store) index = values store index) : Invariant plan store rest :=
  ⟨invariant.rising,invariant.lower,by
    intro query outside
    by_cases equal : query = index
    · subst query; exact same
    · exact invariant.stable query (by simp [List.mem_cons,equal,outside])⟩

theorem Invariant.advance (invariant : Invariant plan store (index :: rest))
    (enabled : plan.equations[index.val].eval (values store) = true) :
    Invariant plan (store.set index.val true index.isLt) (plan.watches[index.val] ++ rest) := by
  let next := store.set index.val true index.isLt
  have growth : Below (values store) (values next) := by rw [show values next = replace (values store) index true from values_set _ _]; exact replace_grows _ _
  have rising : Below (values next) (step plan.source (values next)) := by
    intro query present
    apply Expr.monotone _ growth
    by_cases same : query = index
    · subst query; exact enabled
    · apply invariant.rising query
      simpa [next,values_set,replace,same] using present
  refine ⟨rising,?_,?_⟩
  · intro other fixed query present
    by_cases same : query = index
    · subst query
      have allowed := Expr.monotone plan.equations[index.val] (invariant.lower other fixed) enabled
      have equation := congrFun fixed index
      exact equation ▸ allowed
    · apply invariant.lower other fixed query
      simpa [next,values_set,replace,same] using present
  · intro query outside
    by_cases same : query = index
    · subst query
      have trueAt : values next index = true := by simp [next,values_set,replace]
      exact (rising index trueAt).trans trueAt.symm
    · have notRest : query ∉ rest := fun member => outside (List.mem_append_right _ member)
      have notWatch : query ∉ plan.watches[index.val] := fun member => outside (List.mem_append_left _ member)
      have equal : plan.equations[query.val].eval (values next) = plan.equations[query.val].eval (values store) := by
        apply expressionLocality
        intro dependency member
        have distinct : dependency ≠ index := by
          intro same
          subst dependency
          exact notWatch (plan.complete index query member)
        simp [next,values_set,replace,distinct]
      change plan.equations[query.val].eval (values next) = values next query
      rw [equal]
      have stable := invariant.stable query (by simp [List.mem_cons,same,notRest])
      change plan.equations[query.val].eval (values store) = _ at stable
      rw [stable]
      simp [next,values_set,replace,same]

def Result.skip (result : Result plan store rest) : Result plan store (index :: rest) :=
  ⟨result.store,result.fixed,result.least,{result.stats with pops := result.stats.pops+1},by
    have balance := result.queue_balance; dsimp only; simp only [List.length_cons]; omega,
    result.pushes_bound,by have bound := result.evaluations_bound; dsimp only; omega,result.writes_bound,result.nodes_bound⟩

def Result.reject (result : Result plan store rest) (cost : Nat) (correct : cost = nodes plan.equations[index.val]) :
    Result plan store (index :: rest) :=
  ⟨result.store,result.fixed,result.least,
    {result.stats with pops := result.stats.pops+1,evaluations := result.stats.evaluations+1,nodes := result.stats.nodes+cost},by
      have balance := result.queue_balance; dsimp only; simp only [List.length_cons]; omega,
    result.pushes_bound,by have bound := result.evaluations_bound; dsimp only; omega,result.writes_bound,
    by
      have bound := result.nodes_bound
      have size := plan.nodes_bound index
      dsimp only
      rw [correct,Nat.add_mul]
      simp only [Nat.one_mul]
      omega⟩

def Result.advance (result : Result plan (store.set index.val true index.isLt) (plan.watches[index.val] ++ rest))
    (absent : values store index = false) (cost : Nat) (correct : cost = nodes plan.equations[index.val]) :
    Result plan store (index :: rest) :=
  ⟨result.store,result.fixed,result.least,
    {pops := result.stats.pops+1,evaluations := result.stats.evaluations+1,
     nodes := result.stats.nodes+cost,writes := result.stats.writes+1,pushes := result.stats.pushes+plan.degree index},by
      have balance := result.queue_balance
      simp only [List.length_append] at balance
      dsimp only
      simp only [List.length_cons]
      dsimp [Plan.degree] at *
      omega,
    by
      have bound := result.pushes_bound
      have credit := credit_set plan.degree (values store) index absent
      rw [← values_set] at credit
      dsimp only
      omega,
    by have bound := result.evaluations_bound; dsimp only; omega,
    by
      have bound := result.writes_bound
      have grow := replace_grows (values store) index
      have unequal : values store ≠ replace (values store) index true := by
        intro same
        have observed := congrFun same index
        simp [replace,absent] at observed
      have strict := (system plan.source).strict grow unequal
      rw [← values_set] at strict
      change weight (values store) < weight (values (store.set index.val true index.isLt)) at strict
      have bounded := weight_bound (values (store.set index.val true index.isLt))
      dsimp only
      omega,
    by
      have bound := result.nodes_bound
      have size := plan.nodes_bound index
      dsimp only
      rw [correct,Nat.add_mul]
      simp only [Nat.one_mul]
      omega⟩

def Result.done (invariant : Invariant plan store []) : Result plan store [] :=
  ⟨store,funext (fun index => invariant.stable index (by simp)),invariant.lower,{},by simp,by simp,by simp,by simp,by simp⟩

private def search (fuel : Nat) (plan : Plan n) (store : Store n) (queue : List (Fin n))
    (invariant : Invariant plan store queue) (bounded : potential plan store queue ≤ fuel) : Result plan store queue :=
  match fuel with
  | 0 => by
    have empty : queue = [] := by
      have zero : queue.length = 0 := by unfold potential at bounded; omega
      exact List.eq_nil_of_length_eq_zero zero
    subst queue
    exact Result.done invariant
  | fuel+1 =>
    match queue with
    | [] => Result.done invariant
    | index :: rest =>
      have popBound : potential plan store rest ≤ fuel := by
        unfold potential at bounded ⊢
        simp only [List.length_cons] at bounded
        omega
      if known : values store index = true then
        (search fuel plan store rest (invariant.pop ((invariant.rising index known).trans known.symm)) popBound).skip
      else
        let evaluated := evalCost store plan.equations[index.val]
        have correct : evaluated.2 = nodes plan.equations[index.val] := by simp [evaluated,run_correct]
        have absent : values store index = false := by cases found : values store index <;> simp_all
        if enabled : evaluated.1 = true then
          let next := store.set index.val true index.isLt
          let result := search fuel plan next (plan.watches[index.val] ++ rest)
            (invariant.advance (by simpa [evaluated,run_correct] using enabled)) (by
              have credit := credit_set plan.degree (values store) index absent
              rw [← values_set] at credit
              unfold potential at bounded ⊢
              simp only [List.length_cons,List.length_append] at bounded ⊢
              dsimp only [next,Plan.degree] at credit ⊢
              omega)
          result.advance absent evaluated.2 correct
        else
          let result := search fuel plan store rest (invariant.pop (by
            have same : plan.equations[index.val].eval (values store) = false := by
              simpa [evaluated,run_correct] using Bool.eq_false_iff.mpr enabled
            exact same.trans absent.symm)) popBound
          result.reject evaluated.2 correct
termination_by fuel

/-- Every node is initially queued, so no unstable equation is omitted. -/
def close (plan : Plan n) :=
  let store := Vector.replicate n false
  let queue : List (Fin n) := List.ofFn id
  search (potential plan store queue) plan store queue ⟨by
    intro index present; simp [store,values] at present,
    by intro other fixed index present; simp [store,values] at present,
    by intro index outside; exact False.elim (outside (List.mem_ofFn.mpr ⟨index,rfl⟩))⟩ (Nat.le_refl _)

theorem canonical (plan : Plan n) : values (close plan).store = (PositiveEquations.close plan.source).value :=
  (PositiveEquations.least_unique plan.source _ (close plan).fixed (close plan).least).symm

theorem pop_bound (plan : Plan n) : (close plan).stats.pops ≤ n+total plan.degree := by
  have balance := (close plan).queue_balance
  have bound := (close plan).pushes_bound
  have normalized : credit plan.degree (values (Vector.replicate n false)) = total plan.degree := by
    unfold credit
    congr 1
    funext index
    simp [values]
  rw [normalized] at bound
  simp only [List.length_ofFn] at balance
  omega

/-- Componentwise source operation counts. -/
def Stats.add (left right : Stats) : Stats :=
  ⟨left.pops+right.pops,left.evaluations+right.evaluations,left.nodes+right.nodes,
    left.writes+right.writes,left.pushes+right.pushes⟩

/-- Tail-recursive executable loop. Fuel is derived from the proved V+E
potential, not supplied by clients. The theorem below rules out early exhaustion. -/
def execute (fuel : Nat) (plan : Plan n) (store : Store n) (queue : List (Fin n)) (stats : Stats) : Store n × Stats :=
  match fuel,queue with
  | 0,_ | _,[] => (store,stats)
  | fuel+1,index :: rest =>
    let stats := {stats with pops := stats.pops+1}
    if values store index then execute fuel plan store rest stats else
      let evaluated := evalCost store plan.equations[index.val]
      let stats := {stats with evaluations := stats.evaluations+1,nodes := stats.nodes+evaluated.2}
      if evaluated.1 then
        execute fuel plan (store.set index.val true index.isLt) (plan.watches[index.val] ++ rest)
          {stats with writes := stats.writes+1,pushes := stats.pushes+plan.degree index}
      else execute fuel plan store rest stats

private theorem execute_refines (fuel : Nat) (plan : Plan n) (store : Store n) (queue : List (Fin n))
    (invariant : Invariant plan store queue) (bounded : potential plan store queue ≤ fuel) (stats : Stats) :
    execute fuel plan store queue stats =
      ((search fuel plan store queue invariant bounded).store,
       stats.add (search fuel plan store queue invariant bounded).stats) := by
  induction fuel generalizing store queue stats with
  | zero =>
    have empty : queue = [] := by
      apply List.eq_nil_of_length_eq_zero
      unfold potential at bounded
      omega
    subst queue
    simp [execute,search,Result.done,Stats.add]
  | succ fuel ih =>
    cases queue with
    | nil => simp [execute,search,Result.done,Stats.add]
    | cons index rest =>
      have popBound : potential plan store rest ≤ fuel := by
        unfold potential at bounded ⊢
        simp only [List.length_cons] at bounded
        omega
      by_cases known : values store index = true
      · rw [execute,ite_eq_left known]
        rw [ih store rest (invariant.pop ((invariant.rising index known).trans known.symm)) popBound]
        simp [search,known,Result.skip,Stats.add,Nat.add_assoc,Nat.add_comm]
      · have absent : values store index = false := by cases found : values store index <;> simp_all
        rw [execute,ite_eq_right known]
        by_cases enabled : (evalCost store plan.equations[index.val]).1 = true
        · rw [ite_eq_left enabled]
          have nextBound : potential plan (store.set index.val true index.isLt) (plan.watches[index.val] ++ rest) ≤ fuel := by
            have credit := credit_set plan.degree (values store) index absent
            rw [← values_set] at credit
            unfold potential at bounded ⊢
            simp only [List.length_cons,List.length_append] at bounded ⊢
            dsimp only [Plan.degree] at credit ⊢
            omega
          rw [ih _ _ (invariant.advance (by simpa [run_correct] using enabled)) nextBound]
          simp [search,known,enabled,Result.advance,Stats.add,Nat.add_assoc,Nat.add_comm]
        · rw [ite_eq_right enabled]
          have stable : step plan.source (values store) index = values store index := by
            have disabled : (evalCost store plan.equations[index.val]).1 = false := Bool.eq_false_iff.mpr enabled
            simpa [run_correct,absent,step,Plan.source] using disabled
          rw [ih store rest (invariant.pop stable) popBound]
          simp [search,known,enabled,Result.reject,Stats.add,Nat.add_assoc,Nat.add_comm]
          let remainder := search fuel plan store rest (invariant.pop stable) popBound
          change remainder.stats.nodes + (stats.nodes+(evalCost store plan.equations[index.val]).2) =
            stats.nodes+((evalCost store plan.equations[index.val]).2+remainder.stats.nodes)
          omega

/-- Production entry point: proof/reference computation is erased. The returned
arrays and counters come only from the tail loop, with exactly the certified
semantics and operation-count bounds. -/
def fastClose (plan : Plan n) : Result plan (Vector.replicate n false) (List.ofFn id) :=
  let initial := Vector.replicate n false
  let queue : List (Fin n) := List.ofFn id
  let actual := execute (n+plan.edgeCount) plan initial queue {}
  have fuelEq : n+plan.edgeCount = potential plan initial queue := by
    unfold potential
    have normalized : credit plan.degree (values initial) = total plan.degree := by
      unfold credit
      congr 1
      funext index
      simp [initial,values]
    rw [normalized,plan.edgeCount_eq]
    simp [queue]
  have same : actual = ((close plan).store,(close plan).stats) := by
    change execute (n+plan.edgeCount) plan initial queue {} = _
    rw [fuelEq]
    have refines := execute_refines (potential plan initial queue) plan initial queue
      (by exact ⟨by intro index present; simp [initial,values] at present,
        by intro other fixed index present; simp [initial,values] at present,
        by intro index outside; exact False.elim (outside (List.mem_ofFn.mpr ⟨index,rfl⟩))⟩) (Nat.le_refl _) {}
    simpa [Stats.add,close] using refines
  {store := actual.1
   fixed := by rw [congrArg Prod.fst same]; exact (close plan).fixed
   least := by rw [congrArg Prod.fst same]; exact (close plan).least
   stats := actual.2
   queue_balance := by rw [congrArg Prod.snd same]; exact (close plan).queue_balance
   pushes_bound := by rw [congrArg Prod.snd same]; exact (close plan).pushes_bound
   evaluations_bound := by rw [congrArg Prod.snd same]; exact (close plan).evaluations_bound
   writes_bound := by rw [congrArg Prod.snd same]; exact (close plan).writes_bound
   nodes_bound := by rw [congrArg Prod.snd same]; exact (close plan).nodes_bound}

theorem fast_canonical (plan : Plan n) : values (fastClose plan).store = (PositiveEquations.close plan.source).value :=
  (PositiveEquations.least_unique plan.source _ (fastClose plan).fixed (fastClose plan).least).symm

theorem fast_pop_bound (plan : Plan n) : (fastClose plan).stats.pops ≤ n+total plan.degree := by
  have balance := (fastClose plan).queue_balance
  have bound := (fastClose plan).pushes_bound
  have normalized : credit plan.degree (values (Vector.replicate n false)) = total plan.degree := by
    unfold credit
    congr 1
    funext index
    simp [values]
  rw [normalized] at bound
  simp only [List.length_ofFn] at balance
  omega

/-- Backend-specific primitive upper costs can be supplied without changing
semantic proofs. This charges queue work, evaluation dispatch, AST visits,
state writes and edge scheduling separately. -/
structure Prices where
  pop : Nat
  evaluate : Nat
  node : Nat
  write : Nat
  push : Nat

def Prices.charge (prices : Prices) (stats : Stats) :=
  prices.pop*stats.pops + prices.evaluate*stats.evaluations + prices.node*stats.nodes +
    prices.write*stats.writes + prices.push*stats.pushes

theorem priced_bound (plan : Plan n) (prices : Prices) :
    prices.charge (fastClose plan).stats ≤
      prices.pop*(n+plan.edgeCount) + prices.evaluate*(n+plan.edgeCount) +
      prices.node*((n+plan.edgeCount)*plan.maxNodes) + prices.write*n + prices.push*plan.edgeCount := by
  have pops : (fastClose plan).stats.pops ≤ n+plan.edgeCount := by rw [plan.edgeCount_eq]; exact fast_pop_bound plan
  have evaluations := Nat.le_trans (fastClose plan).evaluations_bound pops
  have nodes := Nat.le_trans (fastClose plan).nodes_bound (Nat.mul_le_mul_right plan.maxNodes evaluations)
  have writes := Nat.le_trans (fastClose plan).writes_bound (Nat.sub_le _ _)
  have pushes : (fastClose plan).stats.pushes ≤ plan.edgeCount := by
    have bound := (fastClose plan).pushes_bound
    rw [plan.edgeCount_eq]
    have normalized : credit plan.degree (values (Vector.replicate n false)) = total plan.degree := by
      unfold credit
      congr 1
      funext index
      simp [values]
    rwa [normalized] at bound
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
    (Nat.add_le_add (Nat.mul_le_mul_left prices.pop pops) (Nat.mul_le_mul_left prices.evaluate evaluations))
    (Nat.mul_le_mul_left prices.node nodes)) (Nat.mul_le_mul_left prices.write writes))
    (Nat.mul_le_mul_left prices.push pushes)

/-- Actual scheduling edges equal the compiled dependency occurrences, including
repeated operands. Index construction is included in the published cost scope. -/
theorem compiled_edge_count (equations : Equations n) : total (compile equations).degree = (edges equations).length := by
  have count := index_edge_count (edges equations) (Vector.replicate n [])
  have zero : total (fun index : Fin n => (Vector.replicate n ([] : List (Fin n)))[index.val].length) = 0 := by
    simpa using (total_zero (n := n))
  rw [zero] at count
  change total (fun index : Fin n => (buildIndex (fun query => (Vector.ofFn equations)[query.val]))[index.val].length) = _
  have same : (fun query : Fin n => (Vector.ofFn equations)[query.val]) = equations := by funext query; simp
  rw [same]
  simpa only [buildIndex,Nat.zero_add] using count

/-- Adapt one fast run to existing publication and retain its actual counters.
Reference computation and source equality are proof-only. -/
def assemble (equations : Equations n) (plan : Plan n) (source : plan.source = equations) :
    ConstructionCache.Cache (declaration equations) × Stats :=
  let result := fastClose plan
  ({closed := ⟨raw (values result.store),by
      rw [GeneralizedGraph.Declaration.step_eq]
      funext index
      rw [PositiveEquations.resolve]
      have fixed : step equations (values result.store) = values result.store := by
        rw [← source]
        exact result.fixed
      exact congrArg (fun value : Bool => some (Except.ok (ε := ComputationError (Fin n)) value)) (congrFun fixed index)⟩
    evaluated := []
    reused := []},result.stats)

theorem assemble_canonical (equations : Equations n) (plan : Plan n) (source : plan.source = equations) :
    (assemble equations plan source).1.closed.raw = raw (PositiveEquations.close equations).value := by
  change raw (values (fastClose plan).store) = _
  rw [fast_canonical,source]

theorem assemble_pop_bound (equations : Equations n) (plan : Plan n) (source : plan.source = equations) :
    (assemble equations plan source).2.pops ≤ n+total plan.degree := fast_pop_bound plan

def materialize (equations : Equations n) := (assemble equations (compile equations) (compile_source equations)).1

theorem materialize_canonical (equations : Equations n) :
    (materialize equations).closed.raw = raw (PositiveEquations.close equations).value :=
  assemble_canonical _ _ _

end LeanPoo.Functional.IncrementalClosure
