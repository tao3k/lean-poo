import Std

namespace QuotientRoutes
variable {N O : Type} [DecidableEq O]

-- Nodes are the ordered concatenation of captured member rows. Owner is a
-- PURE lookup in one immutable SCC snapshot, never an author callback.
def providers (root : O) (owner : N → O) : List N → List O
  | [] => []
  | node :: rest => if owner node = root then providers root owner rest
      else owner node :: providers root owner rest

def allowed (root : O) (owner : N → O) : List N → List N
  | [] => []
  | node :: rest => if owner node = root then allowed root owner rest
      else node :: allowed root owner rest

def collect (root : O) (owner : N → O) : List N → List O × List N
  | [] => ([], [])
  | node :: rest =>
      let provider := owner node
      let next := collect root owner rest
      if provider = root then next else (provider :: next.1, node :: next.2)

theorem same_providers (root : O) (owner : N → O) (nodes : List N) :
    (collect root owner nodes).1 = providers root owner nodes := by
  induction nodes with
  | nil => rfl
  | cons node rest ih =>
    by_cases h : owner node = root <;> simp [collect, providers, h, ih]

theorem same_allowed (root : O) (owner : N → O) (nodes : List N) :
    (collect root owner nodes).2 = allowed root owner nodes := by
  induction nodes with
  | nil => rfl
  | cons node rest ih =>
    by_cases h : owner node = root <;> simp [collect, allowed, h, ih]

-- Keep the SAME rightmost-occurrence normalizer, not a new ordering rule.
theorem same_routes (root : O) (owner : N → O) (nodes : List N)
    (normalize : List O → List O) :
    (normalize (collect root owner nodes).1, (collect root owner nodes).2) =
      (normalize (providers root owner nodes), allowed root owner nodes) := by
  rw [same_providers, same_allowed]

-- Native deduplication constructor/action runs first, then allowed-table
-- construction/insertion. They remain the SAME actions in both programs.
-- Actions may fail and change state. No equivalence of arbitrary owner
-- callbacks is claimed; only the owner function above is pure.
abbrev Action (S E V : Type) := S → Except E V × S
def bind (first : Action S E A) (next : A → Action S E B) : Action S E B :=
  fun state => match first state with
    | (.error error, state') => (.error error, state')
    | (.ok value, state') => next value state'

def prepare (dedup : List O → Action S E (List O))
    (makeAllowed : List N → Action S E A) (routes : List O × List N) :
    Action S E (List O × A) :=
  bind (dedup routes.1) (fun dependencies =>
    bind (makeAllowed routes.2) (fun table => fun state => (.ok (dependencies, table), state)))

theorem same_effectful_preparation (root : O) (owner : N → O) (nodes : List N)
    (dedup : List O → Action S E (List O)) (makeAllowed : List N → Action S E A) :
    prepare dedup makeAllowed (collect root owner nodes) =
      prepare dedup makeAllowed (providers root owner nodes, allowed root owner nodes) := by
  have routes : collect root owner nodes =
      (providers root owner nodes, allowed root owner nodes) :=
    Prod.ext (same_providers root owner nodes) (same_allowed root owner nodes)
  rw [routes]

-- A different external node in the same provider group is still allowed.
-- The allowed domain is node identity, NOT just the deduplicated group roots.
example : collect 0 (fun n : Nat => if n = 0 then 0 else 1) [0, 2, 3, 2] =
    ([1, 1, 1], [2, 3, 2]) := by decide

#print axioms same_providers
#print axioms same_allowed
#print axioms same_routes
#print axioms same_effectful_preparation
end QuotientRoutes
