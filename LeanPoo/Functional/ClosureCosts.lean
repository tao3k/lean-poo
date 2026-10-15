import LeanPoo.Functional.ChunkedClosure

/-! A target-level representation/allocation contract, not a theorem about
Lean's heap, a Scheme compiler, GC or elapsed time. -/
namespace LeanPoo.Functional.ClosureCosts
open PositiveEquations IncrementalClosure

abbrev Bytes (n : Nat) := Vector UInt8 n

def encode (facts : Store n) : Bytes n := Vector.ofFn fun index => if facts[index.val] then 1 else 0
def decode (bytes : Bytes n) : Store n := Vector.ofFn fun index => bytes[index.val] == 1

theorem decode_encode (facts : Store n) : decode (encode facts) = facts := by
  apply Vector.ext
  intro index bounded
  simp only [decode,encode,Vector.getElem_ofFn]
  cases facts[index] <;> rfl

def write (bytes : Bytes n) (index : Fin n) := bytes.set index.val 1 index.isLt

theorem write_refines (facts : Store n) (index : Fin n) :
    write (encode facts) index = encode (facts.set index.val true index.isLt) := by
  apply Vector.ext
  intro query bounded
  simp [write,encode,Vector.getElem_set]
  split <;> simp_all

/-- Fixnum indices are admitted only when the actual fact range fits the chosen
payload bound. No host overflow behavior is inferred. -/
def Fits (limit n : Nat) := n ≤ limit

theorem index_fits (fits : Fits limit n) (index : Fin n) : index.val < limit := Nat.lt_of_lt_of_le index.isLt fits

structure Profile where
  literals : Nat
  reads : Nat
  joins : Nat

def profile : Expr n → Profile
  | .literal _ => ⟨1,0,0⟩
  | .read _ => ⟨0,1,0⟩
  | .both left right | .either left right =>
    let l := profile left
    let r := profile right
    ⟨l.literals+r.literals,l.reads+r.reads,1+l.joins+r.joins⟩

theorem node_partition (expression : Expr n) :
    (profile expression).literals + (profile expression).reads + (profile expression).joins = nodes expression := by
  induction expression <;> simp_all [profile,nodes] <;> omega

structure Dominates (small large : Stats) : Prop where
  pops : small.pops ≤ large.pops
  evaluations : small.evaluations ≤ large.evaluations
  nodes : small.nodes ≤ large.nodes
  writes : small.writes ≤ large.writes
  pushes : small.pushes ≤ large.pushes

def ceiling (plan : Plan n) : Stats :=
  ⟨n+plan.edgeCount,n+plan.edgeCount,(n+plan.edgeCount)*plan.maxNodes,n,plan.edgeCount⟩

theorem actual_ceiling (plan : Plan n) : Dominates (ChunkedClosure.close plan).stats (ceiling plan) := by
  rw [ChunkedClosure.close_stats]
  have pops : (fastClose plan).stats.pops ≤ n+plan.edgeCount := by rw [plan.edgeCount_eq]; exact fast_pop_bound plan
  have pushes := (fastClose plan).pushes_bound
  have normalized : credit plan.degree (values (Vector.replicate n false)) = total plan.degree := by
    unfold credit
    congr 1
    funext index
    simp [values]
  rw [normalized,← plan.edgeCount_eq] at pushes
  exact ⟨pops,Nat.le_trans (fastClose plan).evaluations_bound pops,
    Nat.le_trans (fastClose plan).nodes_bound (Nat.mul_le_mul_right _ (Nat.le_trans (fastClose plan).evaluations_bound pops)),
    Nat.le_trans (fastClose plan).writes_bound (Nat.sub_le _ _),pushes⟩

/-- Target choices. 'owned' means exclusive scratch storage during solving;
'chunked' shares immutable watcher lists; 'scalar' forbids heap result pairs in
the evaluator. These are implementation premises, not facts about Lean RC. -/
structure Representation where
  owned : Bool := true
  chunked : Bool := true
  scalar : Bool := true
  snapshot : Bool := true

structure Layout where
  wordBytes : Nat
  positive : 0 < wordBytes
  vectorHeader : Nat
  bytesHeader : Nat
  pairWords : Nat
  descriptorWords : Nat
  metadataWords : Nat := 0

/-- Rounded payload words; headers and alignment are explicit target parameters. -/
def Layout.byteWords (layout : Layout) (bytes : Nat) := (bytes+layout.wordBytes-1)/layout.wordBytes

/-- Cumulative requested words, not peak live words or measured allocation.
Input AST storage is charged separately; this cold setup creates private
compiled descriptors, reverse lists and one scratch bytevector. -/
def setupWords (layout : Layout) (n edgeCount syntaxNodes : Nat) :=
  layout.metadataWords + 3*layout.vectorHeader + 3*n + layout.bytesHeader + layout.byteWords n +
    layout.pairWords*edgeCount + layout.descriptorWords*syntaxNodes

def queueCells (representation : Representation) (n : Nat) (stats : Stats) :=
  n + if representation.chunked then stats.writes else stats.pushes

def solveWords (layout : Layout) (representation : Representation) (n : Nat) (stats : Stats) :=
  layout.pairWords * queueCells representation n stats +
    (if representation.owned then 0 else (layout.bytesHeader+layout.byteWords n)*stats.writes) +
    (if representation.scalar then 0 else layout.pairWords*stats.nodes) +
    (if representation.snapshot then layout.bytesHeader+layout.byteWords n else 0)

theorem solveWords_mono (layout : Layout) (representation : Representation) (bound : Dominates small large) :
    solveWords layout representation n small ≤ solveWords layout representation n large := by
  have queue : queueCells representation n small ≤ queueCells representation n large := by
    unfold queueCells
    cases representation.chunked <;> simp_all only [Bool.false_eq_true,ite_false,ite_true] <;>
      exact Nat.add_le_add_left (by first | exact bound.pushes | exact bound.writes) _
  apply Nat.add_le_add_right
  apply Nat.add_le_add
  · apply Nat.add_le_add
    · exact Nat.mul_le_mul_left _ queue
    · cases representation.owned <;> simp only [Bool.false_eq_true,ite_false,ite_true]
      · exact Nat.mul_le_mul_left _ bound.writes
      · exact Nat.le_refl _
  · cases representation.scalar <;> simp only [Bool.false_eq_true,ite_false,ite_true]
    · exact Nat.mul_le_mul_left _ bound.nodes
    · exact Nat.le_refl _

theorem allocation_bound (plan : Plan n) (layout : Layout) (representation : Representation) :
    solveWords layout representation n (ChunkedClosure.close plan).stats ≤
      solveWords layout representation n (ceiling plan) :=
  solveWords_mono _ _ (actual_ceiling plan)

theorem owned_chunked_allocation (plan : Plan n) (layout : Layout) (snapshot : Bool) :
    solveWords layout ⟨true,true,true,snapshot⟩ n (ChunkedClosure.close plan).stats ≤
      layout.pairWords*(n+n) + (if snapshot then layout.bytesHeader+layout.byteWords n else 0) := by
  simpa [solveWords,queueCells,ceiling] using allocation_bound plan layout ⟨true,true,true,snapshot⟩

/-- Conservative primitive counts include representation access, queue scanning,
frame normalization and length traversals; they are not CPU instructions. -/
structure Primitives where
  reads : Nat
  writes : Nat
  branches : Nat
  pairs : Nat

def primitives (representation : Representation) (n : Nat) (stats : Stats) : Primitives :=
  ⟨3*stats.pops+3*stats.evaluations+4*stats.nodes+stats.pushes+6*stats.writes+1,
   stats.writes,
   3*stats.pops+stats.nodes+stats.writes+1,
   queueCells representation n stats⟩

structure Prices where
  read : Nat
  write : Nat
  branch : Nat
  allocateWord : Nat

def charge (prices : Prices) (layout : Layout) (representation : Representation) (n : Nat) (stats : Stats) :=
  let operations := primitives representation n stats
  prices.read*operations.reads + prices.write*operations.writes + prices.branch*operations.branches +
    prices.allocateWord*solveWords layout representation n stats

theorem charge_mono (prices : Prices) (layout : Layout) (representation : Representation) (bound : Dominates small large) :
    charge prices layout representation n small ≤ charge prices layout representation n large := by
  have evaluated := bound.evaluations
  have visited := bound.nodes
  have scheduled := bound.pushes
  have written := bound.writes
  have reads : (primitives representation n small).reads ≤ (primitives representation n large).reads := by
    dsimp only [primitives]
    have := Nat.mul_le_mul_left 3 bound.pops
    have := Nat.mul_le_mul_left 3 bound.evaluations
    have := Nat.mul_le_mul_left 4 bound.nodes
    have := Nat.mul_le_mul_left 6 bound.writes
    omega
  have branches : (primitives representation n small).branches ≤ (primitives representation n large).branches := by
    dsimp only [primitives]
    have := Nat.mul_le_mul_left 3 bound.pops
    omega
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ reads)
    (Nat.mul_le_mul_left _ bound.writes)) (Nat.mul_le_mul_left _ branches))
    (Nat.mul_le_mul_left _ (solveWords_mono layout representation bound))

theorem backend_bound (plan : Plan n) (prices : Prices) (layout : Layout) (representation : Representation) :
    charge prices layout representation n (ChunkedClosure.close plan).stats ≤
      charge prices layout representation n (ceiling plan) := charge_mono _ _ _ (actual_ceiling plan)
end LeanPoo.Functional.ClosureCosts
