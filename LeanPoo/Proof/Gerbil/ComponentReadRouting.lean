import Std

namespace ComponentReadRouting

inductive Route where
  | localRead
  | predecessor
  deriving DecidableEq, Repr

def listRoute [BEq K] (members reads : List K) (key : K) : Option Route :=
  if reads.contains key then
    some (if members.contains key then .localRead else .predecessor)
  else none

def insertKeys [BEq K] [Hashable K] (route : K → R) :
    List K → Std.HashMap K R → Std.HashMap K R
  | [], table => table
  | key :: rest, table => (insertKeys route rest table).insert key (route key)

theorem insertKeys_lookup [BEq K] [LawfulBEq K] [Hashable K]
    (route : K → R) (keys : List K) (table : Std.HashMap K R) (key : K) :
    (insertKeys route keys table)[key]? =
      if keys.contains key then some (route key) else table[key]? := by
  induction keys with
  | nil => simp [insertKeys]
  | cons k rest ih =>
    rw [insertKeys, Std.HashMap.getElem?_insert, ih]
    by_cases eq : k = key
    · subst k; simp
    · simp [eq, Ne.symm eq]

def memberIndex [BEq K] [Hashable K] (members : List K) : Std.HashMap K Unit :=
  insertKeys (fun _ => ()) members ∅

-- The member index is built once per group. Each row is compiled by one
-- group-index lookup per declared read. Rows store a route, never a value.
def rowIndex [BEq K] [Hashable K] (members : Std.HashMap K Unit) (reads : List K) :
    Std.HashMap K Route :=
  insertKeys (fun k => if members[k]?.isSome then .localRead else .predecessor) reads ∅

theorem indexed_lookup [BEq K] [LawfulBEq K] [Hashable K]
    (members reads : List K) (key : K) :
    (rowIndex (memberIndex members) reads)[key]? = listRoute members reads key := by
  unfold rowIndex memberIndex listRoute
  rw [insertKeys_lookup, Std.HashMap.getElem?_empty]
  split
  · rw [insertKeys_lookup, Std.HashMap.getElem?_empty]
    split <;> rfl
  · rfl

inductive Run (S E A : Type) where
  | ok (value : A) (state : S)
  | refused (reason : E) (state : S)
  deriving DecidableEq

def Run.bind (v : Run S E A) (next : A → S → Run S E B) : Run S E B :=
  match v with
  | .ok a s => next a s
  | .refused e s => .refused e s

def dispatch (route : Option Route) (undeclared : K → S → Run S E V)
    (localRead predecessor : K → S → Run S E V) (key : K) (s : S) :
    Run S E V :=
  match route with
  | none => undeclared key s
  | some .localRead => localRead key s
  | some .predecessor => predecessor key s

-- Check the authority at the point of each callback read, since the
-- preceding callback may have edited the source or the active index route.
def indexedRead [BEq K] [Hashable K]
    (row : Std.HashMap K Route) (liveLists : S → List K × List K)
    (valid : S → Bool) (undeclared localRead predecessor : K → S → Run S E V)
    (key : K) (s : S) : Run S E V :=
  let route := if valid s then row[key]? else listRoute (liveLists s).1 (liveLists s).2 key
  dispatch route undeclared localRead predecessor key s

-- Equality of the entire callback function allows arbitrary read order,
-- branching, repetition, failures and state changes. Explicit before/after
-- guards stay in the pipeline; this proves neither guard redundant.
theorem guarded_pipeline_exact [BEq K] [LawfulBEq K] [Hashable K]
    (members reads : List K) (liveLists : S → List K × List K) (valid : S → Bool)
    (current : ∀ s, valid s = true → liveLists s = (members, reads))
    (undeclared localRead predecessor : K → S → Run S E V)
    (before : S → Run S E Unit)
    (evaluate : (K → S → Run S E V) → S → Run S E A)
    (after : A → S → Run S E B) (s : S) :
    (before s).bind (fun _ st =>
      (evaluate (indexedRead (rowIndex (memberIndex members) reads) liveLists valid
        undeclared localRead predecessor) st).bind after) =
    (before s).bind (fun _ st =>
      (evaluate (fun key t => dispatch (listRoute (liveLists t).1 (liveLists t).2 key)
        undeclared localRead predecessor key t) st).bind after) := by
  congr 1
  funext _ st
  congr 2
  funext key t
  unfold indexedRead
  cases h : valid t
  · rfl
  · simp [indexed_lookup, current t h]

-- In Scheme .@ is .get. Do not turn that observed read into a bare
-- field load: it may refuse or register an observation. Route only AFTER
-- the original read; the selector must be valid in the resulting state.
def observedRead [BEq K] [Hashable K]
    (getLists : K → S → Run S E (List K × List K))
    (choose : (List K × List K) → S → Option Route)
    (undeclared localRead predecessor : K → S → Run S E V)
    (key : K) (s : S) : Run S E V :=
  (getLists key s).bind fun lists t =>
    dispatch (choose lists t) undeclared localRead predecessor key t

theorem observed_adaptive_read_exact [BEq K] [LawfulBEq K] [Hashable K]
    (members reads : List K) (useIndex : Bool)
    (getLists : K → S → Run S E (List K × List K))
    (valid : (List K × List K) → S → Bool)
    (current : ∀ lists t, valid lists t = true → lists = (members, reads))
    (undeclared localRead predecessor : K → S → Run S E V) (key : K) (s : S) :
    observedRead getLists (fun lists t =>
      if useIndex && valid lists t then (rowIndex (memberIndex members) reads)[key]?
      else listRoute lists.1 lists.2 key)
      undeclared localRead predecessor key s =
    observedRead getLists (fun lists _ => listRoute lists.1 lists.2 key)
      undeclared localRead predecessor key s := by
  unfold observedRead
  cases getLists key s with
  | refused => rfl
  | ok lists t =>
    simp only [Run.bind]
    by_cases h : useIndex && valid lists t
    · have hv : valid lists t = true := by
        cases hl : valid lists t <;> simp_all
      simp [indexed_lookup, current lists t hv]
    · simp [h]

-- Worst placement is witnessed, not just bounded: the requested key is at
-- the end of both lists (or has to scan a whole list for a miss).
def inspected [BEq K] (key : K) : List K → Nat
  | [] => 0
  | a :: rest => if a == key then 1 else 1 + inspected key rest

theorem scan_to_last [BEq K] [LawfulBEq K] (key : K) (xs : List K)
    (absent : key ∉ xs) : inspected key (xs ++ [key]) = xs.length + 1 := by
  induction xs with
  | nil => simp [inspected]
  | cons x rest ih =>
    have h : x ≠ key := fun eq => absent (eq ▸ List.mem_cons_self)
    have h' : key ∉ rest := fun hm => absent (List.mem_cons_of_mem x hm)
    simp [inspected, h, ih h', Nat.add_comm, Nat.add_left_comm]

-- Counts semantic list inspections vs index operations, not hash-table
-- bucket probes, allocations, guard calls or wall time.
def compiledOperations (m d q : Nat) := m + 2 * d + q
def repeatedTailInspections (m d q : Nat) := q * (m + d)

theorem large_group_repeated_reads (m d q : Nat)
    (hm : 4 ≤ m) (hd : 1 ≤ d) (hq : 2 ≤ q) :
    compiledOperations m d q < repeatedTailInspections m d q := by
  unfold compiledOperations repeatedTailInspections
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hq
  rw [Nat.add_mul]
  have : n ≤ n * (m + d) := by
    simpa using Nat.mul_le_mul_left n (show 1 ≤ m + d by omega)
  omega

-- A stale classification is observable. The guarded lane falls back to
-- the predecessor, while forcing the old local classification is wrong.
example :
    indexedRead (rowIndex (memberIndex [1]) [1]) (fun (_ : Unit) => ([], [1]))
      (fun _ => false) (fun _ _ => .refused () ()) (fun _ _ => .ok 10 ())
      (fun _ _ => .ok 20 ()) 1 () = .ok 20 () := by decide +kernel

example :
    indexedRead (rowIndex (memberIndex [1]) [1]) (fun (_ : Unit) => ([], [1]))
      (fun _ => true) (fun _ _ => .refused () ()) (fun _ _ => .ok 10 ())
      (fun _ _ => .ok 20 ()) 1 () = .ok 10 () := by
    simp [indexedRead, indexed_lookup, listRoute, dispatch]

-- An observed getter can refuse before the classifier even for a
-- precompiled local read; an undeclared read never reaches a provider.
example :
    observedRead
      (fun (_ : Nat) (_ : Nat) => (.refused 7 3 : Run Nat Nat (List Nat × List Nat)))
      (fun _ _ => some .localRead) (fun _ s => .refused 8 s)
      (fun _ s => .ok 10 s) (fun _ s => .ok 20 s) 1 0 =
    .refused 7 3 := rfl

example :
    observedRead
      (fun (_ : Nat) s => (.ok ([1], [1]) (s + 1) : Run Nat Nat (List Nat × List Nat)))
      (fun lists _ => listRoute lists.1 lists.2 2)
      (fun _ s => .refused 8 s) (fun _ s => .ok 10 s) (fun _ s => .ok 20 s) 2 0 =
    .refused 8 1 := rfl

#print axioms indexed_lookup
#print axioms guarded_pipeline_exact
#print axioms observed_adaptive_read_exact
#print axioms large_group_repeated_reads

end ComponentReadRouting
