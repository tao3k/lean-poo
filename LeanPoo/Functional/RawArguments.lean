import LeanPoo.Functional.KeywordCoverage

/-! Value-sensitive raw argument coverage in the existing FunctionSignature
protocol. This advances the article's hypothetical type system. Origin admission
is explicit: data requires subtype evidence, protocol markers require their own
Keyword/Exactly/Enum evidence. No origin is replaced with a universal Type.
The finite checker models the request-local traversal, not host memo/GC costs. -/
namespace LeanPoo.Functional.FunctionSignature

/-- Every successful spelling consumes positional data in order and each supplied
key once, with optional key/rest escapes. Payload Types remain at their origins.
Literal-token payloads are conservatively included as ordinary value origins. -/
inductive RawSpelling : List Ty → List (Key × Ty) → List (ArgumentToken Key Ty) → Prop where
  | nil : RawSpelling [] [] []
  | plain : RawSpelling ps ks tail → RawSpelling (ty :: ps) ks (.value ty :: tail)
  | escaped : RawSpelling ps ks tail → RawSpelling (ty :: ps) ks (.keyEscape :: .value ty :: tail)
  | keyed (found : ks[index]? = some (key, ty)) : RawSpelling ps (ks.eraseIdx index) tail →
      RawSpelling ps ks (.keyword key :: .value ty :: tail)
  | rest (ps) : RawSpelling ps [] (.restEscape :: ps.map .value)

/-- Decoder bounds prune only impossible suffixes, before imposing slot evidence. -/
def rawFeasible (ps : List Ty) (ks : List (Key × Ty)) (size : Nat) : Bool :=
  decide (ps.length + 2 * ks.length ≤ size ∧ size ≤ 2 * ps.length + 2 * ks.length + 1)

/-- The origin grammar has the same lower and upper raw bounds as the decoder. -/
theorem RawSpelling.bounds (trace : RawSpelling ps ks tokens) :
    ps.length + 2 * ks.length ≤ tokens.length ∧
    tokens.length ≤ 2 * ps.length + 2 * ks.length + 1 := by
  induction trace with
  | nil => simp
  | plain trace ih => simp only [List.length_cons] at *; omega
  | escaped trace ih => simp only [List.length_cons] at *; omega
  | keyed found trace ih =>
    obtain ⟨inside, _⟩ := List.getElem?_eq_some_iff.mp found
    rw [List.length_eraseIdx_of_lt inside] at ih
    simp only [List.length_cons]
    omega
  | rest ps => simp; omega

/-- Feasibility never discards an actual origin derivation. -/
theorem RawSpelling.feasible (trace : RawSpelling ps ks tokens) :
    rawFeasible ps ks tokens.length = true := decide_eq_true trace.bounds

/-- Exact supplied slots: omitted defaults and absent optional fields are absent. -/
def rawSlots (admit : Nat → ArgumentToken Key Ty → Bool) : Nat → List (ArgumentToken Key Ty) → Bool
  | _, [] => true
  | index, origin :: rest => admit index origin && rawSlots admit (index + 1) rest

/-- Request-local state recursion. Every recursive transition consumes a decoded
value/key and raw tokens. Fuel exhaustion refuses a feasible state; it never
returns a partial success. Scheme separately enforces its shared work quota. -/
def rawCovers (admit : Nat → ArgumentToken Key Ty → Bool) :
    Nat → List Ty → List (Key × Ty) → Nat → Nat → Bool
  | 0, ps, ks, _, size => !rawFeasible ps ks size
  | fuel + 1, ps, ks, index, size =>
    if !rawFeasible ps ks size then true else
      (match ps with
       | [] => true
       | ty :: tail =>
         if decide (1 ≤ size) && rawFeasible tail ks (size - 1) then
           admit index (.value ty) && rawCovers admit fuel tail ks (index + 1) (size - 1)
         else true) &&
      (match ps with
       | [] => true
       | ty :: tail =>
         if decide (2 ≤ size) && rawFeasible tail ks (size - 2) then
           admit index .keyEscape && admit (index + 1) (.value ty) &&
             rawCovers admit fuel tail ks (index + 2) (size - 2)
         else true) &&
      (List.range ks.length).all (fun ordinal =>
        match ks[ordinal]? with
        | none => false
        | some (key, ty) =>
          if decide (2 ≤ size) && rawFeasible ps (ks.eraseIdx ordinal) (size - 2) then
            admit index (.keyword key) && admit (index + 1) (.value ty) &&
              rawCovers admit fuel ps (ks.eraseIdx ordinal) (index + 2) (size - 2)
          else true) &&
      (if ks.isEmpty && decide (size = ps.length + 1) then
        rawSlots admit index (.restEscape :: ps.map .value) else true)

/-- Every checked region admits EVERY grammar spelling, including all supplied
keyword orders, non-minimum escaped rows and trailing rest escape. The theorem
is universal in the slot admission relation and arbitrary payload Types. -/
theorem rawCovers_sound (admit : Nat → ArgumentToken Key Ty → Bool) (fuel : Nat)
    (trace : RawSpelling ps ks tokens)
    (checked : rawCovers admit fuel ps ks index tokens.length = true) :
    rawSlots admit index tokens = true := by
  have sub_two (n : Nat) : n + 1 + 1 - 2 = n := by omega
  induction fuel generalizing ps ks tokens index with
  | zero => simp [rawCovers, trace.feasible] at checked
  | succ fuel ih =>
    simp only [rawCovers, trace.feasible, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      Bool.and_eq_true] at checked
    obtain ⟨⟨⟨plain, escaped⟩, keyed⟩, rest⟩ := checked
    cases trace with
    | nil => rfl
    | plain tail =>
      have suffix := tail.feasible
      simp only [List.length_cons, Nat.add_sub_cancel] at plain
      simp [suffix] at plain
      simp only [rawSlots, Bool.and_eq_true]
      exact ⟨plain.1, ih tail plain.2⟩
    | escaped tail =>
      have suffix := tail.feasible
      simp [List.length_cons, sub_two, suffix] at escaped
      simp only [rawSlots, Bool.and_eq_true]
      exact ⟨escaped.1.1, escaped.1.2, by
        simpa [Nat.add_assoc] using ih tail escaped.2⟩
    | keyed found tail =>
      obtain ⟨inside, _⟩ := List.getElem?_eq_some_iff.mp found
      have selected := List.all_eq_true.mp keyed _ (List.mem_range.mpr inside)
      have suffix := tail.feasible
      simp [found, List.length_cons, sub_two, suffix] at selected
      simp only [rawSlots, Bool.and_eq_true]
      exact ⟨selected.1.1, selected.1.2, by simpa [Nat.add_assoc] using ih tail selected.2⟩
    | rest ps =>
      simpa using rest

/-- No opaque recognizer is assumed: the caller supplies the semantic meaning of
an accepted origin. This lifts every slot decision to its stated semantic law. -/
theorem rawSlots_sound (admit : Nat → ArgumentToken Key Ty → Bool)
    (law : Nat → ArgumentToken Key Ty → Prop)
    (valid : ∀ index origin, admit index origin = true → law index origin)
    (tokens : List (ArgumentToken Key Ty)) (index : Nat)
    (checked : rawSlots admit index tokens = true) :
    ∀ ordinal origin, tokens[ordinal]? = some origin → law (index + ordinal) origin := by
  induction tokens generalizing index with
  | nil => simp
  | cons head tail ih =>
    simp only [rawSlots, Bool.and_eq_true] at checked
    intro ordinal origin found
    cases ordinal with
    | zero => simp at found; subst origin; simpa using valid index head checked.1
    | succ ordinal =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (index + 1) checked.2 ordinal origin found

/-- Explicit finite Enum membership for markers. It is not an inferred top Type. -/
def enumMarker [DecidableEq Key] (allowed : List (ArgumentToken Key Unit))
    (marker : ArgumentToken Key Unit) : Bool := decide (marker ∈ allowed)

/-- Exactly is the singleton special case of Enum's extensional marker law. -/
theorem enumMarker_sound [DecidableEq Key] (allowed : List (ArgumentToken Key Unit)) (marker)
    (checked : enumMarker allowed marker = true) : marker ∈ allowed := of_decide_eq_true checked

/-- Keyword admits keyword tokens only, excluding both escape markers and data. -/
def keywordMarker : ArgumentToken Key Ty → Bool
  | .keyword _ => true
  | _ => false

/-- A Keyword certificate cannot stand in for an escape or ordinary payload. -/
theorem keywordMarker_sound (token : ArgumentToken Key Ty) (checked : keywordMarker token = true) :
    ∃ key, token = .keyword key := by
  cases token <;> simp_all [keywordMarker]

/-- Beyond every fixed prefix, the conservative stationary envelope requires
explicit evidence for every possible origin at every supplied source slot. -/
def stationaryRaw (admit : Nat → ArgumentToken Key Ty → Bool)
    (origins : List (ArgumentToken Key Ty)) (size : Nat) : Bool :=
  (List.range size).all (fun index => origins.all (admit index))

/-- The stationary rule preserves per-origin evidence at arbitrarily large raw
arities; no origin is erased into Any. Its envelope-completeness premise remains
explicit, independently of the finite prefix traversal. -/
theorem stationaryRaw_sound (admit : Nat → ArgumentToken Key Ty → Bool)
    (origins : List (ArgumentToken Key Ty)) (size : Nat)
    (checked : stationaryRaw admit origins size = true)
    (index : Nat) (inside : index < size) (origin) (member : origin ∈ origins) :
    admit index origin = true :=
  List.all_eq_true.mp (List.all_eq_true.mp checked index (List.mem_range.mpr inside)) origin member

/-- Ordinary decoding excludes outer keyword and both escape tokens. Values
inside a container retain their ordinary outer carrier. -/
def ordinaryToken : ArgumentToken Key Value → Bool
  | .value _ => true
  | _ => false

/-- Exactly/Enum restriction is extensional filtering of their finite literals;
no universal Type or opaque recognizer is introduced by this operation. -/
def ordinaryLiterals (values : List (ArgumentToken Key Value)) := values.filter ordinaryToken

/-- Finite literal restriction preserves exactly the ordinary inhabitants. -/
theorem ordinaryLiterals_mem (values : List (ArgumentToken Key Value)) (token) :
    token ∈ ordinaryLiterals values ↔ token ∈ values ∧ ∃ value, token = .value value := by
  cases token <;> simp [ordinaryLiterals, ordinaryToken]

/-- A lone protocol token cannot supply the same token as one positional value.
Such a target input needs an escape; its apparent direct arity cell is empty. -/
theorem protocol_singleton_not_data [DecidableEq Key] (token : ArgumentToken Key Value)
    (protocol : ordinaryToken token = false) :
    decodeKeyword [token] ≠ some (Call.mk [token] []) := by
  cases token <;> simp_all [ordinaryToken, decodeKeyword]

/-- Saturate only beyond the exact finite prefix. The sentinel denotes a lower
bound on actual length, not a sample at which all origins are mixed together. -/
def rawCounter (limit count : Nat) : Nat := min limit count

/-- Every one/two-token transition commutes with counter saturation. -/
theorem rawCounter_add (limit count step : Nat) :
    rawCounter limit (count + step) = rawCounter limit (rawCounter limit count + step) := by
  unfold rawCounter; omega

/-- The product has independent limits and token/value increments. A Boolean
keyword payload may occupy the second raw slot without broadening the first. -/
theorem rawCounter_product (positions raw positionLimit rawLimit values tokens : Nat) :
    (rawCounter positionLimit (positions + values), rawCounter rawLimit (raw + tokens)) =
    (rawCounter positionLimit (rawCounter positionLimit positions + values),
     rawCounter rawLimit (rawCounter rawLimit raw + tokens)) := by
  rw [rawCounter_add, rawCounter_add rawLimit]

/-- A decoded tail region checks ALL raw arity cells up to the raw sentinel,
not the finite upper bound of its shortest decoded representative. -/
def rawTailCounts (rawLimit decodedLimit keyCount : Nat) : List Nat :=
  (List.range (rawLimit + 1)).filter (fun raw => decide (min rawLimit (decodedLimit + 2 * keyCount) ≤ raw))

/-- Every physical raw arity of every longer decoded rest call has a checked cell.
The decoder's lower bound is sufficient; no finite upper tail horizon is assumed. -/
theorem rawTailCounts_complete (rawLimit decodedLimit decoded keys raw : Nat)
    (tail : decodedLimit ≤ decoded) (lower : decoded + 2 * keys ≤ raw) :
    rawCounter rawLimit raw ∈ rawTailCounts rawLimit decodedLimit keys := by
  apply List.mem_filter.mpr
  refine ⟨List.mem_range.mpr (by unfold rawCounter; omega), ?_⟩
  apply decide_eq_true
  unfold rawCounter
  omega

/-- A saturated terminal counter means every actual length at or above its limit. -/
theorem rawCounter_tail (limit count : Nat) : rawCounter limit count = limit ↔ limit ≤ count := by
  unfold rawCounter; omega

/-- Below saturation the counter retains the exact physical position. -/
theorem rawCounter_exact (limit count : Nat) (small : rawCounter limit count < limit) :
    rawCounter limit count = count := by unfold rawCounter at *; omega

/-- Source and target input lookup keep their positional relation after either
counter saturates. Even the second slot of a two-token prefix retains its law. -/
theorem inputAt_rawCounter (signature : TypedSignature Key Ty) (limit index step : Nat)
    (bound : (signature.inputs ++ signature.optional).length ≤ limit) :
    signature.inputAt (rawCounter limit index + step) = signature.inputAt (index + step) := by
  by_cases small : index ≤ limit
  · simp [rawCounter, Nat.min_eq_right small]
  · rw [inputAt_tail signature _ (by unfold rawCounter; omega),
        inputAt_tail signature _ (by omega)]

/-- One complete graph transition retains the ordered origin labels it consumes.
State may be the product of decoded position, key mask, raw offset and parser mode. -/
structure RawTransition (State Origin : Type) where
  source : State
  target : State
  origins : List Origin
  deriving Repr

/-- Finite accepting traces may revisit a state arbitrarily many times. This
relation imposes no sampling horizon on the length of a rest tail. -/
inductive RawGraphPath (edges : List (RawTransition State Origin)) :
    State → State → List (RawTransition State Origin) → Prop where
  | done (state) : RawGraphPath edges state state []
  | step (edge) (inside : edge ∈ edges) (tail : RawGraphPath edges edge.target finish rest) :
      RawGraphPath edges edge.source finish (edge :: rest)

/-- Validate a backwards closure certificate and every edge into that closure.
Endpoints must be live, and no predecessor of a live state may be omitted. This
is checked even when the initial state is claimed to have an empty language. -/
def rawGraphCertificate [DecidableEq State] (edges : List (RawTransition State Origin))
    (endings live : List State) (admit : State → Origin → Bool) : Bool :=
  endings.all (fun state => decide (state ∈ live)) &&
  edges.all (fun edge => if edge.target ∈ live then
    decide (edge.source ∈ live) && edge.origins.all (admit edge.source) else true)

/-- A valid closure certifies every accepting trace, including unbounded repeated
cycles. An uncompleted/provisional visited set cannot satisfy this theorem. -/
theorem rawGraphPath_sound [DecidableEq State] (edges : List (RawTransition State Origin))
    (endings live : List State) (admit : State → Origin → Bool)
    (certificate : rawGraphCertificate edges endings live admit = true)
    (path : RawGraphPath edges start finish trace) (finishes : finish ∈ live) :
    start ∈ live ∧ trace.all (fun edge => edge.origins.all (admit edge.source)) = true := by
  simp only [rawGraphCertificate, Bool.and_eq_true] at certificate
  induction path with
  | done state => exact ⟨finishes, rfl⟩
  | step edge inside tail ih =>
    have suffix := ih finishes
    have valid := List.all_eq_true.mp certificate.2 edge inside
    simp only [suffix.1, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at valid
    exact ⟨valid.1, by simpa only [List.all_cons, Bool.and_eq_true] using And.intro valid.2 suffix.2⟩

/-- Endings are part of the certificate, not an assumed complete memo table. -/
theorem rawGraphCertificate_sound [DecidableEq State] (edges : List (RawTransition State Origin))
    (endings live : List State) (admit : State → Origin → Bool)
    (certificate : rawGraphCertificate edges endings live admit = true)
    (path : RawGraphPath edges start finish trace) (ending : finish ∈ endings) :
    start ∈ live ∧ trace.all (fun edge => edge.origins.all (admit edge.source)) = true := by
  have endpoints := (Bool.and_eq_true_iff.mp certificate).1
  exact rawGraphPath_sound edges endings live admit certificate path
    (of_decide_eq_true (List.all_eq_true.mp endpoints finish ending))

/-- Empty initial regions may skip source/output requirements only after their
full closure certificate is validated. Nonempty regions require a real clause. -/
def rawRegionCovers [DecidableEq State] (edges : List (RawTransition State Origin))
    (endings live : List State) (initial : State) (hasSource : Bool)
    (admit : State → Origin → Bool) : Bool :=
  rawGraphCertificate edges endings live admit && (!(decide (initial ∈ live)) || hasSource)

/-- Every actual successful trace forces a selected source and preserves the
per-position origin law. A dead arity region cannot hide a live bad output case. -/
theorem rawRegionCovers_sound [DecidableEq State] (edges : List (RawTransition State Origin))
    (endings live : List State) (initial : State) (hasSource : Bool) (admit : State → Origin → Bool)
    (checked : rawRegionCovers edges endings live initial hasSource admit = true)
    (path : RawGraphPath edges initial finish trace) (ending : finish ∈ endings) :
    hasSource = true ∧ trace.all (fun edge => edge.origins.all (admit edge.source)) = true := by
  simp only [rawRegionCovers, Bool.and_eq_true] at checked
  have laws := rawGraphCertificate_sound edges endings live admit checked.1 path ending
  exact ⟨by simpa [laws.1] using checked.2, laws.2⟩

/-- The empty-region witness rules out ALL accepting traces, not merely traces
up to a chosen raw length. This also excludes cycles with a reachable exit. -/
theorem rawGraph_empty [DecidableEq State] (edges : List (RawTransition State Origin))
    (endings live : List State) (admit : State → Origin → Bool)
    (certificate : rawGraphCertificate edges endings live admit = true) (empty : initial ∉ live) :
    ∀ finish trace, finish ∈ endings → ¬RawGraphPath edges initial finish trace := by
  intro finish trace ending path
  exact empty (rawGraphCertificate_sound edges endings live admit certificate path ending).1

/-- One finite backwards sweep adds only actual predecessors of the current set.
The runtime uses a standard hash-table worklist and validates its final closure. -/
def rawPredecessors [DecidableEq State] (edges : List (RawTransition State Origin)) (live : List State) :=
  edges.foldl (fun known edge => if edge.target ∈ known ∧ edge.source ∉ known then edge.source :: known else known) live

/-- Controlled graph closure; a feasible unfinished closure is rejected by the
certificate below. Fuel never causes a provisional cyclic success. -/
def rawBackwards [DecidableEq State] (edges : List (RawTransition State Origin))
    (endings : List State) : Nat → List State
  | 0 => endings
  | fuel + 1 => rawPredecessors edges (rawBackwards edges endings fuel)

/-- Return a graph result only with an independently checked closure certificate.
Scheme's work exhaustion remains a typed refusal, not this Boolean false. -/
def rawGraphCheck [DecidableEq State] (fuel : Nat) (edges : List (RawTransition State Origin))
    (endings : List State) (initial : State) (hasSource : Bool) (admit : State → Origin → Bool) : Bool :=
  rawRegionCovers edges endings (rawBackwards edges endings fuel) initial hasSource admit

/-- Finite closure checking lifts to arbitrarily long rest traces. Concrete
product-graph completeness and validator interpretation remain explicit premises. -/
theorem rawGraphCheck_sound [DecidableEq State] (fuel : Nat) (edges : List (RawTransition State Origin))
    (endings : List State) (initial : State) (hasSource : Bool) (admit : State → Origin → Bool)
    (checked : rawGraphCheck fuel edges endings initial hasSource admit = true)
    (path : RawGraphPath edges initial finish trace) (ending : finish ∈ endings) :
    hasSource = true ∧ trace.all (fun edge => edge.origins.all (admit edge.source)) = true :=
  rawRegionCovers_sound edges endings _ initial hasSource admit checked path ending

end LeanPoo.Functional.FunctionSignature
