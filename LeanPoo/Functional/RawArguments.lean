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

end LeanPoo.Functional.FunctionSignature
