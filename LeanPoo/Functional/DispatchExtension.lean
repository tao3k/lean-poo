import LeanPoo.Object.MultimethodSemantics

/-! Negative assumptions on actual multi-argument generic functions.
Shape watches forbid all candidates; call watches forbid applicable methods
at the specified current arguments. Registration transactions inspect the
completed immutable candidate and never invoke method bodies or combine. -/
namespace LeanPoo.Functional.DispatchExtension
open Object
variable {Args Method Result : Type}

inductive Watch (Args : Type) where
  | shape (precedence : DispatchShape)
  | call (args : Args)

def Watch.precedence (generic : Multimethod Args Method Result) : Watch Args → DispatchShape
  | .shape order => order
  | .call args => generic.precedence args

variable {generic : Multimethod Args Method Result} {watch : Watch Args} {watches : List (Watch Args)}

def observed (generic : Multimethod Args Method Result) : Watch Args → Array Method
  | .shape shape => (generic.candidatesFor shape).map MethodCandidate.method
  | .call args => MethodCandidate.select (generic.candidatesFor (generic.precedence args)) args

def reference (generic : Multimethod Args Method Result) : Watch Args → List Method
  | .shape shape => (generic.index.reference (shape.map fun order => order.map Specializer.prototype ++ [.any])).map MethodCandidate.method
  | .call args => (generic.index.reference ((generic.precedence args).map fun order => order.map Specializer.prototype ++ [.any])).filterMap (MethodCandidate.selected args)

theorem observed_reference (generic : Multimethod Args Method Result) (watch : Watch Args) :
    (observed generic watch).toList = reference generic watch := by
  cases watch with
  | shape shape => simp only [observed, reference, Array.toList_map, generic.candidates_reference]
  | call args => rw [observed, MethodCandidate.select_reference, generic.candidates_reference]; rfl

def Absent (generic : Multimethod Args Method Result) (watch : Watch Args) : Prop :=
  (watch.precedence generic).length = generic.arity ∧ (observed generic watch).size = 0

instance (generic : Multimethod Args Method Result) (watch : Watch Args) : Decidable (Absent generic watch) :=
  inferInstanceAs (Decidable (_ ∧ _))

def AllAbsent (generic : Multimethod Args Method Result) (watches : List (Watch Args)) : Prop :=
  ∀ watch ∈ watches, Absent generic watch

structure Certificate (generic : Multimethod Args Method Result) (watches : List (Watch Args)) : Type where
  absent : AllAbsent generic watches

/-- Negative assumptions do not expire when only the candidate cache changes. -/
def Certificate.rebind (certificate : Certificate generic watches) (other : Multimethod Args Method Result)
    (arity : other.arity = generic.arity) (precedence : other.precedence = generic.precedence)
    (index : other.index = generic.index) : Certificate other watches := ⟨by
  intro watch member
  have absent := certificate.absent watch member
  cases watch <;> simpa [Absent, Watch.precedence, observed, Multimethod.candidatesFor,
    arity, precedence, index] using absent⟩

private theorem resolve_frame (generic : Multimethod Args Method Result) (args : Args)
    (candidates : Array (MethodCandidate Args Method)) (updated : Multimethod Args Method Result)
    (resolved : generic.resolve args = .ok (candidates, updated)) :
    updated.arity = generic.arity ∧ updated.precedence = generic.precedence ∧ updated.index = generic.index := by
  unfold Multimethod.resolve at resolved
  simp only [bind, Except.bind, pure, Except.pure, throw] at resolved
  repeat' first | contradiction | split at resolved
  all_goals cases resolved; exact ⟨rfl, rfl, rfl⟩

def Certificate.afterCall (certificate : Certificate generic watches) (args : Args)
    (result : Result) (updated : Multimethod Args Method Result)
    (called : generic.call args = .ok (result, updated)) : Certificate updated watches := by
  cases resolved : generic.resolve args with
  | error error => simp [Multimethod.call, resolved, bind, Except.bind] at called
  | ok pair =>
    rcases pair with ⟨candidates, next⟩
    have same : next = updated := by
      have pair : generic.combine (MethodCandidate.select candidates args) args = result ∧ next = updated := by
        simpa [Multimethod.call, resolved, bind, Except.bind, pure, Except.pure] using called
      exact pair.2
    subst updated
    obtain ⟨arity, precedence, index⟩ := resolve_frame generic args candidates next resolved
    exact certificate.rebind next arity precedence index

structure Invocation (generic : Multimethod Args Method Result) (watches : List (Watch Args)) (args : Args) where
  result : Result
  snapshot : Multimethod Args Method Result
  called : generic.call args = .ok (result, snapshot)
  certificate : Certificate snapshot watches

/-- Invoke normally and transfer the negative certificate through cache lookup,
touch and eviction without rerunning the negative checks. -/
def Certificate.invoke (certificate : Certificate generic watches) (args : Args) :
    Except MultimethodError (Invocation generic watches args) :=
  match called : generic.call args with
  | .error error => .error error
  | .ok (result, snapshot) => .ok ⟨result, snapshot, called, certificate.afterCall args result snapshot called⟩

inductive Violation (generic : Multimethod Args Method Result) (watch : Watch Args) : Type where
  | arity (different : (watch.precedence generic).length ≠ generic.arity)
  | method (same : (watch.precedence generic).length = generic.arity)
      (present : 0 < (observed generic watch).size)

theorem Violation.refutes (violation : Violation generic watch) : ¬ Absent generic watch := by
  intro absent
  cases violation with
  | arity different => exact different absent.1
  | method _ present => have empty := absent.2; omega

/-- Retain the actual first conflicting method without evaluating its body. -/
def Violation.firstMethod (violation : Violation generic watch) : Option Method :=
  match violation with
  | .arity _ => none
  | .method _ present => some ((observed generic watch)[0]'present)

/-- A reported conflict comes from the actual ordered tuple/filter specification. -/
theorem Violation.firstMethod_origin (violation : Violation generic watch) (method : Method)
    (selected : violation.firstMethod = some method) : method ∈ reference generic watch := by
  cases violation with
  | arity different => simp [firstMethod] at selected
  | method same present =>
    have equal : (observed generic watch)[0]'present = method := Option.some.inj selected
    rw [← observed_reference]
    rw [← equal]
    simpa using (Array.getElem_mem present)

structure Conflict (generic : Multimethod Args Method Result) (watches : List (Watch Args)) where
  watch : Watch Args
  earlier : List (Watch Args)
  later : List (Watch Args)
  split : watches = earlier ++ watch :: later
  prior : AllAbsent generic earlier
  violation : Violation generic watch

theorem Conflict.refutes (conflict : Conflict generic watches) : ¬ AllAbsent generic watches := by
  intro absent
  apply conflict.violation.refutes
  apply absent conflict.watch
  exact Eq.mpr (congrArg (fun ws : List (Watch Args) => conflict.watch ∈ ws) conflict.split) (by simp)

def check (generic : Multimethod Args Method Result) : (watches : List (Watch Args)) →
    Except (Conflict generic watches) (Certificate generic watches)
  | [] => .ok ⟨by intro watch member; simp at member⟩
  | watch :: rest =>
    if good : Absent generic watch then
      match check generic rest with
      | .ok certificate => .ok ⟨by
          intro query member
          rcases List.mem_cons.mp member with same | member
          · subst query; exact good
          · exact certificate.absent query member⟩
      | .error conflict => .error ⟨conflict.watch, watch :: conflict.earlier, conflict.later,
          congrArg (List.cons watch) conflict.split, by
            intro query member
            rcases List.mem_cons.mp member with same | member
            · subst query; exact good
            · exact conflict.prior query member,
          conflict.violation⟩
    else
      let violation : Violation generic watch :=
        if same : (watch.precedence generic).length = generic.arity then
          .method same (by
            have nonzero : (observed generic watch).size ≠ 0 := by
              intro empty; exact good ⟨same, empty⟩
            omega)
        else .arity same
      .error ⟨watch, [], rest, rfl, by intro query member; simp at member, violation⟩

theorem check_ok_iff (generic : Multimethod Args Method Result) (watches : List (Watch Args)) :
    (∃ certificate, check generic watches = .ok certificate) ↔ AllAbsent generic watches := by
  constructor
  · rintro ⟨certificate, _⟩; exact certificate.absent
  · intro absent
    cases checked : check generic watches with
    | ok certificate => exact ⟨certificate, rfl⟩
    | error conflict => exact False.elim (conflict.refutes absent)

/-- A structural absence covers every argument with this exact dispatch shape.
A call watch alone does not establish that stronger property. -/
theorem shape_covers_call (generic : Multimethod Args Method Result) (shape : DispatchShape)
    (absent : Absent generic (.shape shape)) (args : Args) (same : generic.precedence args = shape) :
    Absent generic (.call args) := by
  have empty : (generic.candidatesFor shape).size = 0 := by simpa [observed] using absent.2
  have candidates : generic.candidatesFor shape = #[] := Array.eq_empty_iff_size_eq_zero.mpr empty
  constructor
  · simpa [Watch.precedence, same] using absent.1
  · simp [observed, same, candidates, MethodCandidate.select]

inductive Edit (Args Method : Type) where
  | register (path : List Specializer) (method : Method)
  | contribute (path : List Specializer) (method : Method)
  | registerWhen (path : List Specializer) (predicate : Args → Bool) (method : Method)
  | erase (path : List Specializer)

def Edit.apply (edit : Edit Args Method) (generic : Multimethod Args Method Result) :
    Except MultimethodError (Multimethod Args Method Result) :=
  match edit with
  | .register path method => generic.register path method
  | .contribute path method => generic.contribute path method
  | .registerWhen path predicate method => generic.registerWhen path predicate method
  | .erase path => if path.length != generic.arity then .error (.arity generic.arity path.length)
    else .ok { generic with index := generic.index.alter path (fun _ => []), cache := {} }

theorem Edit.cache_empty (edit : Edit Args Method) (generic updated : Multimethod Args Method Result)
    (applied : edit.apply generic = .ok updated) : updated.cache = {} := by
  cases edit <;> simp only [Edit.apply, Multimethod.register, Multimethod.contribute, Multimethod.registerWhen] at applied
  all_goals split at applied <;> (try contradiction)
  all_goals cases applied; rfl

def patch (generic : Multimethod Args Method Result) : List (Edit Args Method) →
    Except MultimethodError (Multimethod Args Method Result)
  | [] => .ok generic
  | edit :: rest => do patch (← edit.apply generic) rest

theorem patch_sound (generic updated : Multimethod Args Method Result) (edits : List (Edit Args Method))
    (sound : generic.CacheSound) (applied : patch generic edits = .ok updated) : updated.CacheSound := by
  induction edits generalizing generic with
  | nil => cases applied; exact sound
  | cons edit rest ih =>
    cases step : edit.apply generic with
    | error error => simp [patch, step, bind, Except.bind] at applied
    | ok next =>
      have nextSound := next.cacheSound_of_empty (edit.cache_empty generic next step)
      exact ih next nextSound (by simpa [patch, step, bind, Except.bind] using applied)

structure Revision (generic : Multimethod Args Method Result) (watches : List (Watch Args)) (edits : List (Edit Args Method)) where
  snapshot : Multimethod Args Method Result
  applied : patch generic edits = .ok snapshot
  certificate : Certificate snapshot watches

inductive Failure (generic : Multimethod Args Method Result) (watches : List (Watch Args)) (edits : List (Edit Args Method)) where
  | registration (error : MultimethodError) (failed : patch generic edits = .error error)
  | introduced (candidate : Multimethod Args Method Result) (applied : patch generic edits = .ok candidate)
      (conflict : Conflict candidate watches)

def guard (generic : Multimethod Args Method Result) (watches : List (Watch Args))
    (_previous : Certificate generic watches) (edits : List (Edit Args Method)) :
    Except (Failure generic watches edits) (Revision generic watches edits) :=
  match applied : patch generic edits with
  | .error error => .error (.registration error applied)
  | .ok candidate => match check candidate watches with
    | .error conflict => .error (.introduced candidate applied conflict)
    | .ok certificate => .ok ⟨candidate, applied, certificate⟩

theorem guard_ok_iff (generic : Multimethod Args Method Result) (watches : List (Watch Args))
    (previous : Certificate generic watches) (edits : List (Edit Args Method)) :
    (∃ revision, guard generic watches previous edits = .ok revision) ↔
      ∃ candidate, patch generic edits = .ok candidate ∧ AllAbsent candidate watches := by
  constructor
  · rintro ⟨revision, _⟩; exact ⟨revision.snapshot, revision.applied, revision.certificate.absent⟩
  · rintro ⟨candidate, applied, absent⟩
    cases outcome : guard generic watches previous edits with
    | ok revision => exact ⟨revision, rfl⟩
    | error failure =>
      cases failure with
      | registration error failed => rw [applied] at failed; contradiction
      | introduced next nextApplied conflict =>
        have same : candidate = next := Except.ok.inj (applied.symm.trans nextApplied)
        subst next
        exact False.elim (conflict.refutes absent)

theorem Revision.cacheSound (revision : Revision generic watches edits) (sound : generic.CacheSound) :
    revision.snapshot.CacheSound := patch_sound generic revision.snapshot edits sound revision.applied

/-- Publish only an accepted revision; every refusal returns the old generic,
including its warm cache. The diagnostic still retains the completed candidate. -/
def publish (generic : Multimethod Args Method Result) (watches : List (Watch Args))
    (previous : Certificate generic watches) (edits : List (Edit Args Method)) :
    Except (Failure generic watches edits) Unit × Multimethod Args Method Result :=
  match guard generic watches previous edits with
  | .error failure => (.error failure, generic)
  | .ok revision => (.ok (), revision.snapshot)

theorem guard_registration_error (generic : Multimethod Args Method Result) (watches : List (Watch Args))
    (previous : Certificate generic watches) (edits : List (Edit Args Method)) (error : MultimethodError)
    (failed : patch generic edits = .error error) :
    ∃ failure, guard generic watches previous edits = .error failure := by
  unfold guard
  split
  · exact ⟨_, rfl⟩
  · rename_i candidate applied
    rw [failed] at applied
    contradiction

theorem publish_refused (generic : Multimethod Args Method Result) (watches : List (Watch Args))
    (previous : Certificate generic watches) (edits : List (Edit Args Method)) (failure : Failure generic watches edits)
    (refused : guard generic watches previous edits = .error failure) :
    publish generic watches previous edits = (.error failure, generic) := by simp [publish, refused]

end LeanPoo.Functional.DispatchExtension
