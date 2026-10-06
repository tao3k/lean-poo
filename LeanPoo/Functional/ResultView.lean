import LeanPoo.Functional.CertifiedView

/-! Named access and projection of already built dependent results. Joint
consumer proofs can use data interfaces without unpacking factory tuples. -/
namespace LeanPoo.Functional.Requirements
universe u v w
variable {Context : Type u} {Key : Type v} {Value : Context → Key → Type w}
variable [DecidableEq Key]

/-- Read the first occurrence of a key at exactly the result tuple's context.
This scans the source list and does not execute any factory. -/
def resultAt {context : Context} : {keys : List Key} → Results Value context keys →
    (key : Key) → key ∈ keys → Value context key
  | [], _, _, member => False.elim (List.not_mem_nil member)
  | head :: rest, (value, tail), key, member =>
    if same : head = key then same ▸ value
    else resultAt tail key (by
      rcases List.mem_cons.mp member with equal | included
      · exact False.elim (same equal.symm)
      · exact included)

/-- Named result access agrees with applying the retained named factory. -/
theorem resultAt_build (factories : Factories Context Value source) (context : Context)
    (key : Key) (member : key ∈ source) :
    resultAt (build factories context) key member = factoryAt factories key member context := by
  induction source with
  | nil => simp at member
  | cons head rest ih =>
    rcases factories with ⟨factory, tail⟩
    by_cases same : head = key
    · subst key; simp [resultAt, factoryAt, build]
    · simpa [resultAt, factoryAt, build, same] using ih tail
        (by simpa [List.mem_cons, Ne.symm same] using member)

/-- Project already built values in consumer order, retaining duplicate keys.
No provider lookup or factory application is performed. -/
def projectResults {context : Context} {source : List Key} (data : Results Value context source) :
    (keys : List Key) → (∀ key ∈ keys, key ∈ source) → Results Value context keys
  | [], _ => PUnit.unit
  | key :: rest, included =>
    (resultAt data key (included key (by simp)),
      projectResults data rest (fun key member => included key (by simp [member])))

/-- Narrow already built data together with its proof. The supplied logical
consequence sees values only; no factory or provider is called. -/
def projectEvidence {context : Context} {source : List Key}
    {Claim : Results Value context source → Prop}
    (data : {value : Results Value context source // Claim value})
    (keys : List Key) (included : ∀ key ∈ keys, key ∈ source)
    (Narrow : Results Value context keys → Prop)
    (derive : ∀ value, Claim value → Narrow (projectResults value keys included)) :
    {value : Results Value context keys // Narrow value} :=
  ⟨projectResults data.val keys included, derive data.val data.property⟩

@[simp] theorem projectEvidence_val {context : Context} {source : List Key}
    {Claim : Results Value context source → Prop}
    (data : {value : Results Value context source // Claim value})
    (keys : List Key) (included : ∀ key ∈ keys, key ∈ source) (Narrow) (derive) :
    (projectEvidence data keys included Narrow derive).val = projectResults data.val keys included := rfl

/-- Building projected factories and projecting their built values commute.
This proves value equality, not equality of evaluation cost or effects. -/
theorem build_project (factories : Factories Context Value source) (keys : List Key)
    (included : ∀ key ∈ keys, key ∈ source) (context : Context) :
    build (project factories keys included) context = projectResults (build factories context) keys included := by
  induction keys with
  | nil => rfl
  | cons key rest ih =>
    simp only [project, build, projectResults, resultAt_build]
    exact congrArg (fun tail => (factoryAt factories key (included key (by simp)) context, tail)) (ih _)

/-- Derive a narrow certificate using a theorem over arbitrary built data.
The client need not unfold retained factory tuples or their application. -/
def Certified.projectData {source : List Key} {Claim : ∀ c, Results Value c source → Prop}
    (ready : Certified source Claim) (keys : List Key) (included : ∀ key ∈ keys, key ∈ source)
    (Narrow : ∀ c, Results Value c keys → Prop)
    (derive : ∀ c data, Claim c data → Narrow c (projectResults data keys included)) :
    Certified keys Narrow :=
  ready.project keys included Narrow (fun c proof => by
    rw [build_project]
    exact derive c _ proof)

@[simp] theorem Certified.projectData_factories {source : List Key}
    {Claim : ∀ c, Results Value c source → Prop} (ready : Certified source Claim)
    (keys : List Key) (included : ∀ key ∈ keys, key ∈ source)
    (Narrow : ∀ c, Results Value c keys → Prop) (derive) :
    (ready.projectData keys included Narrow derive).factories = Requirements.project ready.factories keys included := rfl

/-- The data carried by the narrow certificate is the projected broad data. -/
theorem Certified.projectData_build {source : List Key}
    {Claim : ∀ c, Results Value c source → Prop} (ready : Certified source Claim)
    (keys : List Key) (included : ∀ key ∈ keys, key ∈ source)
    (Narrow : ∀ c, Results Value c keys → Prop) (derive) (context : Context) :
    ((ready.projectData keys included Narrow derive).build context).val =
      projectResults (ready.build context).val keys included :=
  build_project ready.factories keys included context

end LeanPoo.Functional.Requirements
