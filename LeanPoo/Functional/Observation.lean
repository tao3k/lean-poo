import LeanPoo.Functional.View

/-! Preserve consumers through a declared observation interface even when the
two providers return different representations. Contexts and keys stay exact. -/
namespace LeanPoo.Functional.Requirements

universe u v w x y
variable {Context : Type u} {Key : Type v}
variable {Value : Context → Key → Type w} {Other : Context → Key → Type x}
variable {Observed : Context → Key → Type y}

/-- Pointwise compatibility of two retained families. This does not imply
availability, factory equality, or agreement on fields outside the relation. -/
def Related (relation : ∀ context key, Value context key → Other context key → Prop) :
    (keys : List Key) → Factories Context Value keys → Factories Context Other keys → Prop
  | [], _, _ => True
  | key :: rest, (left, tail), (right, remaining) =>
    (∀ context, relation context key (left context) (right context)) ∧
      Related relation rest tail remaining

/-- Relate selections only on a consumer's keys. Successful preparation is a
separate obligation; this condition makes no claim about missing-key errors. -/
def RelatedOn (provider : Provider Context Key Value) (other : Provider Context Key Other)
    (keys : List Key) (relation : ∀ context key, Value context key → Other context key → Prop) : Prop :=
  ∀ key ∈ keys, ∀ left right, provider key = some left → other key = some right →
    ∀ context, relation context key (left context) (right context)

/-- Relating selected functions relates the corresponding complete tuples. -/
theorem selected_related (provider : Provider Context Key Value) (other : Provider Context Key Other)
    (relation : ∀ context key, Value context key → Other context key → Prop)
    (keys : List Key) (left : Factories Context Value keys) (right : Factories Context Other keys)
    (a : Selected provider keys left) (b : Selected other keys right)
    (compatible : RelatedOn provider other keys relation) : Related relation keys left right := by
  induction keys with
  | nil => trivial
  | cons key rest ih =>
    rcases left with ⟨first, tail⟩
    rcases right with ⟨second, remaining⟩
    exact ⟨compatible key (by simp) first second a.1 b.1,
      ih tail remaining a.2 b.2 (fun key member => compatible key (by simp [member]))⟩

/-- Different successful source families can supply related narrow views.
The compatibility obligation covers only the consumer's declared keys. -/
theorem project_related [DecidableEq Key]
    (provider : Provider Context Key Value) (other : Provider Context Key Other)
    (relation : ∀ context key, Value context key → Other context key → Prop)
    (left : Factories Context Value leftKeys) (right : Factories Context Other rightKeys)
    (leftReady : prepare provider leftKeys = .ok left)
    (rightReady : prepare other rightKeys = .ok right)
    (keys : List Key) (a : ∀ key ∈ keys, key ∈ leftKeys)
    (b : ∀ key ∈ keys, key ∈ rightKeys)
    (compatible : RelatedOn provider other keys relation) :
    Related relation keys (project left keys a) (project right keys b) :=
  selected_related provider other relation keys _ _
    ((prepare_ok_iff _ _ _).mp (project_ready provider left leftReady keys a))
    ((prepare_ok_iff _ _ _).mp (project_ready other right rightReady keys b)) compatible

/-- Adapt retained functions to the public observation family. This creates
functions; observation is evaluated when the returned factory is invoked. -/
def observe (expose : ∀ context key, Value context key → Observed context key) :
    {keys : List Key} → Factories Context Value keys → Factories Context Observed keys
  | [], _ => PUnit.unit
  | key :: _, (factory, tail) =>
    ((fun context => expose context key (factory context)), observe expose tail)

/-- Pointwise observation equality is sufficient; the original result types
and hidden fields may differ. The public observation family must be fixed. -/
theorem observe_congr
    (expose : ∀ context key, Value context key → Observed context key)
    (reveal : ∀ context key, Other context key → Observed context key)
    (keys : List Key) (left : Factories Context Value keys) (right : Factories Context Other keys)
    (compatible : Related (fun context key a b => expose context key a = reveal context key b) keys left right) :
    observe expose left = observe reveal right := by
  induction keys with
  | nil => cases left; cases right; rfl
  | cons key rest ih =>
    rcases left with ⟨first, tail⟩
    rcases right with ⟨second, remaining⟩
    exact Prod.ext (funext compatible.1) (ih tail remaining compatible.2)

/-- Any consumer of the observation interface retains its exact result,
including functions over contexts. Consumers of hidden fields are excluded. -/
theorem observed_consumer_stable
    (expose : ∀ context key, Value context key → Observed context key)
    (reveal : ∀ context key, Other context key → Observed context key)
    (keys : List Key) (left : Factories Context Value keys) (right : Factories Context Other keys)
    (compatible : Related (fun context key a b => expose context key a = reveal context key b) keys left right)
    (consume : Factories Context Observed keys → Result) :
    consume (observe expose left) = consume (observe reveal right) :=
  congrArg consume (observe_congr expose reveal keys left right compatible)

end LeanPoo.Functional.Requirements
