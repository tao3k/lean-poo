import LeanPoo.Functional.ObservedView

/-! Retarget a narrow public cache to different internal factories using only
the consumer's declared observation equality and its original joint proof. -/
namespace LeanPoo.Functional.Requirements
universe u v w x y z
variable {Context : Type u} {Key : Type v} [DecidableEq Key]
variable {Value : Context → Key → Type w} {Other : Context → Key → Type x}
variable {Observed : Context → Key → Type y}
variable {source : List Key} {Claim : ∀ c, Results Value c source → Prop}
variable {ready : Certified source Claim}

def Certified.replaceView (ready : Certified source Claim) (keys : List Key)
    (included : ∀ key ∈ keys, key ∈ source)
    (expose : ∀ c key, Value c key → Observed c key)
    (reveal : ∀ c key, Other c key → Observed c key)
    (Public : ∀ c, Results Observed c keys → Prop)
    (derive : ∀ c data, Claim c data → Public c (observeResults expose (projectResults data keys included)))
    (candidate : Factories Context Other keys)
    (compatible : Related (fun c key a b => expose c key a = reveal c key b)
      keys (Requirements.project ready.factories keys included) candidate) :
    Certified keys (fun c data => Public c (observeResults reveal data)) :=
  ⟨candidate, fun c => by
    have same := congrArg (fun factories => Requirements.build factories c)
      (observe_congr expose reveal keys (Requirements.project ready.factories keys included) candidate compatible)
    rw [build_observe, build_observe, build_project] at same
    rw [← same]
    exact derive c _ (ready.valid c)⟩

/-- The public certificate is equal even if hidden carriers, unrequested
methods and representation-specific metadata differ. -/
theorem Certified.replaceView_public (ready : Certified source Claim) (keys : List Key)
    (included : ∀ key ∈ keys, key ∈ source) (expose : ∀ c key, Value c key → Observed c key)
    (reveal : ∀ c key, Other c key → Observed c key) (Public) (derive)
    (candidate : Factories Context Other keys) (compatible) :
    ready.observeProject keys included expose Public derive =
      (ready.replaceView keys included expose reveal Public derive candidate compatible).observe
        reveal Public (fun _ _ proof => proof) := by
  apply Certified.ext
  exact observe_congr expose reveal keys _ candidate compatible

/-- Transfer only observed data to the candidate's public certificate. On a
future miss, the new narrow candidate factories supply the public data. -/
def ContextSlot.retargetView (slot : ContextSlot ready) (keys : List Key)
    (included : ∀ key ∈ keys, key ∈ source) (expose : ∀ c key, Value c key → Observed c key)
    (reveal : ∀ c key, Other c key → Observed c key) (Public) (derive)
    (candidate : Factories Context Other keys) (compatible) :
    ContextSlot ((ready.replaceView keys included expose reveal Public derive candidate compatible).observe
      reveal Public (fun _ _ proof => proof)) :=
  (slot.observeProject keys included expose Public derive).rebind _
    (congrArg Certified.factories (ready.replaceView_public keys included expose reveal Public derive candidate compatible))

omit [DecidableEq Key] in
theorem ContextSlot.rebind_read_reused [DecidableEq Context]
    {keys : List Key} {Public : ∀ c, Results Observed c keys → Prop}
    {left : Certified keys Public} (slot : ContextSlot left) (right : Certified keys Public)
    (same : left.factories = right.factories) (context : Context) :
    ((slot.rebind right same).read context).2.2 = (slot.read context).2.2 := by
  have equal := Certified.ext left right same
  subst right
  simp [ContextSlot.rebind]

theorem ContextSlot.observeProject_read_reused [DecidableEq Context] (slot : ContextSlot ready)
    (keys : List Key) (included : ∀ key ∈ keys, key ∈ source) (expose : ∀ c key, Value c key → Observed c key)
    (Public) (derive) (context : Context) :
    ((slot.observeProject keys included expose Public derive).read context).2.2 = (slot.read context).2.2 := by
  cases stored : slot.retained with
  | none => simp only [ContextSlot.observeProject, ContextSlot.read, stored, Option.map]
  | some pair =>
    rcases pair with ⟨previous, data⟩
    by_cases same : previous = context <;>
      simp [ContextSlot.observeProject, ContextSlot.read, stored, same]

/-- Retargeting preserves the exact hit decision at every context. -/
theorem ContextSlot.retargetView_reused [DecidableEq Context] (slot : ContextSlot ready) (keys : List Key)
    (included : ∀ key ∈ keys, key ∈ source) (expose : ∀ c key, Value c key → Observed c key)
    (reveal : ∀ c key, Other c key → Observed c key) (Public) (derive)
    (candidate : Factories Context Other keys) (compatible) (context : Context) :
    ((slot.retargetView keys included expose reveal Public derive candidate compatible).read context).2.2 =
      (slot.read context).2.2 := by
  unfold ContextSlot.retargetView
  rw [ContextSlot.rebind_read_reused]
  exact slot.observeProject_read_reused keys included expose Public derive context

/-- Every proof-aware public consumer retains its output at every context. -/
theorem ContextSlot.retargetView_consume [DecidableEq Context] (slot : ContextSlot ready) (keys : List Key)
    (included : ∀ key ∈ keys, key ∈ source) (expose : ∀ c key, Value c key → Observed c key)
    (reveal : ∀ c key, Other c key → Observed c key) (Public) (derive)
    (candidate : Factories Context Other keys) (compatible) {Output : Context → Type z}
    (construct : ∀ c data, Public c data → Output c) (context : Context) :
    ((slot.retargetView keys included expose reveal Public derive candidate compatible).consume construct context).1 =
      (ready.observeProject keys included expose Public derive).consume construct context := by
  rw [ContextSlot.consume_value, ← ready.replaceView_public keys included expose reveal Public derive candidate compatible]

end LeanPoo.Functional.Requirements
