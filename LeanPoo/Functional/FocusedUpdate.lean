import LeanPoo.Functional.Assembly
import LeanPoo.Prototype.Lens
import LeanPoo.Prototype.SkewLens

/-! Total nested focuses for the concrete getter/setter/wrapper construction.
The supplied lens laws justify accumulated updates. Open method fragments use
an explicit self; no recursive fixed-point equation is assumed. -/
namespace LeanPoo.Functional
universe u v w x y

structure Focus (Whole : Type u) (Part : Type v) where
  get : Whole → Part
  set : Part → Whole → Whole
  get_set : ∀ part whole, get (set part whole) = part
  set_get : ∀ whole, set (get whole) whole = whole
  set_set : ∀ first second whole, set second (set first whole) = set second whole

namespace Focus
variable {Whole : Type u} {Part : Type v} {Inner : Type w} {Self : Type x} {Error : Type y}

/-- Compose outer and inner focuses, retaining all three update laws. -/
def compose (outer : Focus Whole Part) (inner : Focus Part Inner) : Focus Whole Inner where
  get whole := inner.get (outer.get whole)
  set part whole := outer.set (inner.set part (outer.get whole)) whole
  get_set part whole := by rw [outer.get_set, inner.get_set]
  set_get whole := by rw [inner.set_get, outer.set_get]
  set_set first second whole := by rw [outer.get_set, inner.set_set, outer.set_set]

def modify (focus : Focus Whole Part) (change : Part → Part) (whole : Whole) : Whole :=
  focus.set (change (focus.get whole)) whole

def toMonoLens (focus : Focus Whole Part) : Prototype.MonoLens Whole Part :=
  Prototype.MonoLens.ofGetSet focus.get focus.set

theorem mono_modify (focus : Focus Whole Part) (change : Part → Part) (whole : Whole) :
    focus.toMonoLens.modify change whole = focus.modify change whole := rfl

@[simp] theorem get_modify (focus : Focus Whole Part) (change : Part → Part) (whole : Whole) :
    focus.get (focus.modify change whole) = change (focus.get whole) := focus.get_set _ _

theorem modify_identity (focus : Focus Whole Part) (whole : Whole) :
    focus.modify id whole = whole := focus.set_get whole

/-- Two updates accumulate in caller order, rather than rebuilding an old context. -/
theorem modify_modify (focus : Focus Whole Part) (first second : Part → Part) (whole : Whole) :
    focus.modify second (focus.modify first whole) = focus.modify (second ∘ first) whole := by
  simp only [modify, focus.get_set, focus.set_set, Function.comp_apply]

theorem compose_modify (outer : Focus Whole Part) (inner : Focus Part Inner)
    (change : Inner → Inner) (whole : Whole) :
    (outer.compose inner).modify change whole = outer.modify (inner.modify change) whole := rfl

/-- A declared outside observation is preserved by every focused update. -/
theorem modify_frame (focus : Focus Whole Part) (observe : Whole → Self)
    (outside : ∀ part whole, observe (focus.set part whole) = observe whole)
    (change : Part → Part) (whole : Whole) :
    observe (focus.modify change whole) = observe whole := outside _ _

/-- Use the existing delayed constructor, with explicit cooked self and inherited part. -/
def prototype (focus : Focus Whole Part) (fragment : Self → Part → Part) :
    Prototype.DelayedProto Self Whole Whole :=
  Prototype.lensGen focus.get focus.set
    (fun method self inherited => method self.get inherited.get) fragment

theorem prototype_apply (focus : Focus Whole Part) (fragment : Self → Part → Part)
    (self : Self) (whole : Whole) :
    focus.prototype fragment (Thunk.pure self) (Thunk.pure whole) =
      focus.modify (fragment self) whole := rfl

/-- Actual delayed composition agrees with local parent-then-child method wrapping. -/
theorem prototype_compose (focus : Focus Whole Part) (parent child : Self → Part → Part)
    (self : Thunk Self) (inherited : Thunk Whole) :
    Prototype.DelayedProto.compose (focus.prototype child) (focus.prototype parent) self inherited =
      focus.prototype (fun self old => child self (parent self old)) self inherited := by
  simp only [Prototype.DelayedProto.compose, prototype, Prototype.lensGen,
    Thunk.get, focus.get_set, focus.set_set]

/-- Keep the admission witness in the output while installing its exposed part.
A refused local result returns the whole source unchanged. -/
def checkedWith {Approved : Type w} (focus : Focus Whole Part) (expose : Approved → Part)
    (change : Part → Except Error Approved) (whole : Whole) : Except Error Approved × Whole :=
  match change (focus.get whole) with
  | .error error => (.error error, whole)
  | .ok approved => (.ok approved, focus.set (expose approved) whole)

theorem checkedWith_outcome {Approved : Type w} (focus : Focus Whole Part) (expose : Approved → Part)
    (change : Part → Except Error Approved) (whole : Whole) :
    (focus.checkedWith expose change whole).1 = change (focus.get whole) := by
  unfold checkedWith
  cases change (focus.get whole) <;> rfl

theorem checkedWith_error {Approved : Type w} (focus : Focus Whole Part) (expose : Approved → Part)
    (change : Part → Except Error Approved) (whole : Whole) (error : Error)
    (refused : change (focus.get whole) = .error error) :
    focus.checkedWith expose change whole = (.error error, whole) := by simp [checkedWith, refused]

theorem checkedWith_ok {Approved : Type w} (focus : Focus Whole Part) (expose : Approved → Part)
    (change : Part → Except Error Approved) (whole : Whole) (approved : Approved)
    (accepted : change (focus.get whole) = .ok approved) :
    focus.checkedWith expose change whole = (.ok approved, focus.set (expose approved) whole) := by
  simp [checkedWith, accepted]

theorem checkedWith_frame {Approved : Type w} (focus : Focus Whole Part) (expose : Approved → Part)
    (change : Part → Except Error Approved) (observe : Whole → Self)
    (outside : ∀ part whole, observe (focus.set part whole) = observe whole) (whole : Whole) :
    observe (focus.checkedWith expose change whole).2 = observe whole := by
  unfold checkedWith
  cases change (focus.get whole) <;> simp [outside]

/-- Every successful witness describes precisely the installed local value. -/
theorem checkedWith_installed {Approved : Type w} (focus : Focus Whole Part) (expose : Approved → Part)
    (change : Part → Except Error Approved) (whole : Whole) (approved : Approved)
    (success : (focus.checkedWith expose change whole).1 = .ok approved) :
    focus.get (focus.checkedWith expose change whole).2 = expose approved := by
  unfold checkedWith at success ⊢
  cases changed : change (focus.get whole) with
  | error error => simp [changed] at success
  | ok actual =>
    have same : actual = approved := by simpa [changed] using success
    subst actual
    exact focus.get_set _ _

def checked (focus : Focus Whole Part) (change : Part → Except Error Part) (whole : Whole) :
    Except Error Part × Whole := focus.checkedWith id change whole

theorem checked_error (focus : Focus Whole Part) (change : Part → Except Error Part)
    (whole : Whole) (error : Error) (refused : change (focus.get whole) = .error error) :
    focus.checked change whole = (.error error, whole) := by simp [checked, checkedWith, refused]

theorem checked_ok (focus : Focus Whole Part) (change : Part → Except Error Part)
    (whole : Whole) (part : Part) (accepted : change (focus.get whole) = .ok part) :
    focus.checked change whole = (.ok part, focus.set part whole) := by simp [checked, checkedWith, accepted]

/-- Different focuses commute only under explicit read independence and setter
commutation. Fragments may use the same fixed self, but not changing whole reads. -/
structure Independent (left : Focus Whole Part) (right : Focus Whole Inner) : Prop where
  left_read : ∀ part whole, left.get (right.set part whole) = left.get whole
  right_read : ∀ part whole, right.get (left.set part whole) = right.get whole
  setters : ∀ a b whole, left.set a (right.set b whole) = right.set b (left.set a whole)

theorem modify_commute (left : Focus Whole Part) (right : Focus Whole Inner)
    (independent : Independent left right) (first : Part → Part) (second : Inner → Inner)
    (whole : Whole) :
    left.modify first (right.modify second whole) = right.modify second (left.modify first whole) := by
  simp only [modify, independent.left_read, independent.right_read, independent.setters]

end Focus

/-- Lift a context-dependent local update through a lawful focus of a retained factory. -/
def Factory.focus {Context : Type u} {Whole : Context → Type v} {Part : Context → Type w}
    (focus : ∀ context, Focus (Whole context) (Part context))
    (change : ∀ context, Part context → Part context) (factory : Factory Context Whole) :
    Factory Context Whole := Factory.map (fun context => (focus context).modify (change context)) factory

theorem Factory.focus_get {Context : Type u} {Whole : Context → Type v} {Part : Context → Type w}
    (focus : ∀ context, Focus (Whole context) (Part context))
    (change : ∀ context, Part context → Part context) (factory : Factory Context Whole) (context : Context) :
    (focus context).get (Factory.focus focus change factory context) =
      change context ((focus context).get (factory context)) := Focus.get_modify _ _ _

theorem Factory.focus_identity {Context : Type u} {Whole : Context → Type v} {Part : Context → Type w}
    (focus : ∀ context, Focus (Whole context) (Part context)) (factory : Factory Context Whole) :
    Factory.focus focus (fun _ => id) factory = factory := by
  funext context
  exact Focus.modify_identity _ _

theorem Factory.focus_compose {Context : Type u} {Whole : Context → Type v} {Part : Context → Type w}
    (focus : ∀ context, Focus (Whole context) (Part context))
    (first second : ∀ context, Part context → Part context) (factory : Factory Context Whole) :
    Factory.focus focus second (Factory.focus focus first factory) =
      Factory.focus focus (fun context => second context ∘ first context) factory := by
  funext context
  exact Focus.modify_modify _ _ _ _

end LeanPoo.Functional
