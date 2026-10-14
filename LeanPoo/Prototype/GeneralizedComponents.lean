import LeanPoo.Prototype.GeneralizedInheritance
import LeanPoo.Functional.FocusedUpdate

/-! Research extension: independently closed subprotocols mounted in a larger
cooked service. Lawful independent focuses justify grouping assembly; public
method effects retain their original execution order. -/
namespace LeanPoo.Prototype.Generalized
open Functional

/-- Install a local compiler through the existing generalized lens constructor. -/
def Compiler.mount (compiler : Compiler Part Local Fragment) (focus : Focus Whole Part)
    (view : Global → Local) : Compiler Whole Global Fragment :=
  lensGen focus.get focus.set (fun fragment self parent => compiler fragment (self.map view) parent)

def Protocol.mount (protocol : Protocol Part Local Fragment) (focus : Focus Whole Part)
    (view : Global → Local) (cook : Whole → Global) : Protocol Whole Global Fragment :=
  ⟨cook,protocol.compile.mount focus view⟩

theorem Protocol.assemble_mount (protocol : Protocol Part Local Fragment) (focus : Focus Whole Part)
    (view : Global → Local) (cook : Whole → Global) (fragments : List Fragment)
    (self : Thunk Global) (parent : Thunk Whole) :
    (protocol.mount focus view cook).assemble fragments self parent =
      focus.set (protocol.assemble fragments (self.map view) (parent.map focus.get)) parent.get := by
  induction fragments with
  | nil => exact (focus.set_get _).symm
  | cons fragment rest ih =>
    change focus.set (protocol.compile fragment (self.map view)
      (Thunk.mk fun _ => focus.get ((protocol.mount focus view cook).assemble rest self parent)))
      ((protocol.mount focus view cook).assemble rest self parent) = _
    rw [ih]
    simp only [focus.get_set, focus.set_set]
    rfl

/-- Storage independence alone suffices for assembly partition. Cooked views
may depend on other components; closure needs separate compatibility laws. -/
structure Mounting (left : Compiler L LC LF) (right : Compiler R RC RF) (Whole Global : Type) where
  leftFocus : Focus Whole L
  rightFocus : Focus Whole R
  independent : Focus.Independent leftFocus rightFocus
  leftView : Global → LC
  rightView : Global → RC
  cook : Whole → Global

/-- Both interfaces must be views of local cooking; unrelated focuses must
carry explicit read independence and setter commutation proofs. -/
structure Components (left : Protocol L LC LF) (right : Protocol R RC RF) (Whole Global : Type) where
  leftFocus : Focus Whole L
  rightFocus : Focus Whole R
  independent : Focus.Independent leftFocus rightFocus
  leftView : Global → LC
  rightView : Global → RC
  cook : Whole → Global
  leftCompatible : ∀ whole, leftView (cook whole) = left.cook (leftFocus.get whole)
  rightCompatible : ∀ whole, rightView (cook whole) = right.cook (rightFocus.get whole)

variable {left : Protocol L LC LF} {right : Protocol R RC RF}

def leftFragments : List (Sum LF RF) → List LF
  | [] => []
  | .inl fragment :: rest => fragment :: leftFragments rest
  | .inr _ :: rest => leftFragments rest

def rightFragments : List (Sum LF RF) → List RF
  | [] => []
  | .inl _ :: rest => rightFragments rest
  | .inr fragment :: rest => fragment :: rightFragments rest

@[simp] theorem leftFragments_append (first second : List (Sum LF RF)) :
    leftFragments (first ++ second) = leftFragments first ++ leftFragments second := by
  induction first with
  | nil => rfl
  | cons item rest ih => cases item <;> simp [leftFragments,ih]
@[simp] theorem rightFragments_append (first second : List (Sum LF RF)) :
    rightFragments (first ++ second) = rightFragments first ++ rightFragments second := by
  induction first with
  | nil => rfl
  | cons item rest ih => cases item <;> simp [rightFragments,ih]
@[simp] theorem leftFragments_map_left (items : List LF) :
    leftFragments (items.map (Sum.inl : LF → Sum LF RF)) = items := by
  induction items <;> simp_all [leftFragments]
@[simp] theorem rightFragments_map_left (items : List LF) :
    rightFragments (items.map (Sum.inl : LF → Sum LF RF)) = [] := by
  induction items <;> simp_all [rightFragments]
@[simp] theorem leftFragments_map_right (items : List RF) :
    leftFragments (items.map (Sum.inr : RF → Sum LF RF)) = [] := by
  induction items <;> simp_all [leftFragments]
@[simp] theorem rightFragments_map_right (items : List RF) :
    rightFragments (items.map (Sum.inr : RF → Sum LF RF)) = items := by
  induction items <;> simp_all [rightFragments]

def groupedFragments (fragments : List (Sum LF RF)) : List (Sum LF RF) :=
  (leftFragments fragments).map Sum.inl ++ (rightFragments fragments).map Sum.inr

def Compiler.assemble (compiler : Compiler Raw Cooked Fragment) (fragments : List Fragment) :
    DelayedProto Cooked Raw Raw := DelayedProto.composeAll (fragments.map compiler)

variable {leftCompiler : Compiler L LC LF} {rightCompiler : Compiler R RC RF}

def Mounting.protocol (mounting : Mounting leftCompiler rightCompiler Whole Global) :
    Protocol Whole Global (Sum LF RF) :=
  ⟨mounting.cook,sumCompiler (leftCompiler.mount mounting.leftFocus mounting.leftView)
    (rightCompiler.mount mounting.rightFocus mounting.rightView)⟩

theorem Mounting.assemble_partition
    (components : Mounting leftCompiler rightCompiler Whole Global)
    (fragments : List (Sum LF RF)) (self : Thunk Global) (parent : Thunk Whole) :
    components.protocol.assemble fragments self parent =
      components.rightFocus.set
        (rightCompiler.assemble (rightFragments fragments) (self.map components.rightView) (parent.map components.rightFocus.get))
        (components.leftFocus.set
          (leftCompiler.assemble (leftFragments fragments) (self.map components.leftView) (parent.map components.leftFocus.get)) parent.get) := by
  induction fragments with
  | nil =>
    change parent.get = components.rightFocus.set (components.rightFocus.get parent.get)
      (components.leftFocus.set (components.leftFocus.get parent.get) parent.get)
    rw [components.leftFocus.set_get, components.rightFocus.set_get]
  | cons fragment rest ih =>
    cases fragment with
    | inl fragment =>
      change components.leftFocus.set
        (leftCompiler fragment (self.map components.leftView)
          (Thunk.mk fun _ => components.leftFocus.get (components.protocol.assemble rest self parent)))
        (components.protocol.assemble rest self parent) = _
      rw [ih]
      simp only [components.independent.left_read, components.leftFocus.get_set,
        components.independent.setters, components.leftFocus.set_set]
      rfl
    | inr fragment =>
      change components.rightFocus.set
        (rightCompiler fragment (self.map components.rightView)
          (Thunk.mk fun _ => components.rightFocus.get (components.protocol.assemble rest self parent)))
        (components.protocol.assemble rest self parent) = _
      rw [ih]
      simp only [components.rightFocus.get_set, components.rightFocus.set_set]
      rfl


theorem Mounting.assemble_grouped (mounting : Mounting leftCompiler rightCompiler Whole Global)
    (fragments : List (Sum LF RF)) (self : Thunk Global) (parent : Thunk Whole) :
    mounting.protocol.assemble (groupedFragments fragments) self parent =
      mounting.protocol.assemble fragments self parent := by
  rw [mounting.assemble_partition,mounting.assemble_partition]
  simp only [groupedFragments,leftFragments_append,rightFragments_append,
    leftFragments_map_left,leftFragments_map_right,rightFragments_map_left,rightFragments_map_right,List.append_nil,List.nil_append]

def Components.mounting (components : Components left right Whole Global) :
    Mounting left.compile right.compile Whole Global :=
  ⟨components.leftFocus,components.rightFocus,components.independent,
    components.leftView,components.rightView,components.cook⟩

def Components.protocol (components : Components left right Whole Global) : Protocol Whole Global (Sum LF RF) :=
  components.mounting.protocol

theorem Components.assemble_partition (components : Components left right Whole Global)
    (fragments : List (Sum LF RF)) (self : Thunk Global) (parent : Thunk Whole) :
    components.protocol.assemble fragments self parent =
      components.rightFocus.set
        (right.assemble (rightFragments fragments) (self.map components.rightView) (parent.map components.rightFocus.get))
        (components.leftFocus.set
          (left.assemble (leftFragments fragments) (self.map components.leftView) (parent.map components.leftFocus.get)) parent.get) :=
  components.mounting.assemble_partition fragments self parent

theorem Components.assemble_equiv (components : Components left right Whole Global)
    (first second : List (Sum LF RF))
    (sameLeft : leftFragments first = leftFragments second)
    (sameRight : rightFragments first = rightFragments second)
    (self : Thunk Global) (parent : Thunk Whole) :
    components.protocol.assemble first self parent = components.protocol.assemble second self parent := by
  rw [components.assemble_partition, components.assemble_partition, sameLeft, sameRight]

theorem Components.assemble_grouped (components : Components left right Whole Global)
    (fragments : List (Sum LF RF)) (self : Thunk Global) (parent : Thunk Whole) :
    components.protocol.assemble (groupedFragments fragments) self parent =
      components.protocol.assemble fragments self parent :=
  components.assemble_equiv _ _ (by simp [groupedFragments]) (by simp [groupedFragments]) self parent

theorem Components.step_partition (components : Components left right Whole Global)
    (fragments : List (Sum LF RF)) (final base : Whole) :
    components.protocol.step fragments final base =
      components.rightFocus.set
        (right.step (rightFragments fragments) (components.rightFocus.get final) (components.rightFocus.get base))
        (components.leftFocus.set
          (left.step (leftFragments fragments) (components.leftFocus.get final) (components.leftFocus.get base)) base) := by
  unfold Protocol.step
  rw [components.assemble_partition]
  change components.rightFocus.set
    (right.assemble _ (Thunk.mk fun _ => components.rightView (components.cook final)) _)
    (components.leftFocus.set (left.assemble _ (Thunk.mk fun _ => components.leftView (components.cook final)) _) _) = _
  rw [components.leftCompatible, components.rightCompatible]
  rfl

theorem Components.approximate_left (components : Components left right Whole Global)
    (fragments : List (Sum LF RF)) (base seed : Whole) (depth : Nat) :
    components.leftFocus.get (components.protocol.approximate fragments base seed depth) =
      left.approximate (leftFragments fragments) (components.leftFocus.get base) (components.leftFocus.get seed) depth := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
    rw [Protocol.approximate_succ, components.step_partition]
    simp only [components.independent.left_read, components.leftFocus.get_set]
    rw [ih]
    rfl

theorem Components.approximate_right (components : Components left right Whole Global)
    (fragments : List (Sum LF RF)) (base seed : Whole) (depth : Nat) :
    components.rightFocus.get (components.protocol.approximate fragments base seed depth) =
      right.approximate (rightFragments fragments) (components.rightFocus.get base) (components.rightFocus.get seed) depth := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
    rw [Protocol.approximate_succ, components.step_partition]
    simp only [components.rightFocus.get_set]
    rw [ih]
    rfl

/-- Join actual component closure witnesses without tying another recursive knot. -/
def Components.close (components : Components left right Whole Global) (fragments : List (Sum LF RF)) (base : Whole)
    (leftClosed : Closed left (leftFragments fragments) (components.leftFocus.get base))
    (rightClosed : Closed right (rightFragments fragments) (components.rightFocus.get base)) :
    Closed components.protocol fragments base where
  raw := components.rightFocus.set rightClosed.raw (components.leftFocus.set leftClosed.raw base)
  fixed := by
    rw [components.step_partition]
    change components.rightFocus.set
      (right.step _ (components.rightFocus.get (components.rightFocus.set rightClosed.raw (components.leftFocus.set leftClosed.raw base))) _)
      (components.leftFocus.set (left.step _ (components.leftFocus.get (components.rightFocus.set rightClosed.raw (components.leftFocus.set leftClosed.raw base))) _) _) = _
    rw [components.rightFocus.get_set rightClosed.raw (components.leftFocus.set leftClosed.raw base)]
    rw [components.independent.left_read rightClosed.raw (components.leftFocus.set leftClosed.raw base)]
    rw [components.leftFocus.get_set leftClosed.raw base, rightClosed.fixed, leftClosed.fixed]

theorem Components.close_left (components : Components left right Whole Global)
    (fragments : List (Sum LF RF)) (base : Whole)
    (leftClosed : Closed left (leftFragments fragments) (components.leftFocus.get base))
    (rightClosed : Closed right (rightFragments fragments) (components.rightFocus.get base)) :
    components.leftView (components.close fragments base leftClosed rightClosed).interface = leftClosed.interface := by
  change components.leftView (components.cook (components.close fragments base leftClosed rightClosed).raw) = _
  rw [components.leftCompatible]
  change left.cook (components.leftFocus.get (components.rightFocus.set rightClosed.raw
    (components.leftFocus.set leftClosed.raw base))) = _
  rw [components.independent.left_read, components.leftFocus.get_set]
  rfl

theorem Components.close_right (components : Components left right Whole Global)
    (fragments : List (Sum LF RF)) (base : Whole)
    (leftClosed : Closed left (leftFragments fragments) (components.leftFocus.get base))
    (rightClosed : Closed right (rightFragments fragments) (components.rightFocus.get base)) :
    components.rightView (components.close fragments base leftClosed rightClosed).interface = rightClosed.interface := by
  change components.rightView (components.cook (components.close fragments base leftClosed rightClosed).raw) = _
  rw [components.rightCompatible]
  change right.cook (components.rightFocus.get (components.rightFocus.set rightClosed.raw
    (components.leftFocus.set leftClosed.raw base))) = _
  rw [components.rightFocus.get_set]
  rfl

def Components.projectLeft (components : Components left right Whole Global)
    {fragments : List (Sum LF RF)} {base : Whole} (closed : Closed components.protocol fragments base) :
    Closed left (leftFragments fragments) (components.leftFocus.get base) where
  raw := components.leftFocus.get closed.raw
  fixed := by
    have fixed := congrArg components.leftFocus.get closed.fixed
    rw [components.step_partition] at fixed
    rw [components.independent.left_read, components.leftFocus.get_set] at fixed
    exact fixed

def Components.projectRight (components : Components left right Whole Global)
    {fragments : List (Sum LF RF)} {base : Whole} (closed : Closed components.protocol fragments base) :
    Closed right (rightFragments fragments) (components.rightFocus.get base) where
  raw := components.rightFocus.get closed.raw
  fixed := by
    have fixed := congrArg components.rightFocus.get closed.fixed
    rw [components.step_partition] at fixed
    rw [components.rightFocus.get_set] at fixed
    exact fixed

/-- Regroup the construction of an already closed service; keep its actual raw value. -/
def Components.regroup (components : Components left right Whole Global)
    {fragments : List (Sum LF RF)} {base : Whole} (closed : Closed components.protocol fragments base) :
    Closed components.protocol (groupedFragments fragments) base where
  raw := closed.raw
  fixed := by
    unfold Protocol.step
    rw [components.assemble_grouped]
    exact closed.fixed

theorem Components.regroup_interface (components : Components left right Whole Global)
    {fragments : List (Sum LF RF)} {base : Whole} (closed : Closed components.protocol fragments base) :
    (components.regroup closed).interface = closed.interface := rfl

/-- Replace the right component, retaining the left witness only after proving
that its complete ordered fragment projection is unchanged. -/
def Components.replaceRight (components : Components left right Whole Global)
    {old : List (Sum LF RF)} {base : Whole} (closed : Closed components.protocol old base)
    (revised : List (Sum LF RF)) (sameLeft : leftFragments revised = leftFragments old)
    (rightClosed : Closed right (rightFragments revised) (components.rightFocus.get base)) :
    Closed components.protocol revised base :=
  components.close revised base
    ⟨components.leftFocus.get closed.raw,by rw [sameLeft]; exact (components.projectLeft closed).fixed⟩ rightClosed

theorem Components.replaceRight_left (components : Components left right Whole Global)
    {old : List (Sum LF RF)} {base : Whole} (closed : Closed components.protocol old base)
    (revised : List (Sum LF RF)) (sameLeft : leftFragments revised = leftFragments old)
    (rightClosed : Closed right (rightFragments revised) (components.rightFocus.get base)) :
    components.leftView (components.replaceRight closed revised sameLeft rightClosed).interface =
      components.leftView closed.interface := by
  unfold Components.replaceRight
  rw [components.close_left]
  exact (components.leftCompatible closed.raw).symm

theorem Components.closed_frame (components : Components left right Whole Global)
    {fragments : List (Sum LF RF)} {base : Whole} (closed : Closed components.protocol fragments base)
    (observe : Whole → Frame)
    (leftFrame : ∀ part whole, observe (components.leftFocus.set part whole) = observe whole)
    (rightFrame : ∀ part whole, observe (components.rightFocus.set part whole) = observe whole) :
    observe closed.raw = observe base := by
  calc
    observe closed.raw = observe (components.protocol.step fragments closed.raw base) := congrArg observe closed.fixed.symm
    _ = observe base := by rw [components.step_partition,rightFrame,leftFrame]

/-- All observations outside both components survive positive assembly depths. -/
theorem Components.frame (components : Components left right Whole Global) (fragments : List (Sum LF RF))
    (observe : Whole → Frame)
    (leftFrame : ∀ part whole, observe (components.leftFocus.set part whole) = observe whole)
    (rightFrame : ∀ part whole, observe (components.rightFocus.set part whole) = observe whole)
    (base seed : Whole) (depth : Nat) :
    observe (components.protocol.approximate fragments base seed (depth+1)) = observe base := by
  rw [Protocol.approximate_succ, components.step_partition, rightFrame, leftFrame]

end LeanPoo.Prototype.Generalized
