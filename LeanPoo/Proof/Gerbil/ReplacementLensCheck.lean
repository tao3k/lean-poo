import Std

namespace ReplacementLensCheck

inductive Failure where
  | getPut | putGet | putPut | source (code : Nat)
  deriving DecidableEq, Repr

inductive Run (S A : Type) where
  | ok (value : A) (state : S)
  | refused (error : Failure) (state : S)
  deriving DecidableEq

def Run.bind (x : Run S A) (f : A → S → Run S B) : Run S B :=
  match x with
  | .ok a s => f a s
  | .refused e s => .refused e s

def each (f : A → S → Run S Unit) : List A → S → Run S Unit
  | [], s => .ok () s
  | a :: as, s => (f a s).bind fun _ t => each f as t

structure Operations (S A : Type) where
  get : A → S → Run S A
  put : A → A → S → Run S A
  equal : A → A → S → Run S Bool

def require (eq : A → A → S → Run S Bool) (law : Failure)
    (actual expected : A) (s : S) : Run S Unit :=
  (eq actual expected s).bind fun b t =>
    if b then .ok () t else .refused law t

-- Mirrors the three ordered loops after observed shape and method reads.
def reference (op : Operations S A) (states values : List A) (s : S) : Run S Unit :=
  each (fun raw t =>
    (op.get raw t).bind fun old t₁ =>
    (op.put old raw t₁).bind fun restored t₂ =>
    (require op.equal .getPut restored raw t₂).bind fun _ t₃ =>
    each (fun v t₄ =>
      (op.put v raw t₄).bind fun updated t₅ =>
      (op.get updated t₅).bind fun projected t₆ =>
      (require op.equal .putGet projected v t₆).bind fun _ t₇ =>
      each (fun next t₈ =>
        (op.put v raw t₈).bind fun intermediate t₉ =>
        (op.put next intermediate t₉).bind fun actual t₁₀ =>
        (op.put next raw t₁₀).bind fun expected t₁₁ =>
        require op.equal .putPut actual expected t₁₁) values t₇) values t₃) states s

def replacementComparisons (eq : A → A → S → Run S Bool)
    (states values : List A) (s : S) : Run S Unit :=
  each (fun raw t => (require eq .getPut raw raw t).bind fun _ t₁ =>
    each (fun v t₂ => (require eq .putGet v v t₂).bind fun _ t₃ =>
      each (fun next t₄ => require eq .putPut next next t₄) values t₃)
      values t₁) states s

-- A fast branch needs exact method authority; the identity laws alone
-- would not imply this stateful equality for arbitrary Scheme callbacks.
theorem replacement_exact (op : Operations S A) (states values : List A) (s : S)
    (getExact : ∀ a t, op.get a t = .ok a t)
    (putExact : ∀ a b t, op.put a b t = .ok a t) :
    reference op states values s = replacementComparisons op.equal states values s := by
  simp only [reference, replacementComparisons, getExact, putExact, Run.bind]

theorem each_ok (f : A → S → Run S Unit) (xs : List A) (s : S)
    (h : ∀ x ∈ xs, ∀ t, f x t = .ok () t) :
    each f xs s = .ok () s := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [each, h x List.mem_cons_self, Run.bind]
    exact ih (fun y hy => h y (List.mem_cons_of_mem x hy))

-- Separate certificate: comparison of these actual carrier points
-- succeeds without any observable work. No assumption about other points.
theorem certified_domain_exact
    (eq : A → A → S → Run S Bool) (states values : List A) (s : S)
    (safe : ∀ x, x ∈ states ∨ x ∈ values → ∀ t, eq x x t = .ok true t) :
    replacementComparisons eq states values s = .ok () s := by
  unfold replacementComparisons
  apply each_ok
  intro raw hr t
  simp only [require, safe raw (Or.inl hr), Run.bind, ite_true]
  apply each_ok
  intro v hv t'
  simp only [safe v (Or.inr hv), ite_true]
  apply each_ok
  intro next hn t''
  simp only [safe next (Or.inr hn), ite_true]

-- Shape/method observations run before choosing a certified branch.
-- Independent subsequent source, lens, residual and publication stages
-- execute unchanged, even when the bounded law matrix is discharged.
def optimized (op : Operations S A) (states values : List A)
    (methodCurrent domainSafe : S → Bool) (s : S) : Run S Unit :=
  if methodCurrent s then
    if domainSafe s then .ok () s else replacementComparisons op.equal states values s
  else reference op states values s

theorem guarded_check_exact
    (admit : S → Run S (Operations S A × List A × List A))
    (methods domain : Operations S A → List A → List A → S → Bool)
    (after : S → Run S P) (s : S)
    (exactGet : ∀ op xs vs t, methods op xs vs t = true →
      ∀ a u, op.get a u = .ok a u)
    (exactPut : ∀ op xs vs t, methods op xs vs t = true →
      ∀ a b u, op.put a b u = .ok a u)
    (safe : ∀ op xs vs t, domain op xs vs t = true →
      ∀ x, x ∈ xs ∨ x ∈ vs → ∀ u, op.equal x x u = .ok true u) :
    (admit s).bind (fun (op, xs, vs) t =>
      (optimized op xs vs (methods op xs vs) (domain op xs vs) t).bind (fun _ => after)) =
    (admit s).bind (fun (op, xs, vs) t =>
      (reference op xs vs t).bind (fun _ => after)) := by
  cases admit s with
  | refused => rfl
  | ok input t =>
    obtain ⟨op, xs, vs⟩ := input
    have h : optimized op xs vs (methods op xs vs) (domain op xs vs) t =
        reference op xs vs t := by
      unfold optimized
      split
      · rename_i hm
        rw [replacement_exact op xs vs t (exactGet op xs vs t hm) (exactPut op xs vs t hm)]
        split
        · rename_i hd
          rw [certified_domain_exact op.equal xs vs t (safe op xs vs t hd)]
        · rfl
      · rfl
    simp only [Run.bind, h]

-- Number of callbacks in successful complete traversal. Scope/source
-- guards and method observations are deliberately outside these counts.
def lawEqualities (states values : Nat) := states * (1 + values + values * values)
def lensCallbacks (states values : Nat) := states * (2 + 2 * values + 3 * (values * values))

-- Count callbacks by executing the SAME traversal with instrumented methods.
theorem each_ticks (f : A → Nat → Run Nat Unit) (xs : List A) (s n : Nat)
    (step : ∀ x t, f x t = .ok () (t + n)) :
    each f xs s = .ok () (s + xs.length * n) := by
  induction xs generalizing s with
  | nil => simp [each]
  | cons x xs ih =>
    simp only [each, step, Run.bind, ih, List.length_cons, Nat.succ_mul]
    congr 1
    omega

private def countLens (method eq : Nat) : Operations Nat A :=
  ⟨fun a t => .ok a (t + method), fun a _ t => .ok a (t + method),
    fun _ _ t => .ok true (t + eq)⟩

theorem reference_ticks (states values : List A) (s method eq : Nat) :
    reference (countLens method eq) states values s =
      .ok () (s + states.length *
        (method + method + eq +
          values.length * (method + method + eq +
            values.length * (method + method + method + eq)))) := by
  unfold reference
  apply each_ticks
  intro raw t
  simp only [countLens, Run.bind, require, ite_true]
  rw [each_ticks _ values _ (method + method + eq +
    values.length * (method + method + method + eq))]
  · congr 1
    omega
  · intro v u
    rw [each_ticks _ values _ (method + method + method + eq)]
    · congr 1
      omega
    · intro w k
      congr 1
      omega

theorem actual_law_equalities (states values : List A) (s : Nat) :
    reference (countLens 0 1) states values s =
      .ok () (s + lawEqualities states.length values.length) := by
  rw [reference_ticks]
  simp [lawEqualities, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem actual_lens_callbacks (states values : List A) (s : Nat) :
    reference (countLens 1 0) states values s =
      .ok () (s + lensCallbacks states.length values.length) := by
  rw [reference_ticks]
  simp [lensCallbacks, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm,
    Nat.add_assoc, Nat.add_comm]

example : 2 * lawEqualities 1 1 + lawEqualities 2 3 = 32 := by decide
example : 2 * lensCallbacks 1 1 + lensCallbacks 2 3 = 84 := by decide

private def identityLens (eq : Nat → Nat → Nat → Run Nat Bool) : Operations Nat Nat :=
  ⟨fun a t => .ok a t, fun a _ t => .ok a t, eq⟩

-- Unsupported comparison points preserve the first refusal, not an
-- optimistic law success. Observed equality can change the trace too.
example :
    optimized (identityLens (fun _ _ t => .ok false (t + 1))) [0] [1]
      (fun _ => true) (fun _ => false) 0 = .refused .getPut 1 := rfl

example :
    optimized (identityLens (fun _ _ t => .ok true (t + 1))) [0] [1]
      (fun _ => true) (fun _ => false) 0 = .ok () 3 := rfl

-- Returning the same value does not certify a callback that changes state.
example :
    optimized ⟨fun (a : Nat) (t : Nat) => .ok a (t + 1),
      fun a _ t => .ok a t, fun _ _ t => .ok true t⟩ [0] [1]
      (fun _ => false) (fun _ => true) 0 = .ok () 2 := rfl

#print axioms replacement_exact
#print axioms certified_domain_exact
#print axioms guarded_check_exact
#print axioms actual_law_equalities
#print axioms actual_lens_callbacks

end ReplacementLensCheck
