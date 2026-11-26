import Std

namespace ColdObjectBaseCases

-- Gerbil c4-linearize* first drops empty local parent orders. Its zero-parent
-- branch returns the supplied head, with no suffix or resolver invocation.
-- Keep other branches opaque: no extra graph algorithm is being introduced.
def c4Boundary (head : List N) (parents : List (List N))
    (other : List (List N) → Except E (List N × Option N)) :=
  match parents.filter (fun row => !row.isEmpty) with
  | [] => Except.ok (head, none)
  | rows => other rows

theorem root_precedence (self : N)
    (other : List (List N) → Except E (List N × Option N)) :
    c4Boundary [self] [[]] other = .ok ([self], none) := rfl

-- Ordered effect boundaries surrounding C4 are preserved. In the Scheme
-- path these are active-table admission, then installation and the hook;
-- the hook may refuse even though the canonical order is a singleton.
theorem root_precedence_with_boundaries (self : N)
    (other : List (List N) → Except E (List N × Option N))
    (enter : Except E Unit) (installAndCheck : List N → Except E A) :
    (do
      enter
      let (order, _) ← c4Boundary [self] [[]] other
      installAndCheck order) =
    (do enter; installAndCheck [self]) := by
  cases enter <;> rfl

-- Original slot compilation starts with no predecessor only for explicit
-- constructors that discard it. The same missing-super thunk is passed to
-- a computed spec; neither the thunk nor any user slot body is forced here.
def compileChain (discards : Spec → Bool)
    (applySpec : Spec → Option Fn → Option Fn) (missing : Fn)
    (newestFirst : List Spec) : Option Fn :=
  match newestFirst.reverse with
  | [] => none
  | first :: rest =>
      let initial := if discards first then none else some missing
      (first :: rest).foldl (fun previous spec => applySpec spec previous) initial

theorem singleton_slot_chain (discards : Spec → Bool)
    (applySpec : Spec → Option Fn → Option Fn) (missing : Fn) (spec : Spec) :
    compileChain discards applySpec missing [spec] =
      applySpec spec (if discards spec then none else some missing) := rfl

#print axioms root_precedence_with_boundaries
#print axioms singleton_slot_chain

end ColdObjectBaseCases
