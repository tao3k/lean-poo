import LeanPoo.Prototype.C3Semantics

/-! An uncached finite graph interpretation of Appendix A and an optional
admission check for the production C3 cache. Unlike `C3.linearizeMany`, each
parent occurrence is recomputed. This is a semantic reference, not the fast
execution path. -/

namespace LeanPoo.Prototype.C3

open LeanPoo.C4

private def visitUncached (graph : Graph) (name : String) (path : List String) :
    Nat → Except C4.Error (List String)
  | 0 => .error (.cycle name)
  | fuel+1 => do
    if path.contains name then throw (.cycle name)
    let some entry := graph.find? (fun entry => entry.1 == name) |
      throw (.unknownNode name)
    let mut orders := []
    for parent in entry.2 do
      let order ← visitUncached graph parent (name :: path) fuel
      orders := order :: orders
    let tail ← mergeCertified (orders.reverse ++ [entry.2])
    return name :: tail.output

/-- Independently interpret a validated finite graph without any cache.
`linearizeMany graph []` performs exactly the public graph validation. -/
def linearizeUncached (graph : Graph) (root : String) :
    Except C4.Error (List String) := do
  let _ ← linearizeMany graph []
  visitUncached graph root [] (graph.length+1)

/-- Recompute every root and every ancestor occurrence independently. -/
def linearizeUncachedMany (graph : Graph) (roots : List String) :
    Except C4.Error (List (List String)) :=
  roots.mapM (linearizeUncached graph)

inductive GraphAdmissionError where
  | cached (error : C4.Error)
  | reference (error : C4.Error)
  | disagreement
  deriving Repr, DecidableEq

/-- Proof that the cached batch agrees with the uncached interpretation on
the exact graph and root list supplied to admission. -/
structure GraphCertificate (graph : Graph) (roots : List String) where
  orders : List (List String)
  cached : linearizeMany graph roots = .ok orders
  reference : linearizeUncachedMany graph roots = .ok orders

private theorem mapM_ok_length (f : α → Except ε β) (inputs : List α)
    (outputs : List β) (success : inputs.mapM f = .ok outputs) :
    outputs.length = inputs.length := by
  induction inputs generalizing outputs with
  | nil =>
    change Except.ok [] = Except.ok outputs at success
    cases success
    rfl
  | cons input rest ih =>
    cases first : f input with
    | error error =>
      simp [List.mapM_cons, first, bind, Except.bind] at success
    | ok value =>
      cases tail : rest.mapM f with
      | error error =>
        simp [List.mapM_cons, first, tail, bind, Except.bind] at success
      | ok values =>
        simp [List.mapM_cons, first, tail, bind, Except.bind] at success
        cases success
        simp [ih values tail]

/-- A successful admission has as many output rows as requested roots. -/
theorem GraphCertificate.order_count (certificate : GraphCertificate graph roots) :
    certificate.orders.length = roots.length :=
  mapM_ok_length (linearizeUncached graph) roots certificate.orders certificate.reference

theorem GraphCertificate.agrees (certificate : GraphCertificate graph roots) :
    linearizeMany graph roots = linearizeUncachedMany graph roots := by
  rw [certificate.cached, certificate.reference]

/-- Optional checked admission. It runs the uncached interpreter, so callers
should use `linearizeMany` for ordinary execution and admit only when they
need a graph-level semantic receipt. -/
def certifyGraph (graph : Graph) (roots : List String) :
    Except GraphAdmissionError (GraphCertificate graph roots) :=
  match cached : linearizeMany graph roots with
  | .error error => .error (.cached error)
  | .ok orders =>
    match reference : linearizeUncachedMany graph roots with
    | .error error => .error (.reference error)
    | .ok expected =>
      if same : orders = expected then
        .ok ⟨orders, cached, by simpa [same] using reference⟩
      else .error .disagreement

end LeanPoo.Prototype.C3
