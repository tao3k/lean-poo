import LeanPoo.Prototype.C3GraphTrace

/-! Optional admission of the production C3 cache against the proof-producing
uncached finite interpreter. -/

namespace LeanPoo.Prototype.C3

open LeanPoo.C4

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

/-- An admitted cached batch carries a paper-style recursive trace for every
requested root, including all visited parents and each node's C3 merge. -/
theorem GraphCertificate.source_traces (certificate : GraphCertificate graph roots) :
    ParentTraces graph (graph.length+1) roots certificate.orders :=
  linearizeUncachedMany_sound graph roots certificate.orders certificate.reference

/-- Compare an admitted cached batch with any independently supplied
paper-style graph derivations, without rerunning either interpreter. -/
theorem GraphCertificate.eq_source (certificate : GraphCertificate graph roots)
    (source : ParentTraces graph fuel roots output) :
    certificate.orders = output :=
  certificate.source_traces.unique source

/-- A successful admission has as many output rows as requested roots. -/
theorem GraphCertificate.order_count (certificate : GraphCertificate graph roots) :
    certificate.orders.length = roots.length :=
  certificate.source_traces.length

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
