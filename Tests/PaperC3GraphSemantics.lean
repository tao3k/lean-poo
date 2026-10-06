import LeanPoo.Prototype.C3GraphSemantics

open LeanPoo.Prototype
namespace LeanPoo.Tests.PaperC3GraphSemantics

private def graph : C3.Graph :=
  [("O", []), ("A", ["O"]), ("B", ["O"]),
   ("X", ["A", "B"]), ("Y", ["B", "O"])]

private def roots : List String := ["X", "Y", "A", "X"]

#guard (C3.linearizeUncachedMany graph roots).toOption ==
  some [["X", "A", "B", "O"], ["Y", "B", "O"], ["A", "O"],
    ["X", "A", "B", "O"]]
#guard (C3.certifyGraph graph roots).toOption.map (·.orders) ==
  some [["X", "A", "B", "O"], ["Y", "B", "O"], ["A", "O"],
    ["X", "A", "B", "O"]]
#guard C3.certifyGraph [("A", ["B"]), ("B", ["A"])] ["A"] matches
  .error (.cached (.cycle _))
#guard C3.certifyGraph [("A", []), ("A", [])] [] matches
  .error (.cached (.duplicateNode "A"))
#guard C3.linearizeUncached [("A", ["B"]), ("B", ["A"])] "A" matches
  .error (.cycle _)
#guard C3.linearizeUncached [("A", ["missing"])] "A" matches
  .error (.unknownNode "missing")
#guard C3.linearizeUncached [("A", []), ("A", [])] "A" matches
  .error (.duplicateNode "A")
#guard C3.linearizeUncachedMany [("A", []), ("A", [])] [] matches
  .error (.duplicateNode "A")
#guard C3.linearizeUncachedMany [("A", ["B", "B"])] ["A"] matches
  .error .inconsistentOrder
#guard C3.linearizeUncachedMany graph [] matches .ok []
#guard C3.linearizeUncachedMany [("A", [])] ["missing", "A"] matches
  .error (.unknownNode "missing")
#guard C3.linearizeUncachedMany [("A", ["A"])] ["A", "missing"] matches
  .error (.cycle "A")
#guard C3.linearizeUncached [("O", []), ("A", ["O"]), ("B", ["O"]),
  ("X", ["A", "B"]), ("Y", ["B", "A"]), ("Z", ["X", "Y"])] "Z" matches
  .error .inconsistentOrder

private theorem admitted_agrees (certificate : C3.GraphCertificate graph roots) :
    C3.linearizeMany graph roots = C3.linearizeUncachedMany graph roots :=
  certificate.agrees

private theorem admitted_first_root (certificate : C3.GraphCertificate graph roots) :
    ∃ order tail, certificate.orders = order :: tail ∧ order.head? = some "X" := by
  obtain ⟨order, tail, rows, trace⟩ := certificate.source_traces.head
  exact ⟨order, tail, rows, trace.root_head⟩

private theorem admitted_first_parent_order (certificate : C3.GraphCertificate graph roots) :
    ∃ (entry : String × List String) (tail : List String)
      (rest : List (List String)),
      graph.find? (fun row => row.1 == "X") = some entry ∧
      certificate.orders = ("X" :: tail) :: rest ∧
      entry.2.Sublist tail ∧ tail.Nodup := by
  obtain ⟨order, rest, rows, trace⟩ := certificate.source_traces.head
  obtain ⟨entry, tail, lookup, same, parents, nodup⟩ := trace.parent_order
  subst order
  exact ⟨entry, tail, rest, lookup, rows, parents, nodup⟩

private theorem source_root_unique (left : C3.GraphTrace graph fuel₁ "X" first)
    (right : C3.GraphTrace graph fuel₂ "X" second) : first = second :=
  left.unique right

private theorem admitted_batch_unique (certificate : C3.GraphCertificate graph roots)
    (other : C3.ParentTraces graph fuel roots orders) :
    certificate.orders = orders :=
  certificate.eq_source other

private theorem reference_derivation
    (success : C3.linearizeUncachedMany graph roots = .ok orders) :
    C3.ParentDerivations graph roots orders :=
  C3.linearizeUncachedMany_derivation graph roots orders success

private theorem cached_derivation
    (success : C3.linearizeMany graph roots = .ok orders) :
    C3.ParentDerivations graph roots orders :=
  C3.linearizeMany_derivation graph roots orders success

private theorem cached_matches_paper
    (success : C3.linearizeMany graph roots = .ok orders)
    (source : C3.ParentDerivations graph roots expected) :
    orders = expected :=
  C3.linearizeMany_eq_derivation graph roots orders success source

private theorem cached_row_count
    (success : C3.linearizeMany graph roots = .ok orders) :
    orders.length = roots.length :=
  C3.linearizeMany_order_count graph roots orders success

private theorem successful_traversals_equal
    (cached : C3.linearizeMany graph roots = .ok cachedOrders)
    (reference : C3.linearizeUncachedMany graph roots = .ok referenceOrders) :
    cachedOrders = referenceOrders :=
  C3.linearizeMany_eq_uncached_success graph roots cachedOrders referenceOrders
    cached reference

private theorem empty_batch_agrees (other : C3.Graph) :
    C3.linearizeMany other [] = C3.linearizeUncachedMany other [] :=
  C3.linearizeMany_nil_eq_uncached other

private theorem invalid_batch_agrees (other : C3.Graph) (requested : List String)
    (err : LeanPoo.C4.Error) (invalid : C3.validateGraph other = .error err) :
    C3.linearizeMany other requested = C3.linearizeUncachedMany other requested :=
  C3.linearizeMany_eq_uncached_validation_error other requested err invalid

private theorem uncached_singleton_agrees (other : C3.Graph) (requested : String) :
    C3.linearizeUncachedMany other [requested] =
      (C3.linearizeUncached other requested).map (fun order => [order]) :=
  C3.linearizeUncachedMany_singleton other requested

private theorem missing_first_agrees (other : C3.Graph) (requested : String)
    (remaining : List String)
    (missing : other.find? (fun entry => entry.1 == requested) = none) :
    C3.linearizeMany other (requested :: remaining) =
      C3.linearizeUncachedMany other (requested :: remaining) :=
  C3.linearizeMany_eq_uncached_missing_first other requested remaining missing

private theorem self_parent_first_agrees (other : C3.Graph) (requested : String)
    (parents remaining : List String)
    (found : other.find? (fun entry => entry.1 == requested) =
      some (requested, requested :: parents)) :
    C3.linearizeMany other (requested :: remaining) =
      C3.linearizeUncachedMany other (requested :: remaining) :=
  C3.linearizeMany_eq_uncached_self_parent_first other requested parents remaining found

private theorem first_scalar_error_stops (other : C3.Graph) (requested : String)
    (remaining : List String) (err : LeanPoo.C4.Error)
    (cached : C3.linearize other requested = .error err)
    (reference : C3.linearizeUncached other requested = .error err) :
    C3.linearizeMany other (requested :: remaining) =
      C3.linearizeUncachedMany other (requested :: remaining) :=
  C3.linearizeMany_eq_uncached_of_first_scalar_error other requested remaining err
    cached reference

private theorem admitted_derivation (certificate : C3.GraphCertificate graph roots) :
    C3.ParentDerivations graph roots certificate.orders :=
  certificate.derivations

private theorem admitted_derivation_unique
    (certificate : C3.GraphCertificate graph roots)
    (other : C3.ParentDerivations graph roots orders) :
    certificate.orders = orders :=
  certificate.eq_derivation other

private theorem memoize_derived
    (valid : C3.CacheDerivations graph cache)
    (derived : C3.GraphDerivation graph root order) :
    C3.CacheDerivations graph (cache.insert root order) :=
  valid.insert derived

private theorem memoized_hit_agrees
    (valid : C3.CacheDerivations graph cache)
    (found : cache.get? root = some cached)
    (source : C3.GraphDerivation graph root expected) :
    cached = expected :=
  valid.agrees found source

#eval IO.println "POOF-C3-GRAPH-SEMANTICS-OK singleton=allGraphs recursiveSourceTrace=true cachedDerivation=true cachedBatchAdmission=true"
#print axioms C3.linearizeMany_singleton
#print axioms C3.linearizeUncached_sound
#print axioms C3.linearizeUncachedMany_sound
#print axioms C3.linearizeUncachedMany_singleton
#print axioms C3.GraphTrace.unique
#print axioms C3.ParentTraces.unique
#print axioms C3.GraphTrace.eraseFuel
#print axioms C3.GraphDerivation.unique
#print axioms C3.ParentDerivations.unique
#print axioms C3.linearizeUncachedMany_derivation
#print axioms C3.CacheDerivations.empty
#print axioms C3.CacheDerivations.insert
#print axioms C3.CacheDerivations.agrees
#print axioms C3.visit_sound
#print axioms C3.linearize_derivation
#print axioms C3.linearizeMany_derivation
#print axioms C3.linearizeMany_eq_derivation
#print axioms C3.linearizeMany_order_count
#print axioms C3.linearizeMany_eq_uncached_success
#print axioms C3.linearizeMany_nil_eq_uncached
#print axioms C3.linearizeMany_eq_uncached_validation_error
#print axioms C3.linearizeMany_eq_uncached_missing_first
#print axioms C3.linearizeMany_eq_uncached_self_parent_first
#print axioms C3.linearizeMany_eq_uncached_of_first_scalar_error
#print axioms C3.GraphCertificate.source_traces
#print axioms C3.GraphCertificate.derivations
#print axioms C3.GraphCertificate.eq_source
#print axioms C3.GraphCertificate.eq_derivation
#print axioms C3.GraphCertificate.order_count
#print axioms C3.GraphCertificate.agrees
#print axioms admitted_first_root
#print axioms admitted_first_parent_order
#print axioms source_root_unique
#print axioms admitted_batch_unique
#print axioms reference_derivation
#print axioms cached_derivation
#print axioms cached_matches_paper
#print axioms cached_row_count
#print axioms successful_traversals_equal
#print axioms admitted_derivation
#print axioms admitted_derivation_unique
#print axioms memoize_derived
#print axioms memoized_hit_agrees
#print axioms admitted_agrees

end LeanPoo.Tests.PaperC3GraphSemantics
