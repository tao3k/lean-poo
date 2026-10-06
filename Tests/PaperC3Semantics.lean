import LeanPoo.Prototype.C3Semantics

open LeanPoo.Prototype
namespace LeanPoo.Tests.PaperC3Semantics

private def candidates : List (List String) :=
  [[], ["A", "O"], ["B", "O"], [], ["A", "B"]]

#guard C3.sourceChoose candidates == some "A"
#guard C3.removeNext "A" candidates == [["O"], ["B", "O"], ["B"]]
#guard (C3.mergeCertified candidates).toOption.map (·.output) ==
  some ["A", "B", "O"]
#guard (C3.mergeCertified [["A", "B"], ["B", "A"]]) matches
  .error .inconsistentOrder

private theorem direct_parent_order (certificate :
    LeanPoo.C4.Precedence.Certified candidates) :
    ["A", "B"].Sublist certificate.output :=
  C3.mergeCertified_preserves candidates certificate ["A", "B"]
    (by simp [candidates])

private theorem inherited_order (certificate :
    LeanPoo.C4.Precedence.Certified candidates) :
    ["A", "O"].Sublist certificate.output :=
  C3.mergeCertified_preserves candidates certificate ["A", "O"]
    (by simp [candidates])

private theorem no_duplicates (certificate :
    LeanPoo.C4.Precedence.Certified candidates) :
    certificate.output.Nodup :=
  C3.mergeCertified_nodup candidates certificate

private theorem source_trace_same (source : C3.SourceTrace candidates output)
    (certificate : LeanPoo.C4.Precedence.Certified candidates) :
    output = certificate.output :=
  source.eq_certified certificate

#eval IO.println "POOF-C3-SEMANTICS-OK allCandidateLists=true leftmost=true normalizedStep=true sourceTrace=true certifiedOrder=true"
#print axioms C3.sourceEligible_eq
#print axioms C3.sourceChoose_eq
#print axioms C3.removeNext_eq_advance
#print axioms C3.SourceTrace.ofCertified
#print axioms C3.SourceTrace.eq_certified
#print axioms C3.mergeCertified_preserves
#print axioms C3.mergeCertified_covers
#print axioms C3.mergeCertified_nodup
#print axioms direct_parent_order
#print axioms inherited_order
#print axioms no_duplicates
#print axioms source_trace_same

end LeanPoo.Tests.PaperC3Semantics
