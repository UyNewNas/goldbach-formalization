import ImbalancedChen.ActualThirdOriginalP4AOrdinaryConcreteCandidate
import ImbalancedChen.Certificates.OriginalNodeArraysV1.All40CheckedTable

/-!
SOURCEONLY / UNCOMPILED / MAIN OPEN30.
The second import means the frozen 20261024y All40CheckedTableV2 draft,
with its Block19/37 source repairs and every listed Block00..39 dependency.
This file consumes that exact table; it does not emit or alter table data.
No historical saved-leaf membership or final all-candidate minimum is claimed.
-/
namespace ImbalancedChen.OriginalThirdP4AOrdinaryConcreteAll40SourceOnly
noncomputable section
open Set MeasureTheory
open OriginalThirdCompactPartitionSourceOnly OriginalThirdClippedChordSourceOnly
open OriginalThirdP4AOrdinaryConcreteCandidateSourceOnly
open OriginalU2All40CheckedTable20261024wSourceOnly

/-- Fixed cost expression at the existing all40 literal reader. -/
def literalCandidateUpper : ℤ := candidateUpper literalCheckedBlockTable

/-- Closed composition with the existing concrete all40 supplier. There are
no query soundness, cell geometry, target cost or integral premises. All
remaining uncertainty is dependency elaboration and historical tree binding. -/
theorem literal_ordinary_candidate_upper :
    (∫ t in compactRegion ∩ Icc leafA leafB, compactKernel t)≤
      value literalCandidateUpper := by
  exact concrete_ordinary_candidate_upper literalCheckedBlockTable

end
end ImbalancedChen.OriginalThirdP4AOrdinaryConcreteAll40SourceOnly
