import ImbalancedChen.ActualThirdOriginalP4AOriginalClippedGapLeaf
import ImbalancedChen.ActualThirdOriginalP4AOrdinaryRawFallbackAllOld

/-! SOURCEONLY / UNCOMPILED / MAIN OPEN30.
Actual existing sourceCapLower supplies the primitive cap-floor obligation.
This separate assembly avoids making the original OuterMinimum module
depend on its own cap-floor / clipped descendants. -/
namespace ImbalancedChen.OriginalThirdP4AOriginalClippedGapAssemblySourceOnly
noncomputable section
open Set MeasureTheory
open OriginalThirdBoxMomentsSourceOnly OriginalThirdCompactPartitionSourceOnly
open OriginalThirdClippedChordSourceOnly OriginalThirdRoundedNewSourceOnly
open OriginalThirdBelowMuBRoundedSourceOnly
open OriginalThirdP4AOrdinaryFiniteSelectorSourceOnly
open OriginalThirdP4AOrdinaryFiniteDispatchSourceOnly
open OriginalThirdP4AOrdinaryOuterMinimumSourceOnly
open OriginalThirdP4AOrdinaryRawFallbackAllOldSourceOnly
open OriginalU2StoredNodeBlockDataSourceOnly OriginalU2StoredNodeBlockCheckerSourceOnly
open OriginalU2StoredQueryLookupSourceOnly

theorem clipped_high_eq_source (table : CheckedBlockTable) (lo hi : Fin 3 → ℤ) :
    OriginalThirdP4AOriginalClippedGapSourceOnly.clippedHigh table lo hi (sourceCapLower lo hi)=
      clippedFallbackHigh table lo hi := by
  rfl

/-- The literal cap-floor algorithm is consumed here, so the actual
clipped integral has no assumed cap or target-difference inequality. -/
theorem original_clipped_source_mean_upper (table : CheckedBlockTable)
    (lo hi : Fin 3 → ℤ) (a b : Fin 3 → ℚ) (g : OrdinaryGrid lo hi a b)
    (hassert : hi 0+hi 1<sourceCapLower lo hi) :
    (∫ t in compactRegion ∩ Icc (realBox a) (realBox b),compactKernel t)≤
      4*boxMass (realBox a) (realBox b)*value (clippedFallbackHigh table lo hi) := by
  have hca : sourceCapLower lo hi≤(481573208064:ℤ) := min_le_left _ _
  have hc := OriginalThirdP4AOriginalClippedGapSourceOnly.original_clipped_gap_integral
    table lo hi (sourceCapLower lo hi) (realBox a) (realBox b)
    (realBox_grid_binding lo a g.lower) (realBox_grid_binding hi b g.upper)
    g.positive g.width hca hassert
    (fun t ht => original_integer_cap_lower_le_actual lo hi a b g ht.2)
  rw [clipped_high_eq_source] at hc
  exact hc

/-- The exact clipped source high at the SAME selected candidate's mass,
retaining B's or tent's original operation tree and one final integer UP. -/
theorem original_clipped_source_integer_upper (table : CheckedBlockTable)
    (lo hi : Fin 3 → ℤ) (a b : Fin 3 → ℚ) (g : OrdinaryGrid lo hi a b)
    (p : Candidate) (hassert : hi 0+hi 1<sourceCapLower lo hi) :
    (∫ t in compactRegion ∩ Icc (realBox a) (realBox b),compactKernel t)≤
      value (charge (candidateMassHi lo hi p) (clippedFallbackHigh table lo hi)) := by
  have hf := original_clipped_source_mean_upper table lo hi a b g hassert
  have hm := candidate_mass_upper lo hi a b g p
  have hh : 0≤value (clippedFallbackHigh table lo hi) := by
    rw [← clipped_high_eq_source]
    exact OriginalThirdP4AOriginalClippedGapSourceOnly.clippedHigh_nonneg _ _ _ _
  calc
    (∫ t in compactRegion ∩ Icc (realBox a) (realBox b),compactKernel t)≤
        4*boxMass (realBox a) (realBox b)*value (clippedFallbackHigh table lo hi) := hf
    _≤value (candidateMassHi lo hi p)*value (clippedFallbackHigh table lo hi) :=
      mul_le_mul_of_nonneg_right hm hh
    _=value (clippedFallbackHigh table lo hi)*value (candidateMassHi lo hi p) := by ring
    _≤value (charge (candidateMassHi lo hi p) (clippedFallbackHigh table lo hi)) :=
      OriginalThirdSymmetricMassCeilSourceOnly.literal_product_UP_ge _ _

/-- The original first two high candidates, in their actual min order,
with neither candidate's integral bound assumed by the caller. -/
theorem original_raw_clipped_min_integer_upper (table : CheckedBlockTable)
    (lo hi : Fin 3 → ℤ) (a b : Fin 3 → ℚ) (g : OrdinaryGrid lo hi a b)
    (p : Candidate) (hassert : hi 0+hi 1<sourceCapLower lo hi) :
    (∫ t in compactRegion ∩ Icc (realBox a) (realBox b),compactKernel t)≤
      value (charge (candidateMassHi lo hi p)
        (min (rawFallbackHigh table lo hi) (clippedFallbackHigh table lo hi))) := by
  rw [charge_min _ _ _ (candidate_mass_nonneg lo hi a b g p),value_min]
  exact le_min (original_raw_all_old_integer_upper table lo hi a b g p hassert)
    (original_clipped_source_integer_upper table lo hi a b g p hassert)

end
end ImbalancedChen.OriginalThirdP4AOriginalClippedGapAssemblySourceOnly
