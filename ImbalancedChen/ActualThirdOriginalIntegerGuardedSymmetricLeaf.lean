import ImbalancedChen.ActualThirdOriginalRoundedOldWeight
import ImbalancedChen.ActualThirdOriginalPositive256LogIntegerGuards

/-! SOURCEONLY / HOLD_ELABORATION / OPEN30.
The two original OLD/NEW interval-divisor guards are supplied from the original
integer coordinate representation. No guard or mean/weight bound is an input. -/
namespace ImbalancedChen.OriginalThirdIntegerGuardedLeafSourceOnly
noncomputable section
open Set MeasureTheory
open OriginalThirdClippedChordSourceOnly OriginalThirdRoundedNewSourceOnly
open OriginalThirdPositiveLogSourceOnly OriginalThirdTriangleMomentsSourceOnly
open OriginalThirdSymmetricJensenSourceOnly OriginalThirdRoundedOldWeightSourceOnly
open OriginalThirdSortedHalfIntegralSourceOnly OriginalThirdCompactPartitionSourceOnly

/-- One original above-mu symmetric Jensen candidate on the stored coordinate
grid. The rational endpoint bindings are representation equalities. The three
factor-query results and the original branch geometry remain explicit. -/
theorem original_stored_symmetric_leaf_candidate
    (x0 x1 : ℤ) (a b c d : ℚ) (fl fh out : ℤ)
    (ha : a=(x0:ℚ)/((48000*2^24:ℤ):ℚ))
    (hb : b=(x1:ℚ)/((48000*2^24:ℤ):ℚ))
    (hg : SymmetricFullBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ))
    (hmu : VariableEnvelope.mu≤(a:ℝ))
    (hlo : 2≤oldLow (b:ℝ) (d:ℝ))
    (hspan : oldLow (b:ℝ) (d:ℝ)<oldHigh (a:ℝ) (c:ℝ))
    (hfl : value fl≤actualExtendedThirdLowerFactor (oldLow (b:ℝ) (d:ℝ)))
    (hfh : value fh≤actualExtendedThirdLowerFactor (oldHigh (a:ℝ) (c:ℝ)))
    (hquery : actualExtendedThirdLowerFactor
      (symmetricNewQuery (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ)
        (originalLnUnit ((b:ℝ)/(a:ℝ))):ℝ)≤value out) :
    (∫ t in compactRegion ∩ symmetricBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ),compactKernel t)≤
      prismMass (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ)*value (meanHigh
        (rawWeight a b c d (originalLnUnit ((b:ℝ)/(a:ℝ)))).lo
        (rawWeight a b c d (originalLnUnit ((b:ℝ)/(a:ℝ)))).hi fl fh out) := by
  have hmuScalar : (25:ℝ)/128≤(a:ℝ) := by
    simpa only [VariableEnvelope.mu] using hmu
  have hrhoScalar : (b:ℝ)≤(19:ℝ)/96 := by
    simpa only [thirdPrefixRho] using hg.upper_rho
  have hguards := original_stored_above_mu_log_guards x0 x1 a b ha hb
    hg.width_xy hmuScalar hrhoScalar
  exact original_symmetric_literal_means_candidate a b c d fl fh out hg hmu
    hguards.1 hguards.2 hlo hspan hfl hfh hquery

end
end ImbalancedChen.OriginalThirdIntegerGuardedLeafSourceOnly
