import ImbalancedChen.ActualThirdOriginalP4AUnsafeSymmetricSelectorWitness
import ImbalancedChen.ActualThirdOriginalP4ASymmetricSafeChordDirection

/-! SOURCEONLY / UNCOMPILED / OPEN30.
The exact correction between the producer square OLD chord and the actual
triangle OLD chord at a source-selected xz/fall witness. Strict query ordering
remains a separate primitive comparison; no saved leaf failure is asserted. -/
namespace ImbalancedChen.OriginalThirdP4AUnsafeSymmetricChordGapSourceOnly

noncomputable section
open Set MeasureTheory
open OriginalThirdBoxMomentsSourceOnly OriginalThirdOldChordMeanSourceOnly
open OriginalThirdSixTentCandidatesSourceOnly
open OriginalThirdTriangleMomentsSourceOnly OriginalThirdSymmetricJensenSourceOnly
open OriginalThirdSortedHalfIntegralSourceOnly
open OriginalThirdP4ASymmetricTentPrerequisites
open OriginalThirdP4ASymmetricSafeChordDirection
open OriginalThirdP4AUnsafeSymmetricSelectorWitnessSourceOnly

/-- Strictness follows from the actual closed triangle moment, using the
pinned Mathlib logarithm inequality, not a floating-point log estimate. -/
theorem triangle_squareEx_lt_maxMean {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    (b-a)/Real.log (b/a) < maxMean a b := by
  have hb : 0 < b := ha.trans hab
  have hx : 0 < (b-a)/a := div_pos (sub_pos.mpr hab) ha
  have hbound := Real.lt_log_one_add_of_pos hx
  have hratio : 1+(b-a)/a = b/a := by
    field_simp [ha.ne']
    <;> ring
  have hden : (b-a)/a+2 = (a+b)/a := by
    field_simp [ha.ne']
    <;> ring
  have hsum : 0 < a+b := add_pos ha hb
  have hfrac : 2*((b-a)/a)/((b-a)/a+2) = 2*(b-a)/(a+b) := by
    rw [hden]
    field_simp [ha.ne', hsum.ne']
    <;> ring
  rw [hratio, hfrac] at hbound
  have hnum : 0 < (a+b)*Real.log (b/a)-2*(b-a) := by
    have hh := (div_lt_iff₀ hsum).mp hbound
    nlinarith
  have hlog : 0 < Real.log (b/a) := Real.log_pos ((one_lt_div ha).2 hab)
  have hgap : maxMean a b-(b-a)/Real.log (b/a) =
      ((a+b)*Real.log (b/a)-2*(b-a))/(Real.log (b/a))^2 := by
    unfold maxMean
    field_simp [hlog.ne']
    <;> ring
  apply sub_pos.mp
  rw [hgap]
  exact div_pos hnum (sq_pos_of_pos hlog)

theorem producer_mean_sub_ordered_mean (s : TentSum) (k : TentSide)
    (a b c d : ℝ) :
    tentOldMean s k (symmetricLeft a c) (symmetricRight b d)-
        orderedTentMean s k a b c d =
      (oldY s k-oldX s k)*(maxMean a b-(b-a)/Real.log (b/a))*invZMean c d := by
  calc
    _ = -(orderedTentMean s k a b c d-
        tentOldMean s k (symmetricLeft a c) (symmetricRight b d)) := by ring
    _ = _ := by rw [ordered_mean_sub_producer_mean]; ring

/-- Exact producer minus ordered chord, valid even for totalized zero span. -/
theorem producer_chord_sub_ordered_chord (s : TentSum) (k : TentSide)
    (a b c d flo fhi : ℝ) :
    tentOldChord s k (symmetricLeft a c) (symmetricRight b d) flo fhi-
        orderedTentChord s k a b c d flo fhi =
      (tentOldMean s k (symmetricLeft a c) (symmetricRight b d)-
          orderedTentMean s k a b c d)/
        (tentOldHigh s k (symmetricLeft a c)-tentOldLow s k (symmetricRight b d))*
        (fhi-flo) := by
  unfold tentOldChord orderedTentChord
  ring

theorem xz_fall_producer_chord_gap (a b c d flo fhi : ℝ) :
    tentOldChord .xz .fall (symmetricLeft a c) (symmetricRight b d) flo fhi-
        orderedTentChord .xz .fall a b c d flo fhi =
      ((3/2:ℝ)*(maxMean a b-(b-a)/Real.log (b/a))*invZMean c d)/
        (tentOldHigh .xz .fall (symmetricLeft a c)-
          tentOldLow .xz .fall (symmetricRight b d))*(fhi-flo) := by
  rw [producer_chord_sub_ordered_chord, producer_mean_sub_ordered_mean]
  norm_num [oldX, oldY, planeSlope, sumX, sumY]

def witnessCoordinateGap : ℝ :=
  maxMean (21/128) (169/1024)-
    ((169/1024)-(21/128))/Real.log ((169/1024)/(21/128))

def witnessChordGap (flo fhi : ℝ) : ℝ :=
  (12480/109:ℝ)*witnessCoordinateGap*(fhi-flo)

theorem witnessCoordinateGap_pos : 0 < witnessCoordinateGap := by
  exact sub_pos.mpr (triangle_squareEx_lt_maxMean (by norm_num) (by norm_num))

theorem witness_span_and_inverse_z :
    tentOldHigh .xz .fall (symmetricLeft (21/128) (1/32))-
        tentOldLow .xz .fall (symmetricRight (169/1024) (33/1024)) = 109/264 ∧
    (0:ℝ) < 109/264 ∧ invZMean (1/32) (33/1024) = 1040/33 := by
  norm_num [tentOldLow, tentOldHigh, tentOldArgument, affineArgument,
    symmetricLeft, symmetricRight, oldX, oldY, oldZ, planeConst, planeSlope,
    sumX, sumY, sumZ, invZMean]

theorem witness_mean_gap_exact :
    tentOldMean .xz .fall (symmetricLeft (21/128) (1/32))
        (symmetricRight (169/1024) (33/1024))-
      orderedTentMean .xz .fall (21/128) (169/1024) (1/32) (33/1024) =
        (520/11:ℝ)*witnessCoordinateGap := by
  rw [producer_mean_sub_ordered_mean]
  change (oldY .xz .fall-oldX .xz .fall)*witnessCoordinateGap*
    invZMean (1/32) (33/1024) = _
  norm_num [oldX, oldY, planeSlope, sumX, sumY, invZMean]
  <;> ring

theorem witness_ordered_mean_lt_producer_mean :
    orderedTentMean .xz .fall (21/128) (169/1024) (1/32) (33/1024) <
      tentOldMean .xz .fall (symmetricLeft (21/128) (1/32))
        (symmetricRight (169/1024) (33/1024)) := by
  apply sub_pos.mp
  rw [witness_mean_gap_exact]
  exact mul_pos (by norm_num) witnessCoordinateGap_pos

theorem witness_producer_chord_gap_exact (flo fhi : ℝ) :
    tentOldChord .xz .fall (symmetricLeft (21/128) (1/32))
        (symmetricRight (169/1024) (33/1024)) flo fhi-
      orderedTentChord .xz .fall (21/128) (169/1024) (1/32) (33/1024) flo fhi =
        witnessChordGap flo fhi := by
  rw [producer_chord_sub_ordered_chord, witness_mean_gap_exact,
    witness_span_and_inverse_z.1]
  unfold witnessChordGap
  ring

theorem witnessChordGap_nonneg {flo fhi : ℝ} (hquery : flo ≤ fhi) :
    0 ≤ witnessChordGap flo fhi := by
  exact mul_nonneg (mul_nonneg (by norm_num) witnessCoordinateGap_pos.le)
    (sub_nonneg.mpr hquery)

/-- The only strictness premise here is the primitive query-output gap. -/
theorem witnessChordGap_pos {flo fhi : ℝ} (hquery : flo < fhi) :
    0 < witnessChordGap flo fhi := by
  exact mul_pos (mul_pos (by norm_num) witnessCoordinateGap_pos) (sub_pos.mpr hquery)

theorem witness_ordered_chord_lt_producer_of_query_lt {flo fhi : ℝ}
    (hquery : flo < fhi) :
    orderedTentChord .xz .fall (21/128) (169/1024) (1/32) (33/1024) flo fhi <
      tentOldChord .xz .fall (symmetricLeft (21/128) (1/32))
        (symmetricRight (169/1024) (33/1024)) flo fhi := by
  apply sub_pos.mp
  rw [witness_producer_chord_gap_exact]
  exact witnessChordGap_pos hquery

theorem witnessChordGap_flat (f : ℝ) : witnessChordGap f f = 0 := by
  simp only [witnessChordGap, sub_self, mul_zero]

theorem witness_ordered_chord_eq_producer_sub_gap (flo fhi : ℝ) :
    orderedTentChord .xz .fall (21/128) (169/1024) (1/32) (33/1024) flo fhi =
      tentOldChord .xz .fall (symmetricLeft (21/128) (1/32))
        (symmetricRight (169/1024) (33/1024)) flo fhi-witnessChordGap flo fhi := by
  linarith [witness_producer_chord_gap_exact flo fhi]

/-- A real correction supplier: subtracting the explicit gap recovers the
proved triangle chord and hence an actual OLD factor integral lower bound.
The two primitive factor-query bounds stay explicit; no desired integral
inequality or producer-to-triangle comparison is assumed. -/
theorem witness_corrected_chord_le_actual_integral (flo fhi : ℝ)
    (hfl : flo ≤ actualExtendedThirdLowerFactor (238/33))
    (hfh : fhi ≤ actualExtendedThirdLowerFactor (61/8)) :
    tentOldChord .xz .fall (symmetricLeft (21/128) (1/32))
        (symmetricRight (169/1024) (33/1024)) flo fhi-witnessChordGap flo fhi ≤
      ∫ p, actualExtendedThirdLowerFactor (actualPrismOld p)
        ∂prismProbability (21/128) (169/1024) (1/32) (33/1024) := by
  have hloEq : tentOldLow .xz .fall (symmetricRight (169/1024) (33/1024)) =
      238/33 := by
    simpa only [symmetricRight] using witness_old_support_and_unsafe_coefficients.1
  have hhiEq : tentOldHigh .xz .fall (symmetricLeft (21/128) (1/32)) = 61/8 := by
    simpa only [symmetricLeft] using witness_old_support_and_unsafe_coefficients.2.1
  have hactive : sourceActive .xz .fall (symmetricLeft (21/128) (1/32))
      (symmetricRight (169/1024) (33/1024)) := by
    norm_num [sourceActive, sourceDelta, tentPlane, tentSum, planeConst,
      planeSlope, sumX, sumY, sumZ, symmetricLeft, symmetricRight]
  have hroot : planeUpper .xz .fall (symmetricLeft (21/128) (1/32))
      (symmetricRight (169/1024) (33/1024)) ≤ thirdPrefixTheta := by
    norm_num [planeUpper, tentPlane, tentSum, planeConst, planeSlope,
      sumX, sumY, sumZ, symmetricLeft, thirdPrefixTheta]
  have hres : 0 < oldNumerator .xz .fall (symmetricRight (169/1024) (33/1024)) := by
    norm_num [oldNumerator, oldX, oldY, planeConst, planeSlope,
      sumX, sumY, symmetricRight]
  have hi := symmetric_tent_chord_le_actual_integral .xz .fall
    witness_symmetric_full_box (by norm_num [VariableEnvelope.mu]) hactive hroot hres
    (by rw [hloEq]; norm_num) (by rw [hloEq]; exact hfl) (by rw [hhiEq]; exact hfh)
  rw [witness_ordered_chord_eq_producer_sub_gap] at hi
  exact hi

end
end ImbalancedChen.OriginalThirdP4AUnsafeSymmetricChordGapSourceOnly
