import ImbalancedChen.ActualThirdOriginalLocalCurvature
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! SOURCEONLY / UNCOMPILED / OPEN30.
The actual normalized lower-factor increment needed by the original second
decay candidate. The genuine coupled derivative and source-factor monotonicity
supply every derivative bound; no Lipschitz or increment premise is assumed.
Literal integer rounding, decay anchors and cell geometry remain separate. -/
namespace ImbalancedChen.OriginalThirdP4AActualLowerIncrementGapBoundSourceOnly

noncomputable section
open Set
open OriginalU2CoupledRecurrenceSourceOnly

/-- Gap in exactly the amplitude normalization of the queried lower factor. -/
def canonicalFactorGap (s : ℝ) : ℝ := upper s-lower s

theorem canonicalFactorGap_eq_actualSieveGap_div_A (s : ℝ) :
    canonicalFactorGap s = actualSieveGap s/A := by
  unfold canonicalFactorGap upper lower thirdTailLowerFactor actualSieveGap A
  ring

theorem canonicalFactorGap_nonneg {s : ℝ} (hs : 2 ≤ s) :
    0 ≤ canonicalFactorGap s := by
  exact sub_nonneg.mpr (lower_le_upper hs)

/-- The actual derivative numerator is bounded by the reference gap one unit
to the left. Both comparisons are supplied by canonical source monotonicity. -/
theorem lower_derivative_numerator_le_reference_gap {s0 s : ℝ}
    (hs0 : 4 ≤ s0) (hs : s0 ≤ s) :
    upper (s-1)-lower s ≤ canonicalFactorGap (s0-1) := by
  have hup : upper (s-1) ≤ upper (s0-1) :=
    upper_antitone_gt_one (by change 1 < s0-1; linarith)
      (by change 1 < s-1; linarith) (by linarith)
  have hlow : lower (s0-1) ≤ lower s :=
    lower_monotone (by change 2 ≤ s0-1; linarith)
      (by change 2 ≤ s; linarith) (by linarith)
  exact sub_le_sub hup hlow

/-- Includes s=s0 and s0=4. The derivative source is valid on the entire
closed interval used later, since all its arguments are strictly above two. -/
theorem lowerSlope_le_reference_gap_div {s0 s : ℝ}
    (hs0 : 4 ≤ s0) (hs : s0 ≤ s) :
    lowerSlope s ≤ canonicalFactorGap (s0-1)/s0 := by
  have hgap := canonicalFactorGap_nonneg (s := s0-1) (by linarith)
  have hnum := lower_derivative_numerator_le_reference_gap hs0 hs
  exact div_le_div₀ hgap hnum (by linarith : 0 < s0) hs

theorem actual_lower_deriv_le_reference_gap_div {s0 s : ℝ}
    (hs0 : 4 ≤ s0) (hs : s0 ≤ s) :
    deriv lower s ≤ canonicalFactorGap (s0-1)/s0 := by
  rw [(hasDerivAt_lower (by linarith : 2 < s)).deriv]
  exact lowerSlope_le_reference_gap_div hs0 hs

/-- Actual MVT increment bound. The lower function here is the genuine
thirdTailLowerFactor, not a caller-supplied function or derivative. -/
theorem lower_increment_le_reference_gap_mul {s0 old new : ℝ}
    (hs0 : 4 ≤ s0) (hold : s0 ≤ old) (hnew : old ≤ new) :
    lower new-lower old ≤ (new-old)*(canonicalFactorGap (s0-1)/s0) := by
  have hc : ContinuousOn lower (Icc old new) := by
    intro s hs
    exact (continuousAt_lower (by linarith [hs.1] : 2 < s)).continuousWithinAt
  have hd : DifferentiableOn ℝ lower (interior (Icc old new)) := by
    intro s hs
    have hs' : s ∈ Ioo old new := by simpa only [interior_Icc] using hs
    exact (hasDerivAt_lower (by linarith [hs'.1] : 2 < s)).differentiableAt.differentiableWithinAt
  have hb : ∀ s ∈ interior (Icc old new),
      deriv lower s ≤ canonicalFactorGap (s0-1)/s0 := by
    intro s hs
    have hs' : s ∈ Ioo old new := by simpa only [interior_Icc] using hs
    exact actual_lower_deriv_le_reference_gap_div hs0 (by linarith [hs'.1])
  have hm := (convex_Icc old new).image_sub_le_mul_sub_of_deriv_le
    hc hd hb old ⟨le_rfl,hnew⟩ new ⟨hnew,le_rfl⟩ hnew
  simpa only [mul_comm] using hm

theorem lower_increment_le_delta_gap {s0 old new delta : ℝ}
    (hs0 : 4 ≤ s0) (hold : s0 ≤ old) (hnew : old ≤ new)
    (hdelta : new-old ≤ delta) :
    lower new-lower old ≤ delta*canonicalFactorGap (s0-1)/s0 := by
  have hC : 0 ≤ canonicalFactorGap (s0-1)/s0 :=
    div_nonneg (canonicalFactorGap_nonneg (by linarith)) (by linarith)
  calc
    lower new-lower old ≤ (new-old)*(canonicalFactorGap (s0-1)/s0) :=
      lower_increment_le_reference_gap_mul hs0 hold hnew
    _ ≤ delta*(canonicalFactorGap (s0-1)/s0) :=
      mul_le_mul_of_nonneg_right hdelta hC
    _ = delta*canonicalFactorGap (s0-1)/s0 := by ring

/-- Same bound for exactly the extended-third lower factor queried by the
original producer. Its max-two extension is paid by old,new>=s0>=4. -/
theorem actualLowerFactor_increment_le_reference_gap_mul {s0 old new : ℝ}
    (hs0 : 4 ≤ s0) (hold : s0 ≤ old) (hnew : old ≤ new) :
    actualExtendedThirdLowerFactor new-actualExtendedThirdLowerFactor old ≤
      (new-old)*(canonicalFactorGap (s0-1)/s0) := by
  rw [← lower_eq_actual (s := new) (by linarith),
    ← lower_eq_actual (s := old) (by linarith)]
  exact lower_increment_le_reference_gap_mul hs0 hold hnew

theorem actualLowerFactor_increment_le_delta_gap {s0 old new delta : ℝ}
    (hs0 : 4 ≤ s0) (hold : s0 ≤ old) (hnew : old ≤ new)
    (hdelta : new-old ≤ delta) :
    actualExtendedThirdLowerFactor new-actualExtendedThirdLowerFactor old ≤
      delta*canonicalFactorGap (s0-1)/s0 := by
  rw [← lower_eq_actual (s := new) (by linarith),
    ← lower_eq_actual (s := old) (by linarith)]
  exact lower_increment_le_delta_gap hs0 hold hnew hdelta

/-- Anchor adapter: `anchor` is a real enclosure of the actual canonical gap,
not an assumed increment/Lipschitz estimate. Integer decay suppliers may
instantiate it from the already proved quadratic source-gap decay. -/
theorem actualLowerFactor_increment_le_delta_anchor {s0 old new delta anchor : ℝ}
    (hs0 : 4 ≤ s0) (hold : s0 ≤ old) (hnew : old ≤ new)
    (hdelta : new-old ≤ delta) (hanchor : canonicalFactorGap (s0-1) ≤ anchor) :
    actualExtendedThirdLowerFactor new-actualExtendedThirdLowerFactor old ≤
      delta*anchor/s0 := by
  have hdelta0 : 0 ≤ delta := (sub_nonneg.mpr hnew).trans hdelta
  calc
    actualExtendedThirdLowerFactor new-actualExtendedThirdLowerFactor old ≤
        delta*canonicalFactorGap (s0-1)/s0 :=
      actualLowerFactor_increment_le_delta_gap hs0 hold hnew hdelta
    _ ≤ delta*anchor/s0 := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hanchor hdelta0) (by linarith)

theorem actualLowerFactor_increment_le_delta_normalized_source_gap
    {s0 old new delta : ℝ} (hs0 : 4 ≤ s0) (hold : s0 ≤ old)
    (hnew : old ≤ new) (hdelta : new-old ≤ delta) :
    actualExtendedThirdLowerFactor new-actualExtendedThirdLowerFactor old ≤
      delta*(actualSieveGap (s0-1)/A)/s0 := by
  simpa only [canonicalFactorGap_eq_actualSieveGap_div_A] using
    actualLowerFactor_increment_le_delta_gap hs0 hold hnew hdelta

/-- Exact shape of the original second-decay candidate before integer UP.
The cell supplier only pays argument geometry; the derivative estimate was
proved above from the actual canonical factors. `capGap` is T-ca. -/
theorem actualLowerFactor_increment_le_original_second_decay_gap
    {ao z0 z1 capGap old new : ℝ}
    (hz0 : 0 < z0) (hz1 : 0 < z1) (hgate : 4*z1 ≤ ao)
    (hold : ao/z1 ≤ old) (hnew : old ≤ new)
    (hdelta : new-old ≤ capGap/z0) :
    actualExtendedThirdLowerFactor new-actualExtendedThirdLowerFactor old ≤
      canonicalFactorGap ((ao-z1)/z1)*capGap*z1/(z0*ao) := by
  have hs0 : (4:ℝ) ≤ ao/z1 := (le_div_iff₀ hz1).2 hgate
  have hao : 0 < ao := (mul_pos (by norm_num : (0:ℝ) < 4) hz1).trans_le hgate
  have hshift : ao/z1-1 = (ao-z1)/z1 := by
    field_simp [hz1.ne']
    <;> ring
  calc
    actualExtendedThirdLowerFactor new-actualExtendedThirdLowerFactor old ≤
        (capGap/z0)*canonicalFactorGap (ao/z1-1)/(ao/z1) :=
      actualLowerFactor_increment_le_delta_gap hs0 hold hnew hdelta
    _ = canonicalFactorGap ((ao-z1)/z1)*capGap*z1/(z0*ao) := by
      rw [hshift]
      field_simp [hz0.ne', hz1.ne', hao.ne']
      <;> ring

/-- Same original shape with an independently supplied actual gap anchor.
It may be the real value of decay(ao-z1,z1); no final integer rounding or
target cell cost inequality is assumed here. -/
theorem actualLowerFactor_increment_le_original_second_decay_anchor
    {ao z0 z1 capGap old new anchor : ℝ}
    (hz0 : 0 < z0) (hz1 : 0 < z1) (hgate : 4*z1 ≤ ao)
    (hold : ao/z1 ≤ old) (hnew : old ≤ new)
    (hdelta : new-old ≤ capGap/z0)
    (hanchor : canonicalFactorGap ((ao-z1)/z1) ≤ anchor) :
    actualExtendedThirdLowerFactor new-actualExtendedThirdLowerFactor old ≤
      anchor*capGap*z1/(z0*ao) := by
  have hs0 : (4:ℝ) ≤ ao/z1 := (le_div_iff₀ hz1).2 hgate
  have hao : 0 < ao := (mul_pos (by norm_num : (0:ℝ) < 4) hz1).trans_le hgate
  have hshift : ao/z1-1 = (ao-z1)/z1 := by
    field_simp [hz1.ne']
    <;> ring
  have ha : canonicalFactorGap (ao/z1-1) ≤ anchor := by
    simpa only [hshift] using hanchor
  calc
    actualExtendedThirdLowerFactor new-actualExtendedThirdLowerFactor old ≤
        (capGap/z0)*anchor/(ao/z1) :=
      actualLowerFactor_increment_le_delta_anchor hs0 hold hnew hdelta ha
    _ = anchor*capGap*z1/(z0*ao) := by
      field_simp [hz0.ne', hz1.ne', hao.ne']
      <;> ring

end
end ImbalancedChen.OriginalThirdP4AActualLowerIncrementGapBoundSourceOnly
