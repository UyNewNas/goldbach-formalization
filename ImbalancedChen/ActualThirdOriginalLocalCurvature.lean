import ImbalancedChen.ActualThirdOriginalCoupledRecurrence
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
SOURCEONLY continuation: actual normalized factors and their derivative bounds.
The previous peer-V3 source is included verbatim above in the standalone draft.
No synthetic DDE, target node enclosure or numerical curvature premise is used.
-/
namespace ImbalancedChen.OriginalU2CoupledRecurrenceSourceOnly

noncomputable section
open Set MeasureTheory Filter Topology
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

/-- The genuine upper initial strip, with the amplitude normalized exactly. -/
theorem upper_eq_inv {s : ℝ} (hs1 : 1 < s) (hs3 : s ≤ 3) :
    upper s = 1/s := by
  have h := mul_suzukiProposition118SourceTPlus_eq_amplitude_sub
    jr1965Section13HatSourceContract hs1 hs3
  have hA : suzukiLowerSieveAmplitude = A := by
    simpa only [A] using
      suzukiLowerSieveAmplitude_eq_two_mul_exp_eulerMascheroni_of_sourceContract
        jr1965Section13HatSourceContract
  rw [hA] at h
  rw [upper_source]
  apply (div_eq_div_iff (ne_of_gt A_pos) (by linarith : s ≠ 0)).2
  nlinarith only [h]

theorem H_eq_one {s : ℝ} (hs1 : 1 < s) (hs3 : s ≤ 3) : H s = 1 := by
  rw [H, upper_eq_inv hs1 hs3]
  field_simp [ne_of_gt (by linarith : 0 < s)]

theorem lower_eq_log {s : ℝ} (hs2 : 2 ≤ s) (hs4 : s ≤ 4) :
    lower s = Real.log (s-1)/s := by
  have hA := suzukiLowerSieveAmplitude_eq_two_mul_exp_eulerMascheroni_of_sourceContract
    jr1965Section13HatSourceContract
  rw [lower, thirdTailLowerFactor, suzukiContinuousLowerFactor,
    suzukiContinuousLowerTail,
    one_sub_suzukiProposition118SourceTMinus_eq_lowerSieveFactorFirstInterval
      jr1965Section13HatSourceContract hs2 hs4,
    suzukiLowerSieveFactorFirstInterval_eq_log hs2 hs4, hA]
  field_simp [ne_of_gt (Real.exp_pos Real.eulerMascheroniConstant)]

theorem L_eq_log {s : ℝ} (hs2 : 2 ≤ s) (hs4 : s ≤ 4) :
    L s = Real.log (s-1) := by
  rw [L, lower_eq_log hs2 hs4]
  field_simp [ne_of_gt (by linarith : 0 < s)]

/-- The source odd series is antitone on its full open source domain. -/
theorem upper_antitone_gt_one : AntitoneOn upper (Ioi 1) := by
  intro x hx y hy hxy
  change 1 < x at hx
  change 1 < y at hy
  have hplus : suzukiProposition118SourceTPlus y ≤
      suzukiProposition118SourceTPlus x := by
    apply Summable.tsum_le_tsum _
      (summable_suzukiProposition118SourceTPlus_of_sourceContract
        jr1965Section13HatSourceContract hy)
      (summable_suzukiProposition118SourceTPlus_of_sourceContract
        jr1965Section13HatSourceContract hx)
    intro k
    exact suzukiLayer_one_antitoneOn_parityDomain (by norm_num) (2*k+1)
      (by simp [suzukiParityDomainOne, KappaOneModel.parityDomain]; linarith)
      (by simp [suzukiParityDomainOne, KappaOneModel.parityDomain]; linarith) hxy
  simpa only [upper, suzukiContinuousUpperFactor, add_comm] using
    (div_le_div_of_nonneg_right (add_le_add_left hplus 1) A_pos.le)

theorem lower_nonneg {s : ℝ} (hs : 2 ≤ s) : 0 ≤ lower s := by
  rw [lower_eq_actual hs]
  exact actualExtendedThirdLowerFactor_nonneg s

theorem lower_le_upper {s : ℝ} (hs : 2 ≤ s) : lower s ≤ upper s := by
  have h := div_nonneg (actualSieveGap_nonneg hs) A_pos.le
  change 0 ≤ (suzukiContinuousUpperFactor s - suzukiContinuousLowerFactor s)/A at h
  change suzukiContinuousLowerFactor s/A ≤ suzukiContinuousUpperFactor s/A
  rw [sub_div] at h
  exact sub_nonneg.mp h

theorem upper_le_half {s : ℝ} (hs : 2 ≤ s) : upper s ≤ 1/2 := by
  have h := upper_antitone
    (show (2 : ℝ) ∈ Ici 2 from by change (2 : ℝ) ≤ 2; exact le_rfl) hs hs
  simpa only [upper_eq_inv (by norm_num : (1 : ℝ) < 2) (by norm_num : (2 : ℝ) ≤ 3)] using h

theorem factors_range {s : ℝ} (hs : 2 ≤ s) :
    0 ≤ lower s ∧ lower s ≤ upper s ∧ upper s ≤ 1/2 :=
  ⟨lower_nonneg hs, lower_le_upper hs, upper_le_half hs⟩

theorem upper_le_one {s : ℝ} (hs : 1 < s) : upper s ≤ 1 := by
  by_cases hs2 : 2 ≤ s
  · exact (upper_le_half hs2).trans (by norm_num)
  · rw [upper_eq_inv hs (by linarith)]
    exact (div_le_one (by linarith : 0 < s)).2 hs.le

theorem continuousAt_lower {s : ℝ} (hs : 2 < s) : ContinuousAt lower s := by
  exact continuousOn_thirdTailLowerFactor.continuousAt (Ici_mem_nhds hs)

/-- Continuity of the upper factor comes from the genuine source gap and lower
factor. It is not an assumed continuity property of a numerical table. -/
theorem continuousAt_upper {s : ℝ} (hs : 2 < s) : ContinuousAt upper s := by
  have hq := continuousAt_suzukiProposition118SourceQ_of_two_lt
    jr1965Section13HatSourceContract hs
  apply ((continuousAt_lower hs).add (hq.div_const A)).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hs] with u hu
  have hqeq := actualSieveGap_eq_source hu.le
  dsimp
  rw [← hqeq]
  unfold upper lower thirdTailLowerFactor actualSieveGap A
  ring

/-- The lower numerator derivative above three, directly from the actual
coupled integral recurrence and FTC. -/
theorem hasDerivAt_L_tail {s : ℝ} (hs : 3 < s) :
    HasDerivAt L (upper (s-1)) s := by
  let g : ℝ → ℝ := fun t => upper (t-1)
  have hg := (shifted_factors_integrable (x := 3) (by norm_num) hs.le).1
  have hcont (u : ℝ) (hu : 3 < u) : ContinuousAt g u := by
    exact (continuousAt_upper (s := u-1) (by linarith : 2 < u-1)).comp
      (f := fun v : ℝ => v-1) (x := u)
      (continuousAt_id.sub continuousAt_const)
  have hmeas : StronglyMeasurableAtFilter g (𝓝 s) volume := by
    apply ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioi
      (s := Ioi (3 : ℝ)) _ s hs
    intro u hu
    exact hcont u hu
  have hp := intervalIntegral.integral_hasDerivAt_right hg hmeas (hcont s hs)
  have hb := hp.const_add (L 3)
  apply hb.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hs] with u hu
  have h := L_sub (x := 3) (by norm_num) hu.le
  linarith only [h]

theorem hasDerivAt_H_tail {s : ℝ} (hs : 3 < s) :
    HasDerivAt H (lower (s-1)) s := by
  let g : ℝ → ℝ := fun t => lower (t-1)
  have hg := (shifted_factors_integrable (x := 3) (by norm_num) hs.le).2
  have hcont (u : ℝ) (hu : 3 < u) : ContinuousAt g u := by
    exact (continuousAt_lower (s := u-1) (by linarith : 2 < u-1)).comp
      (f := fun v : ℝ => v-1) (x := u)
      (continuousAt_id.sub continuousAt_const)
  have hmeas : StronglyMeasurableAtFilter g (𝓝 s) volume := by
    apply ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioi
      (s := Ioi (3 : ℝ)) _ s hs
    intro u hu
    exact hcont u hu
  have hp := intervalIntegral.integral_hasDerivAt_right hg hmeas (hcont s hs)
  have hb := hp.const_add (H 3)
  apply hb.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hs] with u hu
  have h := H_sub (x := 3) (by norm_num) hu.le
  linarith only [h]

/-- The actual lower numerator DDE holds on all s>2, using its logarithmic
initial strip where the above-three integral representation is unavailable. -/
theorem hasDerivAt_L {s : ℝ} (hs : 2 < s) :
    HasDerivAt L (upper (s-1)) s := by
  by_cases hs4 : s < 4
  · have hn : s-1 ≠ 0 := by linarith
    have hd := HasDerivAt.comp_sub_const (f := Real.log) s 1 (Real.hasDerivAt_log hn)
    have hd' : HasDerivAt (fun u : ℝ => Real.log (u-1)) (upper (s-1)) s := by
      rw [upper_eq_inv (by linarith : 1 < s-1) (by linarith : s-1 ≤ 3)]
      simpa only [one_div] using hd
    apply hd'.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds hs hs4] with u hu
    exact L_eq_log hu.1.le hu.2.le
  · exact hasDerivAt_L_tail (by linarith)

/-- Explicit derivatives of the actual normalized factors. -/
def lowerSlope (s : ℝ) : ℝ := (upper (s-1) - lower s)/s
def upperSlope (s : ℝ) : ℝ := (lower (s-1) - upper s)/s

theorem hasDerivAt_lower {s : ℝ} (hs : 2 < s) :
    HasDerivAt lower (lowerSlope s) s := by
  have hs0 : s ≠ 0 := by linarith
  have hd := (hasDerivAt_L hs).fun_div (hasDerivAt_id s) hs0
  have hd' : HasDerivAt (fun u => L u/u) (lowerSlope s) s := by
    apply hd.congr_deriv
    change (upper (s-1)*s-(s*lower s)*1)/s^2 = (upper (s-1)-lower s)/s
    apply (div_eq_div_iff (pow_ne_zero 2 hs0) hs0).2
    ring
  apply hd'.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hs] with u hu
  change 2 < u at hu
  have hu0 : u ≠ 0 := by linarith
  simp [L, hu0]

theorem hasDerivAt_upper_tail {s : ℝ} (hs : 3 < s) :
    HasDerivAt upper (upperSlope s) s := by
  have hs0 : s ≠ 0 := by linarith
  have hd := (hasDerivAt_H_tail hs).fun_div (hasDerivAt_id s) hs0
  have hd' : HasDerivAt (fun u => H u/u) (upperSlope s) s := by
    apply hd.congr_deriv
    change (lower (s-1)*s-(s*upper s)*1)/s^2 = (lower (s-1)-upper s)/s
    apply (div_eq_div_iff (pow_ne_zero 2 hs0) hs0).2
    ring
  apply hd'.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hs] with u hu
  change 3 < u at hu
  have hu0 : u ≠ 0 := by linarith
  simp [H, hu0]

theorem hasDerivAt_upper_base {s : ℝ} (hs1 : 1 < s) (hs3 : s < 3) :
    HasDerivAt upper (-(s^2)⁻¹) s := by
  have hd := hasDerivAt_inv (by linarith : s ≠ 0)
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hs1 hs3] with u hu
  simpa only [one_div] using upper_eq_inv hu.1 hu.2.le

/-- The sharp bound needed for numerator curvature, with no derivative-sign
hypothesis. Order and the explicit initial upper normalization supply it. -/
theorem lowerSlope_bounds {s : ℝ} (hs : 2 < s) :
    0 ≤ lowerSlope s ∧ lowerSlope s ≤ 1/s := by
  have hs0 : 0 < s := by linarith
  have hlow := lower_nonneg hs.le
  have hup := upper_le_one (by linarith : 1 < s-1)
  have horder : lower s ≤ upper (s-1) :=
    (lower_le_upper hs.le).trans
      (upper_antitone_gt_one (by change 1 < s-1; linarith)
        (by change 1 < s; linarith) (by linarith))
  constructor
  · exact div_nonneg (sub_nonneg.mpr horder) hs0.le
  · exact div_le_div_of_nonneg_right (by linarith : upper (s-1)-lower s ≤ 1) hs0.le

theorem upperSlope_bounds {s : ℝ} (hs : 3 < s) :
    -(1/s) ≤ upperSlope s ∧ upperSlope s ≤ 0 := by
  have hs0 : 0 < s := by linarith
  have hlow := lower_nonneg (by linarith : 2 ≤ s-1)
  have hup := upper_le_half (by linarith : 2 ≤ s)
  have horder : lower (s-1) ≤ upper s :=
    (lower_monotone (by change 2 ≤ s-1; linarith)
      (by change 2 ≤ s; linarith) (by linarith)).trans (lower_le_upper (by linarith))
  constructor
  · have h := div_le_div_of_nonneg_right
      (by linarith : (-1 : ℝ) ≤ lower (s-1)-upper s) hs0.le
    simpa only [neg_div, lowerSlope, upperSlope] using h
  · exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr horder) hs0.le

/-- Curvature coefficients for the actual numerator derivatives. -/
def Lcurvature (s : ℝ) : ℝ :=
  if s < 4 then -((s-1)^2)⁻¹ else upperSlope (s-1)
def Hcurvature (s : ℝ) : ℝ := lowerSlope (s-1)

theorem hasDerivAt_Lprime {s : ℝ} (hs : 2 < s) (hs4 : s ≠ 4) :
    HasDerivAt (fun u => upper (u-1)) (Lcurvature s) s := by
  by_cases hlt : s < 4
  · have hd := HasDerivAt.comp_sub_const (f := upper) s 1
      (hasDerivAt_upper_base (s := s-1) (by linarith : 1 < s-1)
        (by linarith : s-1 < 3))
    simpa only [Lcurvature, if_pos hlt] using hd
  · have hd := HasDerivAt.comp_sub_const (f := upper) s 1
      (hasDerivAt_upper_tail (s := s-1)
        (by have h4 := lt_of_le_of_ne (not_lt.mp hlt) hs4.symm; linarith : 3 < s-1))
    simpa only [Lcurvature, if_neg hlt] using hd

theorem hasDerivAt_Hprime {s : ℝ} (hs : 3 < s) :
    HasDerivAt (fun u => lower (u-1)) (Hcurvature s) s := by
  have hd := HasDerivAt.comp_sub_const (f := lower) s 1
    (hasDerivAt_lower (s := s-1) (by linarith : 2 < s-1))
  simpa only [Hcurvature] using hd

theorem Lcurvature_bounds {s : ℝ} (hs : 2 < s) (hs4 : s ≠ 4) :
    -(1/(s-1)) ≤ Lcurvature s ∧ Lcurvature s ≤ 0 := by
  by_cases hlt : s < 4
  · rw [Lcurvature, if_pos hlt]
    have hden : s-1 ≤ (s-1)^2 := by nlinarith
    have h := one_div_le_one_div_of_le (by linarith : 0 < s-1) hden
    constructor
    · simpa only [one_div] using neg_le_neg h
    · exact neg_nonpos.mpr (inv_nonneg.mpr (sq_nonneg _))
  · rw [Lcurvature, if_neg hlt]
    exact upperSlope_bounds (by have h4 := lt_of_le_of_ne (not_lt.mp hlt) hs4.symm; linarith : 3 < s-1)

theorem Hcurvature_bounds {s : ℝ} (hs : 3 < s) :
    0 ≤ Hcurvature s ∧ Hcurvature s ≤ 1/(s-1) := by
  exact lowerSlope_bounds (by linarith : 2 < s-1)

/-- On an arbitrary original lower-numerator cell, four cannot be an interior
point. Thus the exact local 1/(left-1) curvature is available throughout the
interior without assuming C2 across the delay knot at four. -/
theorem original_L_cell_curvature (i : ℕ) (hi : 32768 ≤ i)
    {s : ℝ} (hs : s ∈ Ioo ((i : ℝ)/16384) (((i : ℝ)+1)/16384)) :
    HasDerivAt L (upper (s-1)) s ∧
    HasDerivAt (fun u => upper (u-1)) (Lcurvature s) s ∧
    -(1/((i : ℝ)/16384-1)) ≤ Lcurvature s ∧ Lcurvature s ≤ 0 := by
  have hiR : (32768 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  have hs2 : 2 < s := by linarith [hs.1]
  have hs4 : s ≠ 4 := by
    by_cases hi4 : i < 65536
    · have hi4R : (i : ℝ)+1 ≤ 65536 := by exact_mod_cast (show i+1 ≤ 65536 by omega)
      linarith [hs.2]
    · have hi4R : (65536 : ℝ) ≤ (i : ℝ) := by exact_mod_cast (Nat.le_of_not_gt hi4)
      linarith [hs.1]
  have hb := Lcurvature_bounds hs2 hs4
  have hinv := one_div_le_one_div_of_le
    (by linarith : 0 < (i : ℝ)/16384-1)
    (by linarith [hs.1] : (i : ℝ)/16384-1 ≤ s-1)
  exact ⟨hasDerivAt_L hs2, hasDerivAt_Lprime hs2 hs4,
    (neg_le_neg hinv).trans hb.1, hb.2⟩

/-- Original upper-numerator query cells start at three; H is exactly one
below that cutoff. Every nonconstant cell has the original local curvature. -/
theorem original_H_cell_curvature (i : ℕ) (hi : 49152 ≤ i)
    {s : ℝ} (hs : s ∈ Ioo ((i : ℝ)/16384) (((i : ℝ)+1)/16384)) :
    HasDerivAt H (lower (s-1)) s ∧
    HasDerivAt (fun u => lower (u-1)) (Hcurvature s) s ∧
    0 ≤ Hcurvature s ∧ Hcurvature s ≤ 1/((i : ℝ)/16384-1) := by
  have hiR : (49152 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  have hs3 : 3 < s := by linarith [hs.1]
  have hb := Hcurvature_bounds hs3
  have hinv := one_div_le_one_div_of_le
    (by linarith : 0 < (i : ℝ)/16384-1)
    (by linarith [hs.1] : (i : ℝ)/16384-1 ≤ s-1)
  exact ⟨hasDerivAt_H_tail hs3, hasDerivAt_Hprime hs3, hb.1, hb.2.trans hinv⟩


/-- Closed-domain continuity supplies the endpoint hypothesis needed by a
future convexity/chord wrapper. No second derivative is demanded at a knot. -/
theorem continuousOn_L : ContinuousOn L (Ici 2) := by
  exact continuousOn_id.mul continuousOn_thirdTailLowerFactor

theorem continuousOn_H : ContinuousOn H (Ici 3) := by
  intro s hs
  exact (continuousAt_id.mul
    (continuousAt_upper (by change 3 ≤ s at hs; linarith))).continuousWithinAt

/-- The resulting real chord allowance is precisely the original local
query allowance before its upward integer rounding. -/
theorem original_cell_curvature_allowance (i : ℕ) (hi : 32768 ≤ i) :
    (1/((i : ℝ)/16384-1)) * (1/16384)^2 / 8 =
      1/(8*16384*((i : ℝ)-16384)) := by
  have hiR : (32768 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  have hd : (i : ℝ)-16384 ≠ 0 := by linarith
  have hd' : (i : ℝ)/16384-1 ≠ 0 := by linarith
  field_simp [hd, hd']

/-- Only the first lower cell has exactly this unrounded 112-bit allowance.
Later cells keep their smaller local formula. -/
theorem original_first_cell_curvature_112bit :
    (2^112 : ℝ) * ((1/((32768 : ℝ)/16384-1)) * (1/16384)^2 / 8) = 2^81 := by
  norm_num

end
end ImbalancedChen.OriginalU2CoupledRecurrenceSourceOnly
