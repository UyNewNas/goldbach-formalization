import ImbalancedChen.ActualThirdOriginalLocalCurvature
import ImbalancedChen.Certificates.P2HistoricJTableInterpreter

/-! Ordinary normalized Suzuki upper factor in the original fourth
integral, including its actual derivative at the transition point 3. -/
namespace ImbalancedChen.P1OriginalFourthDerivativeNumerator
noncomputable section
open Set MeasureTheory Filter Topology
open scoped Interval
open OriginalU2CoupledRecurrenceSourceOnly
open Certificates.P2HistoricJTableInterpreter (q q_monotone)

def numerator (s : ℝ) : ℝ := -(s^2) * deriv upper s

private def stopped (s : ℝ) : ℝ :=
  Real.log (max 1 (s-2)) / (max 1 (s-2) + 1)

private theorem stopped_continuous : Continuous stopped := by
  have hm : Continuous (fun s : ℝ => max 1 (s-2)) := continuous_const.max (continuous_id.sub continuous_const)
  have hp (s : ℝ) : 0 < max 1 (s-2) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  exact (hm.log (fun s => (hp s).ne')).div (hm.add continuous_const) (fun s => by linarith [hp s])

private theorem stopped_left {s : ℝ} (hs : s ≤ 3) : stopped s = 0 := by
  simp [stopped,max_eq_left (by linarith : s-2 ≤ 1)]

private theorem stopped_right {s : ℝ} (hs : 3 ≤ s) : stopped s = q (s-1) := by
  rw [stopped,max_eq_right (by linarith : 1 ≤ s-2),q]
  ring_nf

theorem lower_shift {s : ℝ} (ha : 3 ≤ s) (hb : s ≤ 5) : lower (s-1) = q (s-1) := by
  exact lower_eq_log (by linarith) (by linarith)

private theorem H_eq_primitive {s : ℝ} (ha : 1 < s) (hb : s ≤ 5) :
    H s = 1 + ∫ t in (3:ℝ)..s, stopped t := by
  by_cases hs : s ≤ 3
  · have he : (∫ t in (3:ℝ)..s, stopped t) = ∫ _ in (3:ℝ)..s, (0:ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_ge hs] at ht
      exact stopped_left ht.2
    simp [he,H_eq_one ha hs]
  · have hs' := le_of_not_ge hs
    have hd := H_sub (x := 3) (by norm_num) hs'
    have hi : (∫ t in (3:ℝ)..s, lower (t-1)) = ∫ t in (3:ℝ)..s, stopped t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hs'] at ht
      rw [lower_shift ht.1 (ht.2.trans hb),stopped_right ht.1]
    rw [hi,H_eq_one (by norm_num : (1:ℝ)<3) le_rfl] at hd
    linarith

theorem hasDerivAt_upper_three : HasDerivAt upper (-(3:ℝ)^(-2:ℤ)) 3 := by
  have hI := intervalIntegral.integral_hasDerivAt_right
    (stopped_continuous.intervalIntegrable (3:ℝ) 3)
    stopped_continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
    (stopped_continuous.continuousAt (x := (3:ℝ)))
  have hH : HasDerivAt H 0 3 := by
    rw [← stopped_left (le_refl (3:ℝ))]
    apply (hI.const_add 1).congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds (by norm_num : (1:ℝ)<3) (by norm_num : (3:ℝ)<5)] with u hu
    exact H_eq_primitive hu.1 hu.2.le
  have hU := hH.fun_div (hasDerivAt_id (3:ℝ)) (by norm_num)
  have hd : HasDerivAt (fun s : ℝ => H s/s) (-(3:ℝ)^(-2:ℤ)) 3 := by
    convert hU using 1 <;> norm_num [H_eq_one (by norm_num : (1:ℝ)<3) le_rfl]
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds (by norm_num : (0:ℝ)<3)] with u hu
  change upper u = (u*upper u)/u
  field_simp [hu.ne']

theorem numerator_initial {s : ℝ} (ha : 1 < s) (hb : s ≤ 3) : numerator s = 1 := by
  rcases lt_or_eq_of_le hb with h | rfl
  · rw [numerator,(hasDerivAt_upper_base ha h).deriv]
    field_simp [ne_of_gt (by linarith : 0 < s)]
  · rw [numerator,hasDerivAt_upper_three.deriv]
    norm_num

/-- The factor multiplying the logarithm is s/(s-1). -/
theorem numerator_eq {s : ℝ} (ha : 3 ≤ s) (hb : s ≤ 5) :
    numerator s = H s - s*q (s-1) := by
  rcases lt_or_eq_of_le ha with hs | he
  · rw [numerator,(hasDerivAt_upper_tail hs).deriv,upperSlope,lower_shift hs.le hb,H]
    field_simp [ne_of_gt (by linarith : 0 < s)] <;> ring
  · subst s
    norm_num [numerator_initial (by norm_num : (1:ℝ)<3) le_rfl,H_eq_one (by norm_num : (1:ℝ)<3) le_rfl,q]

theorem H_interval_bounds {u v : ℝ} (hu : 3 ≤ u) (huv : u ≤ v) (hv : v ≤ 5) :
    (v-u)*q (u-1) ≤ H v-H u ∧ H v-H u ≤ (v-u)*q (v-1) := by
  have hit : IntervalIntegrable (fun t => lower (t-1)) volume u v :=
    (shifted_factors_integrable hu huv).2
  rw [H_sub hu huv]
  constructor
  · have hh := intervalIntegral.integral_mono_on huv
      (continuous_const.intervalIntegrable u v) hit (f := fun _ : ℝ => q (u-1)) (fun t ht => by
        rw [lower_shift (hu.trans ht.1) (ht.2.trans hv)]
        exact q_monotone ⟨by linarith,by linarith⟩ ⟨by linarith [ht.1],by linarith [ht.2]⟩
          (by linarith [ht.1]))
    simpa only [intervalIntegral.integral_const,smul_eq_mul] using hh
  · have hh := intervalIntegral.integral_mono_on huv hit
      (continuous_const.intervalIntegrable u v) (g := fun _ : ℝ => q (v-1)) (fun t ht => by
        rw [lower_shift (hu.trans ht.1) (ht.2.trans hv)]
        exact q_monotone ⟨by linarith [ht.1],by linarith [ht.2]⟩ ⟨by linarith,by linarith⟩
          (by linarith [ht.2]))
    simpa only [intervalIntegral.integral_const,smul_eq_mul] using hh

theorem numerator_antitone_tail : AntitoneOn numerator (Icc 3 5) := by
  intro u hu v hv huv
  have hh := (H_interval_bounds hu.1 huv hv.2).2
  have hq := q_monotone (show u-1 ∈ Icc (2:ℝ) 4 from ⟨by linarith [hu.1],by linarith [hu.2]⟩)
    (show v-1 ∈ Icc (2:ℝ) 4 from ⟨by linarith [hv.1],by linarith [hv.2]⟩) (by linarith)
  have h := mul_le_mul_of_nonneg_left hq (show 0 ≤ u by linarith [hu.1])
  rw [numerator_eq hv.1 hv.2,numerator_eq hu.1 hu.2]
  linarith only [hh,h]

theorem numerator_antitone : AntitoneOn numerator (Ioc 1 5) := by
  intro u hu v hv huv
  by_cases h : v ≤ 3
  · rw [numerator_initial hu.1 (huv.trans h),numerator_initial hv.1 h]
  · have hv3 : 3 ≤ v := le_of_not_ge h
    by_cases hu3 : 3 ≤ u
    · exact numerator_antitone_tail ⟨hu3,hu.2⟩ ⟨hv3,hv.2⟩ huv
    · rw [numerator_initial hu.1 (le_of_not_ge hu3)]
      simpa only [numerator_initial (by norm_num : (1:ℝ)<3) le_rfl] using
        numerator_antitone_tail (show (3:ℝ) ∈ Icc 3 5 by norm_num) ⟨hv3,hv.2⟩ hv3

end
end ImbalancedChen.P1OriginalFourthDerivativeNumerator
