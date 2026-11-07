import ImbalancedChen.Part3ActualJUniformCompactRealOrderBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.

Native qFirst of actual ordinary real-order J is O(q^(-1/2)). The proof
uses the already derived radial energy, including its derivative term;
no oscillatory asymptotic, critical quotient, or extra energy bound is
assumed. The weighted derivative tail is genuinely L1 for Re(s)<3/2,
and its integration-by-parts boundary tends to zero.
-/

namespace ImbalancedChen.Part3.ActualJFirstLargeQBound20261026b

noncomputable section
open Complex Set MeasureTheory Filter
open scoped Topology
open ActualGeneralJBesselSourceOnly ActualRealOrderJRadialJet20261026b
open ActualRealOrderJLargeQ20261026b ActualJUniformCompactRealOrderBounds20261026b

theorem realRadialJFirst_norm_le_initial {nu : ℝ} (hnu : |nu| ≤ 1 / 2)
    {q : ℝ} (hq : 1 ≤ q) : ‖realRadialJFirst nu q‖ ≤ realLargeQAmplitude nu := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hE := realRadialEnergy_antitoneOn hnu (show (1 : ℝ) ∈ Ioi 0 by norm_num) hq0 hq
  have hV : 0 ≤ realRadialPotential nu q := (by norm_num : (0 : ℝ) ≤ 1).trans
    (realRadialPotential_ge_one hnu q)
  have hs : ‖realRadialJFirst nu q‖ ^ 2 ≤ realRadialEnergy nu q := by
    unfold realRadialEnergy
    exact le_add_of_nonneg_right (mul_nonneg hV (sq_nonneg _))
  exact Real.le_sqrt_of_sq_le (hs.trans hE)

theorem generalJFirst_real_large_q_bound {nu : ℝ} (hnu : |nu| ≤ 1 / 2)
    {q : ℝ} (hq : 1 ≤ q) :
    ‖generalJFirst (nu : ℂ) q‖ ≤ (2 * realLargeQAmplitude nu) / Real.sqrt q := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hS : 0 < Real.sqrt q := Real.sqrt_pos.2 hq0
  have hA : 0 ≤ realLargeQAmplitude nu := Real.sqrt_nonneg _
  have hsq : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt hq0.le
  have hid : (Real.sqrt q : ℂ) * generalJFirst (nu : ℂ) q =
      realRadialJFirst nu q - ((1 / (2 * Real.sqrt q) : ℝ) : ℂ) * generalJ (nu : ℂ) q := by
    unfold realRadialJFirst
    ring
  have hn := norm_sub_le (realRadialJFirst nu q)
    (((1 / (2 * Real.sqrt q) : ℝ) : ℂ) * generalJ (nu : ℂ) q)
  rw [← hid, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hS,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.sqrt q))] at hn
  have hc : (1 / (2 * Real.sqrt q)) * ‖generalJ (nu : ℂ) q‖ ≤ realLargeQAmplitude nu := by
    calc
      _ ≤ (1 / (2 * Real.sqrt q)) * (realLargeQAmplitude nu / Real.sqrt q) :=
        mul_le_mul_of_nonneg_left (generalJ_real_large_q_bound hnu hq) (by positivity)
      _ = realLargeQAmplitude nu / (2 * q) := by field_simp [hS.ne']; nlinarith [hsq]
      _ ≤ realLargeQAmplitude nu := by
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * q)).2
        nlinarith
  apply (le_div_iff₀ hS).2
  have hF := realRadialJFirst_norm_le_initial hnu hq
  nlinarith

theorem exists_generalJFirst_uniform_real_large_q_bound {r : ℝ} (hr : r < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ nu ∈ Icc (-r) r, ∀ q : ℝ, 1 ≤ q →
      ‖generalJFirst (nu : ℂ) q‖ ≤ C / Real.sqrt q := by
  obtain ⟨A, hA⟩ := (isCompact_Icc : IsCompact (Icc (-r) r))
    .exists_bound_of_continuousOn (realLargeQAmplitude_continuousOn hr)
  refine ⟨2 * (|A| + 1), by positivity, ?_⟩
  intro nu hnu q hq
  have habs : |nu| ≤ 1 / 2 := (abs_le.mpr hnu).trans hr.le
  have hb : realLargeQAmplitude nu ≤ |A| + 1 := by
    have h := hA nu hnu
    rw [Real.norm_eq_abs] at h
    linarith [le_abs_self (realLargeQAmplitude nu), le_abs_self A]
  exact (generalJFirst_real_large_q_bound habs hq).trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb (by norm_num)) (Real.sqrt_nonneg q))

def derivativeMellinRemainder (s : ℂ) (nu q : ℝ) : ℂ :=
  (q : ℂ) ^ (s - 2) * generalJFirst (nu : ℂ) q

theorem integrableOn_derivativeMellinRemainder {nu : ℝ} (hnu : |nu| ≤ 1 / 2)
    {s : ℂ} (hs : s.re < 3 / 2) :
    IntegrableOn (derivativeMellinRemainder s nu) (Ioi 1) := by
  have hc : ContinuousOn (derivativeMellinRemainder s nu) (Ioi 1) := by
    intro q hq
    have hq0 : 0 < q := lt_trans (by norm_num) hq
    exact ((Complex.continuousAt_ofReal_cpow_const q (s - 2) (Or.inr hq0.ne')).mul
      (generalJFirst_hasDerivAt (real_order_lower hnu) hq0).continuousAt).continuousWithinAt
  have hi : IntegrableOn (fun q : ℝ => (2 * realLargeQAmplitude nu) * q ^ (s.re - 5 / 2)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : s.re - 5 / 2 < -1)
      (by norm_num : (0 : ℝ) < 1)).const_mul _
  apply hi.mono' (hc.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
  have hq0 : 0 < q := lt_trans (by norm_num) hq
  rw [derivativeMellinRemainder, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hq0]
  simp only [Complex.sub_re, Complex.ofNat_re]
  calc
    q ^ (s.re - 2) * ‖generalJFirst (nu : ℂ) q‖ ≤
        q ^ (s.re - 2) * ((2 * realLargeQAmplitude nu) / Real.sqrt q) :=
      mul_le_mul_of_nonneg_left (generalJFirst_real_large_q_bound hnu hq.le) (Real.rpow_nonneg hq0.le _)
    _ = (2 * realLargeQAmplitude nu) * (q ^ (s.re - 2) / q ^ (1 / 2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow]; ring
    _ = (2 * realLargeQAmplitude nu) * q ^ (s.re - 5 / 2) := by
      rw [← Real.rpow_sub hq0]
      congr 1
      congr 1
      ring

theorem derivativeMellinBoundary_tendsto_zero {nu : ℝ} (hnu : |nu| ≤ 1 / 2)
    {s : ℂ} (hs : s.re < 3 / 2) :
    Tendsto (fun q : ℝ => (q : ℂ) ^ (s - 1) * generalJFirst (nu : ℂ) q) atTop (𝓝 0) := by
  have hp : Tendsto (fun q : ℝ => q ^ (s.re - 3 / 2)) atTop (𝓝 0) := by
    have he : s.re - 3 / 2 = -(3 / 2 - s.re) := by ring
    rw [he]
    exact Real.tendsto_rpow_neg_atTop (by linarith : 0 < 3 / 2 - s.re)
  have hm : Tendsto (fun q : ℝ => (2 * realLargeQAmplitude nu) * q ^ (s.re - 3 / 2)) atTop (𝓝 0) :=
    by simpa using hp.const_mul (2 * realLargeQAmplitude nu)
  apply squeeze_zero_norm' ?_ hm
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with q hq
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hq0]
  simp only [Complex.sub_re, Complex.one_re]
  calc
    _ ≤ q ^ (s.re - 1) * ((2 * realLargeQAmplitude nu) / Real.sqrt q) :=
      mul_le_mul_of_nonneg_left (generalJFirst_real_large_q_bound hnu hq) (Real.rpow_nonneg hq0.le _)
    _ = (2 * realLargeQAmplitude nu) * (q ^ (s.re - 1) / q ^ (1 / 2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow]; ring
    _ = (2 * realLargeQAmplitude nu) * q ^ (s.re - 3 / 2) := by
      rw [← Real.rpow_sub hq0]
      congr 1
      congr 1
      ring

end
end ImbalancedChen.Part3.ActualJFirstLargeQBound20261026b
