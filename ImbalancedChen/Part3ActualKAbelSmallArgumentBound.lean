import ImbalancedChen.Part3ComplexOrderKEntire
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-26.

A genuine uniform small-argument estimate for the ACTUAL Abel-normalized
K kernel. For0<q<=1 and0<=Re nu<=1, arbitrary imaginary part,
  |(q/2)^nu K_nu(q)| <= 1-log(q/2).
The proof splits the literal cosh-Laplace coordinate at L=-log(q/2).
The head is bounded by1 and the tail by exp(L-u), using2w<=exp(w).
The majorant and its exact integral L+1 are proved. There is no imported
small-q asymptotic, unproved uniformity, or zero-argument substitution.
This is the missing logarithmic majorant for opposite-sign radial Abel
transport; that transport itself is not asserted by this module.
-/

namespace ImbalancedChen.Part3.ActualKAbelSmallArgumentBound20261026b

noncomputable section
open Set MeasureTheory Filter
open ImbalancedChen.Part3.ComplexOrderKBridgeSourceOnly

def logCut (q : ℝ) : ℝ := -Real.log (q / 2)

theorem logCut_nonneg {q : ℝ} (hq : 0 < q) (hqu : q ≤ 1) : 0 ≤ logCut q := by
  have hh : 0 ≤ q / 2 := (half_pos hq).le
  have hhu : q / 2 ≤ 1 := by linarith
  exact neg_nonneg.mpr (Real.log_nonpos hh hhu)

def logarithmicEnvelope (L u : ℝ) : ℝ :=
  (Ioc (0 : ℝ) L).indicator (fun _ => (1 : ℝ)) u +
    (Ioi L).indicator (fun u => Real.exp (L - u)) u

theorem logarithmicEnvelope_integrable (L : ℝ) : Integrable (logarithmicEnvelope L) := by
  have hhead : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc 0 L) :=
    (continuous_const.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have htail : IntegrableOn (fun u : ℝ => Real.exp (L - u)) (Ioi L) := by
    apply ((integrableOn_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) L).const_mul (Real.exp L)).congr_fun
      _ measurableSet_Ioi
    intro u hu
    rw [← Real.exp_add]
    congr 1
    ring
  exact (hhead.integrable_indicator measurableSet_Ioc).add
    (htail.integrable_indicator measurableSet_Ioi)

theorem logarithmicEnvelope_integral {L : ℝ} (hL : 0 ≤ L) :
    (∫ u : ℝ, logarithmicEnvelope L u) = L + 1 := by
  have hhead : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc 0 L) :=
    (continuous_const.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have htail : IntegrableOn (fun u : ℝ => Real.exp (L - u)) (Ioi L) := by
    apply ((integrableOn_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) L).const_mul (Real.exp L)).congr_fun
      _ measurableSet_Ioi
    intro u hu
    rw [← Real.exp_add]
    congr 1
    ring
  have hh : (∫ u in Ioc (0 : ℝ) L, (1 : ℝ)) = L := by
    simp only [setIntegral_const, Real.volume_real_Ioc_of_le hL, sub_zero, smul_eq_mul, mul_one]
  have ht : (∫ u in Ioi L, Real.exp (L - u)) = 1 := by
    have he : (fun u : ℝ => Real.exp (L - u)) = fun u => Real.exp L * Real.exp (-u) := by
      funext u
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he, integral_const_mul]
    have hi : (∫ u in Ioi L, Real.exp (-u)) = Real.exp (-L) := by
      simpa using integral_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) L
    rw [hi, ← Real.exp_add, add_neg_cancel, Real.exp_zero]
  unfold logarithmicEnvelope
  rw [integral_add (hhead.integrable_indicator measurableSet_Ioc)
    (htail.integrable_indicator measurableSet_Ioi),
    integral_indicator measurableSet_Ioc, integral_indicator measurableSet_Ioi, hh, ht]

theorem logarithmicEnvelope_zero_nonpositive {L : ℝ} (hL : 0 ≤ L)
    {u : ℝ} (hu : u ≤ 0) : logarithmicEnvelope L u = 0 := by
  have hh : u ∉ Ioc (0 : ℝ) L := fun h => (not_lt_of_ge hu) h.1
  have ht : u ∉ Ioi L := fun h => (not_lt_of_ge (hu.trans hL)) h
  simp [logarithmicEnvelope, hh, ht]

/-- A pointwise estimate on the literal actual integrand, uniform in
the imaginary order and all real parts between0 and1. -/
theorem normalized_integrand_norm_le {ν : ℂ} (hν0 : 0 ≤ ν.re) (hν1 : ν.re ≤ 1)
    {q u : ℝ} (hq : 0 < q) (hqu : q ≤ 1) (hu : 0 < u) :
    ‖((q / 2 : ℝ) : ℂ) ^ ν * complexOrderIntegrand ν q u‖ ≤
      logarithmicEnvelope (logCut q) u := by
  have hc := half_pos hq
  have hcosh : ‖Complex.cosh (ν * (u : ℂ))‖ ≤ Real.exp (ν.re * u) := by
    have hnorm : ‖Complex.cosh (ν * (u : ℂ))‖ ≤ Real.cosh (ν.re * u) := by
      simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero] using norm_complex_cosh_le_real_cosh (ν * (u : ℂ))
    have hle : Real.exp (-(ν.re * u)) ≤ Real.exp (ν.re * u) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg hν0 hu.le]
    apply hnorm.trans
    rw [Real.cosh_eq]
    linarith
  have hexp : ‖((q / 2 : ℝ) : ℂ) ^ ν * complexOrderIntegrand ν q u‖ ≤
      Real.exp (-q * Real.cosh u + ν.re * (u - logCut q)) := by
    calc
      _ = (q / 2) ^ ν.re * Real.exp (-q * Real.cosh u) *
          ‖Complex.cosh (ν * (u : ℂ))‖ := by
        simp only [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hc, complexOrderIntegrand,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_assoc]
      _ ≤ (q / 2) ^ ν.re * Real.exp (-q * Real.cosh u) * Real.exp (ν.re * u) :=
        mul_le_mul_of_nonneg_left hcosh
          (mul_nonneg (Real.rpow_nonneg hc.le _) (Real.exp_pos _).le)
      _ = _ := by
        rw [Real.rpow_def_of_pos hc, ← Real.exp_add, ← Real.exp_add]
        congr 1
        unfold logCut
        ring
  by_cases hhead : u ≤ logCut q
  · have hnonpos : -q * Real.cosh u + ν.re * (u - logCut q) ≤ 0 := by
      have hh := mul_nonpos_of_nonneg_of_nonpos hν0 (sub_nonpos.mpr hhead)
      nlinarith [mul_pos hq (Real.cosh_pos u)]
    have hhmem : u ∈ Ioc (0 : ℝ) (logCut q) := ⟨hu, hhead⟩
    have htmem : u ∉ Ioi (logCut q) := not_lt_of_ge hhead
    simpa only [logarithmicEnvelope, indicator_of_mem hhmem, indicator_of_not_mem htmem, add_zero,
      Real.exp_zero] using hexp.trans (Real.exp_le_exp.mpr hnonpos)
  · have hw : 0 < u - logCut q := sub_pos.mpr (lt_of_not_ge hhead)
    have hqcosh : Real.exp (u - logCut q) ≤ q * Real.cosh u := by
      have he : Real.exp (u - logCut q) = Real.exp u * (q / 2) := by
        unfold logCut
        rw [sub_neg_eq_add, Real.exp_add, Real.exp_log hc]
      rw [he, Real.cosh_eq]
      nlinarith [mul_nonneg hq.le (Real.exp_pos (-u)).le]
    have htw : 2 * (u - logCut q) ≤ Real.exp (u - logCut q) := Real.two_mul_le_exp
    have hmul : ν.re * (u - logCut q) ≤ u - logCut q := by
      nlinarith [mul_le_mul_of_nonneg_right hν1 hw.le]
    have he : -q * Real.cosh u + ν.re * (u - logCut q) ≤ logCut q - u := by
      linarith
    have hhmem : u ∉ Ioc (0 : ℝ) (logCut q) := fun h => hhead h.2
    have htmem : u ∈ Ioi (logCut q) := lt_of_not_ge hhead
    simpa only [logarithmicEnvelope, indicator_of_not_mem hhmem, indicator_of_mem htmem, zero_add]
      using hexp.trans (Real.exp_le_exp.mpr he)

/-- The actual Abel-normalized K kernel has a logarithmic small-q
majorant uniform up to imaginary order, including nu=0. -/
theorem actual_normalized_K_small_argument_bound {ν : ℂ}
    (hν0 : 0 ≤ ν.re) (hν1 : ν.re ≤ 1) {q : ℝ} (hq : 0 < q) (hqu : q ≤ 1) :
    ‖((q / 2 : ℝ) : ℂ) ^ ν * complexOrderK ν q‖ ≤ 1 - Real.log (q / 2) := by
  have hL := logCut_nonneg hq hqu
  have heq : ((q / 2 : ℝ) : ℂ) ^ ν * complexOrderK ν q =
      ∫ u in Ioi (0 : ℝ), ((q / 2 : ℝ) : ℂ) ^ ν * complexOrderIntegrand ν q u := by
    rw [integral_const_mul]
    rfl
  rw [heq]
  calc
    _ ≤ ∫ u in Ioi (0 : ℝ), logarithmicEnvelope (logCut q) u :=
      norm_integral_le_of_norm_le (logarithmicEnvelope_integrable _).integrableOn (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        exact normalized_integrand_norm_le hν0 hν1 hq hqu hu)
    _ = ∫ u : ℝ, logarithmicEnvelope (logCut q) u :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun u hu =>
        logarithmicEnvelope_zero_nonpositive hL (le_of_not_gt hu))
    _ = _ := by rw [logarithmicEnvelope_integral hL]; unfold logCut; ring

end
end ImbalancedChen.Part3.ActualKAbelSmallArgumentBound20261026b
