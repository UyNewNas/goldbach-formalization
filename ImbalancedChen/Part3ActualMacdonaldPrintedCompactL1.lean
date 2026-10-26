import ImbalancedChen.Part3ActualMacdonaldPositiveProductSheet
import ImbalancedChen.Part3ActualSchwingerPowerEnvelope
import ImbalancedChen.Part3ActualComplexMacdonaldQuarterIdentity
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-26.

Actual inherited-sheet Macdonald endpoint L1 on the printed slit/sum
quarter-sector domain, for each fixed |Re(nu)|<r<1/2, including zero.
On each compact parameter family A=Re((z+w)^2) has a positive floor
delta. If B=Re(z*w)<=delta/8, the honest cover growth combines with the
outer exponential through A-2B-2|B|>=delta/2. A compact half-log bound
then leaves the proved real-power Schwinger envelope. If B>=delta/8,
the proved product-sheet geometry binds the actual Laplace fiber and
the combined A/B joint majorant applies. Both bounds share one common
almost-everywhere set and one actual integrable envelope. Parameter
holomorphy, continuation topology, and the full printed E18 identity
are NOT conclusions of this module.
-/

namespace ImbalancedChen.Part3.ActualMacdonaldPrintedCompactL120261026b

noncomputable section
open Set MeasureTheory Filter
open ActualKUnequalPositiveShear20261026b (positiveMeasure)
open ActualComplexArgumentKLaplace20261026b
open ActualLogCoverKModel20261026b ActualLogCoverIPoissonGrowth20261026b
open ActualMacdonaldProductDetermination20261026b
open ActualComplexMacdonaldQuarterL120261026b
open ActualComplexMacdonaldQuarterIdentity20261026b
open ActualComplexMacdonaldCombinedL120261026b
open ActualMacdonaldPositiveProductSheet20261026b ActualSchwingerPowerEnvelope20261026b

def inheritedMacdonaldKernel (nu z w : ℂ) (t : ℝ) : ℂ :=
  ((t⁻¹ : ℝ) : ℂ) *
    Complex.exp (((-t / 2 : ℝ) : ℂ) - (z ^ 2 + w ^ 2) * ((1 / (2 * t) : ℝ) : ℂ)) *
      determinedProductK nu z w t

def macdonaldPositiveFiberMajorant (nu : ℂ) (c t : ℝ) : ℝ :=
  ∫ v in Ioi (0 : ℝ), positiveMacdonaldMajorant nu c v t

theorem macdonaldPositiveFiberMajorant_integrable (nu : ℂ) {c : ℝ} (hc : 0 < c) :
    Integrable (macdonaldPositiveFiberMajorant nu c) positiveMeasure :=
  (positiveMacdonaldMajorant_integrable nu hc).integral_prod_right

theorem macdonaldPositiveFiberMajorant_nonneg (nu : ℂ) (c : ℝ) {t : ℝ} (ht : 0 < t) :
    0 ≤ macdonaldPositiveFiberMajorant nu c t := by
  apply integral_nonneg
  intro v
  unfold positiveMacdonaldMajorant
  positivity

theorem inheritedMacdonaldKernel_norm (nu z w : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖inheritedMacdonaldKernel nu z w t‖ = t⁻¹ *
      Real.exp (-t / 2 - ((z ^ 2).re + (w ^ 2).re) * (1 / (2 * t))) *
        ‖determinedProductK nu z w t‖ := by
  simp only [inheritedMacdonaldKernel, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr ht), Complex.norm_exp, Complex.sub_re, Complex.add_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

theorem inheritedMacdonaldKernel_eq_display (nu z w : ℂ) (t : ℝ) :
    inheritedMacdonaldKernel nu z w t =
      Complex.exp (-(t : ℂ) / 2 - (z ^ 2 + w ^ 2) / (2 * (t : ℂ))) *
        determinedProductK nu z w t / (t : ℂ) := by
  have he : (((-t / 2 : ℝ) : ℂ) - (z ^ 2 + w ^ 2) * ((1 / (2 * t) : ℝ) : ℂ)) =
      -(t : ℂ) / 2 - (z ^ 2 + w ^ 2) / (2 * (t : ℂ)) := by
    push_cast
    simp only [div_eq_mul_inv, one_mul]
  unfold inheritedMacdonaldKernel
  rw [he]
  push_cast
  simp only [div_eq_mul_inv]
  ring

theorem coverPhysicalArgument_productHalfLog {z w : ℂ} {t : ℝ}
    (hz : z ≠ 0) (hw : w ≠ 0) (ht : 0 < t) :
    coverPhysicalArgument (productHalfLog z w t) = physicalProductArgument z w t :=
  physical_product_of_half_log hz hw ht

theorem physicalProductArgument_re (z w : ℂ) {t : ℝ} (ht : 0 < t) :
    (physicalProductArgument z w t).re = (z * w).re / t := by
  have he : physicalProductArgument z w t = z * w * ((t⁻¹ : ℝ) : ℂ) := by
    simp only [physicalProductArgument, div_eq_mul_inv, Complex.ofReal_inv]
  rw [he]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    div_eq_mul_inv]

theorem inheritedMacdonaldKernel_eq_laplace {nu z w : ℂ}
    (hL : -(1 / 2 : ℝ) < nu.re) (hU : nu.re < 1 / 2)
    (hz : z ∈ Complex.slitPlane) (hw : w ∈ Complex.slitPlane)
    (hs : 0 < (z + w).re) (hB : 0 < (z * w).re) {t : ℝ} (ht : 0 < t) :
    inheritedMacdonaldKernel nu z w t = complexMacdonaldKernel nu z w t := by
  unfold inheritedMacdonaldKernel complexMacdonaldKernel
  rw [determinedProductK_eq_actual_positive_product hL hU hz hw hs hB ht]
  simp only [physicalProductArgument, div_eq_mul_inv, Complex.ofReal_inv]

theorem small_product_exponent_bound {z w : ℂ} {delta t : ℝ}
    (hd : 0 < delta) (hA : delta ≤ ((z + w) ^ 2).re)
    (hB : (z * w).re ≤ delta / 8) (ht : 0 < t) :
    -t / 2 - ((z ^ 2).re + (w ^ 2).re) * (1 / (2 * t)) + |(z * w).re| / t ≤
      -t / 2 - (delta / 4) / t := by
  have hnum : delta / 2 ≤ ((z + w) ^ 2).re - 2 * (z * w).re - 2 * |(z * w).re| := by
    by_cases hb : (z * w).re ≤ 0
    · rw [abs_of_nonpos hb]
      linarith
    · rw [abs_of_pos (lt_of_not_ge hb)]
      linarith
  have hdiv := mul_le_mul_of_nonneg_right hnum (by positivity : 0 ≤ 1 / (2 * t))
  have he : ((z ^ 2).re + (w ^ 2).re) * (1 / (2 * t)) - |(z * w).re| / t =
      (((z + w) ^ 2).re - 2 * (z * w).re - 2 * |(z * w).re|) * (1 / (2 * t)) := by
    rw [combined_square_re]
    field_simp [ht.ne'] <;> ring
  have hdv : (delta / 2) * (1 / (2 * t)) = (delta / 4) / t := by
    field_simp [ht.ne'] <;> ring
  rw [← he, hdv] at hdiv
  linarith

/-- Compactness bounds only the fixed part of the actual inherited
half-log. Its integration dependence remains the literal -log(t). -/
theorem compact_productHalfLog_real_bound {S : Set (ℂ × ℂ)} (hS : IsCompact S)
    (hprinted : S ⊆ printedMacdonaldDomain) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p ∈ S, ∀ t : ℝ, 0 < t →
      |(productHalfLog p.1 p.2 t).re| ≤ M + |Real.log t| := by
  let F : ℂ × ℂ → ℂ := fun p => Complex.log p.1 + Complex.log p.2
  have hF : ContinuousOn F S := by
    intro p hp
    have hz := (Complex.analyticAt_clog (hprinted hp).1).continuousAt.comp continuous_fst.continuousAt
    have hw := (Complex.analyticAt_clog (hprinted hp).2.1).continuousAt.comp continuous_snd.continuousAt
    exact (hz.add hw).continuousWithinAt
  obtain ⟨M₀, hM₀⟩ := hS.exists_bound_of_continuousOn hF
  let M : ℝ := max M₀ 0 + |Real.log 2| + 1
  refine ⟨M, by dsimp [M]; positivity, ?_⟩
  intro p hp t ht
  have hFbound : |(F p).re| ≤ max M₀ 0 :=
    (Complex.abs_re_le_norm _).trans ((hM₀ p hp).trans (le_max_left _ _))
  have he : (productHalfLog p.1 p.2 t).re = (F p).re - Real.log t - Real.log 2 := by
    rw [productHalfLog_eq_sum_logs p.1 p.2 ht]
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, F]
  rw [he]
  calc
    _ ≤ |(F p).re - Real.log t| + |Real.log 2| := abs_sub _ _
    _ ≤ (|(F p).re| + |Real.log t|) + |Real.log 2| :=
      add_le_add_right (abs_sub _ _) _
    _ ≤ _ := by dsimp [M]; linarith

theorem inheritedMacdonaldKernel_measurable {nu : ℂ} (hL : -1 < nu.re) (hU : nu.re < 1)
    (z w : ℂ) : Measurable (inheritedMacdonaldKernel nu z w) := by
  have hc : Continuous (logCoverK nu) := continuous_iff_continuousAt.mpr fun L =>
    ((logCoverK_analyticOnNhd hL hU) L (mem_univ _)).continuousAt
  have hlog : Measurable (fun t : ℝ => productHalfLog z w t) := by
    unfold productHalfLog
    fun_prop
  have hK : Measurable (fun t : ℝ => determinedProductK nu z w t) := hc.measurable.comp hlog
  have hfactor : Measurable (fun t : ℝ => ((t⁻¹ : ℝ) : ℂ) *
      Complex.exp (((-t / 2 : ℝ) : ℂ) - (z ^ 2 + w ^ 2) * ((1 / (2 * t) : ℝ) : ℂ))) := by
    fun_prop
  exact hfactor.mul hK

/-- The actual common compact envelope has one common almost-everywhere
set for ALL parameters in the compact family. This is stronger than
parameter-dependent exceptional-set bounds. -/
theorem compact_inheritedMacdonaldKernel_majorant {nu : ℂ} {r : ℝ}
    (horder : |nu.re| < r) (hr : 0 < r) (hrhalf : r < 1 / 2)
    {S : Set (ℂ × ℂ)} (hS : IsCompact S) (hprinted : S ⊆ printedMacdonaldDomain) :
    ∃ g : ℝ → ℝ, Integrable g positiveMeasure ∧
      ∀ᵐ t : ℝ ∂positiveMeasure, ∀ p ∈ S, ‖inheritedMacdonaldKernel nu p.1 p.2 t‖ ≤ g t := by
  have hAc : Continuous (fun p : ℂ × ℂ => ((p.1 + p.2) ^ 2).re) := by fun_prop
  obtain ⟨delta, hd, hA⟩ := hS.exists_forall_le' hAc.continuousOn
    (fun p hp => strictQuarterSector_square_re_pos (hprinted hp).2.2)
  obtain ⟨M, hM, hlog⟩ := compact_productHalfLog_real_bound hS hprinted
  obtain ⟨C, hC, hK⟩ := exists_logCoverK_half_log_growth horder hr hrhalf
    (by positivity : 0 ≤ 3 * Real.pi / 2)
  let g : ℝ → ℝ := fun t => C * Real.exp (r * M) * schwingerPowerEnvelope r (delta / 4) t +
    macdonaldPositiveFiberMajorant nu (delta / 32) t
  have hg : Integrable g positiveMeasure :=
    ((schwingerPowerEnvelope_integrable r (by positivity : 0 < delta / 4)).const_mul _).add
      (macdonaldPositiveFiberMajorant_integrable nu (by positivity : 0 < delta / 32))
  refine ⟨g, hg, ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioi,
    (positiveMacdonaldMajorant_integrable nu (by positivity : 0 < delta / 32)).prod_left_ae]
    with t ht hfiber
  intro p hp
  rcases hprinted hp with ⟨hz, hw, hs⟩
  have hzn := (Complex.mem_slitPlane_iff_arg.mp hz).2
  have hwn := (Complex.mem_slitPlane_iff_arg.mp hw).2
  have hs0 := strictQuarterSector_re_pos hs
  have hpow : 0 ≤ t ^ r + t ^ (-r) := add_nonneg
    (Real.rpow_nonneg ht.le _) (Real.rpow_nonneg ht.le _)
  have hpoly : 0 ≤ schwingerPowerEnvelope r (delta / 4) t := by
    unfold schwingerPowerEnvelope
    positivity
  have hL : -(1 / 2 : ℝ) < nu.re := by have h := (abs_lt.mp horder).1; linarith
  have hU : nu.re < 1 / 2 := by have h := (abs_lt.mp horder).2; linarith
  by_cases hB : (p.1 * p.2).re ≤ delta / 8
  · have hphase : |(productHalfLog p.1 p.2 t).im| ≤ 3 * Real.pi / 2 := by
      rw [productHalfLog_im]
      exact (inherited_phase_lt_three_half_pi hz hw hs0).le
    have hKgrowth := hK (productHalfLog p.1 p.2 t) hphase
    rw [coverPhysicalArgument_productHalfLog hzn hwn ht, physicalProductArgument_re _ _ ht,
      abs_div, abs_of_pos ht] at hKgrowth
    have hlogExp : Real.exp (r * |(productHalfLog p.1 p.2 t).re|) ≤
        Real.exp (r * M) * (t ^ r + t ^ (-r)) := by
      calc
        _ ≤ Real.exp (r * (M + |Real.log t|)) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hlog p hp t ht) hr.le)
        _ = Real.exp (r * M) * Real.exp (r * |Real.log t|) := by
          rw [← Real.exp_add]
          congr 1
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (exp_abs_log_le_powers r ht) (Real.exp_pos _).le
    have hKbound : ‖determinedProductK nu p.1 p.2 t‖ ≤
        C * (Real.exp (r * M) * (t ^ r + t ^ (-r))) * Real.exp (|(p.1 * p.2).re| / t) :=
      hKgrowth.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlogExp hC.le) (Real.exp_pos _).le)
    have hE : Real.exp (-t / 2 - ((p.1 ^ 2).re + (p.2 ^ 2).re) * (1 / (2 * t))) *
        Real.exp (|(p.1 * p.2).re| / t) ≤ Real.exp (-t / 2 - (delta / 4) / t) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (small_product_exponent_bound hd (hA p hp) hB ht)
    have hbound : ‖inheritedMacdonaldKernel nu p.1 p.2 t‖ ≤
        C * Real.exp (r * M) * schwingerPowerEnvelope r (delta / 4) t := by
      rw [inheritedMacdonaldKernel_norm _ _ _ ht]
      calc
        _ ≤ t⁻¹ * Real.exp (-t / 2 - ((p.1 ^ 2).re + (p.2 ^ 2).re) * (1 / (2 * t))) *
            (C * (Real.exp (r * M) * (t ^ r + t ^ (-r))) * Real.exp (|(p.1 * p.2).re| / t)) :=
          mul_le_mul_of_nonneg_left hKbound (by positivity)
        _ = (C * Real.exp (r * M) * ((t ^ r + t ^ (-r)) / t)) *
            (Real.exp (-t / 2 - ((p.1 ^ 2).re + (p.2 ^ 2).re) * (1 / (2 * t))) *
              Real.exp (|(p.1 * p.2).re| / t)) := by simp only [div_eq_mul_inv]; ring
        _ ≤ (C * Real.exp (r * M) * ((t ^ r + t ^ (-r)) / t)) *
            Real.exp (-t / 2 - (delta / 4) / t) :=
          mul_le_mul_of_nonneg_left hE (by positivity)
        _ = _ := by unfold schwingerPowerEnvelope; ring
    exact hbound.trans (le_add_of_nonneg_right (macdonaldPositiveFiberMajorant_nonneg nu _ ht))
  · have hBfloor : delta / 8 ≤ (p.1 * p.2).re := (lt_of_not_ge hB).le
    have hBpos : 0 < (p.1 * p.2).re := lt_of_lt_of_le (by positivity : 0 < delta / 8) hBfloor
    have hAfloor : delta / 8 ≤ ((p.1 + p.2) ^ 2).re := (by linarith : delta / 8 ≤ delta).trans (hA p hp)
    have hnorm : ‖inheritedMacdonaldKernel nu p.1 p.2 t‖ ≤
        macdonaldPositiveFiberMajorant nu (delta / 32) t := by
      rw [inheritedMacdonaldKernel_eq_laplace hL hU hz hw hs0 hBpos ht,
        ← complexMacdonaldJoint_integral_v nu p.1 p.2 t]
      apply norm_integral_le_of_norm_le hfiber
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      have hb := complexMacdonaldJoint_norm_le_combined nu
        (by positivity : 0 < delta / 8) hAfloor hBfloor ht v
      have hquarter : (delta / 8) / 4 = delta / 32 := by ring
      simpa only [hquarter] using hb
    exact hnorm.trans (le_add_of_nonneg_left (mul_nonneg
      (mul_nonneg hC.le (Real.exp_pos _).le) hpoly))

/-- Actual original t-integral absolute convergence on all inherited
sheets in the printed slit/sum-quarter domain, in the stated order strip.
This is a convergence theorem, not the Macdonald product identity. -/
theorem inheritedMacdonaldKernel_integrable {nu : ℂ} {r : ℝ}
    (horder : |nu.re| < r) (hr : 0 < r) (hrhalf : r < 1 / 2)
    {z w : ℂ} (hprinted : (z, w) ∈ printedMacdonaldDomain) :
    Integrable (inheritedMacdonaldKernel nu z w) positiveMeasure := by
  obtain ⟨g, hg, hdom⟩ := compact_inheritedMacdonaldKernel_majorant horder hr hrhalf
    (isCompact_singleton : IsCompact ({(z, w)} : Set (ℂ × ℂ)))
    (by intro p hp; have he : p = (z, w) := mem_singleton_iff.mp hp; subst p; exact hprinted)
  have hL : -1 < nu.re := by have h := (abs_lt.mp horder).1; linarith
  have hU : nu.re < 1 := by have h := (abs_lt.mp horder).2; linarith
  apply hg.mono' (inheritedMacdonaldKernel_measurable hL hU z w).aestronglyMeasurable
  filter_upwards [hdom] with t ht
  exact ht (z, w) (by simp)

theorem inherited_macdonald_display_integrable {nu : ℂ} {r : ℝ}
    (horder : |nu.re| < r) (hr : 0 < r) (hrhalf : r < 1 / 2)
    {z w : ℂ} (hprinted : (z, w) ∈ printedMacdonaldDomain) :
    IntegrableOn (fun t =>
      Complex.exp (-(t : ℂ) / 2 - (z ^ 2 + w ^ 2) / (2 * (t : ℂ))) *
        determinedProductK nu z w t / (t : ℂ)) (Ioi 0) := by
  apply (inheritedMacdonaldKernel_integrable horder hr hrhalf hprinted).congr
  exact Eventually.of_forall (inheritedMacdonaldKernel_eq_display nu z w)

end
end ImbalancedChen.Part3.ActualMacdonaldPrintedCompactL120261026b
