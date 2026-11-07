import ImbalancedChen.Part3GeneralISmallQWronskian
import ImbalancedChen.Part3PositiveMultiplicativeLog
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.L2Space

/-!
The actual real-order I solution is real and strictly positive. For every
real nu>0 its actual mode and first logarithmic derivative are L2 at the
left logarithmic endpoint. The local exponential bound is obtained from
the proved normalized small-q limits, never assumed. The final statement
transports both L2 functions to the literal physical dq/q measure.
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
-/

namespace ImbalancedChen.Part3.GeneralIRealPositiveEndpoint20261025a

noncomputable section
open Set MeasureTheory Filter Topology
open scoped BigOperators
open GeneralComplexISeriesSourceOnly GeneralIQODE20261025a
open GeneralISmallQWronskian20261025a PositiveMultiplicativeLogSourceOnly

private def realCoeff (nu : ℝ) (n : ℕ) : ℝ :=
  ((n.factorial : ℝ) * Real.Gamma ((n : ℝ) + nu + 1))⁻¹

private theorem coeff_ofReal (nu : ℝ) (n : ℕ) :
    generalICoeff (nu : ℂ) n = (realCoeff nu n : ℂ) := by
  have harg : (n : ℂ) + (nu : ℂ) + 1 = (((n : ℝ) + nu + 1 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [generalICoeff, harg, Complex.Gamma_ofReal]
  simp only [realCoeff, Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_natCast]

private theorem realCoeff_pos {nu : ℝ} (hnu : -1 < nu) (n : ℕ) :
    0 < realCoeff nu n := by
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  exact inv_pos.mpr (mul_pos hf (Real.Gamma_pos_of_pos (by linarith)))

/-- The entire Gamma core has a real positive value on the nonnegative
real axis. Strict positivity is paid by its actual n=0 coefficient. -/
theorem generalICore_real_positive {nu x : ℝ} (hnu : -1 < nu) (hx : 0 ≤ x) :
    (generalICore (nu : ℂ) (x : ℂ)).im = 0 ∧
      0 < (generalICore (nu : ℂ) (x : ℂ)).re := by
  have hnuC : -1 < (nu : ℂ).re := by simpa using hnu
  have hterm (n : ℕ) : generalICoeff (nu : ℂ) n * (x : ℂ) ^ n =
      ((realCoeff nu n * x ^ n : ℝ) : ℂ) := by
    rw [coeff_ofReal, ← Complex.ofReal_pow, ← Complex.ofReal_mul]
  have hs := generalICore_hasSum hnuC (x : ℂ)
  have hsRe : HasSum (fun n : ℕ => realCoeff nu n * x ^ n)
      (generalICore (nu : ℂ) (x : ℂ)).re := by
    simpa only [hterm, Complex.ofReal_re] using Complex.hasSum_re hs
  have hsIm : HasSum (fun _ : ℕ => (0 : ℝ))
      (generalICore (nu : ℂ) (x : ℂ)).im := by
    simpa only [hterm, Complex.ofReal_im] using Complex.hasSum_im hs
  refine ⟨by simpa using hsIm.tsum_eq.symm, ?_⟩
  have hzero : realCoeff nu 0 ≤ (generalICore (nu : ℂ) (x : ℂ)).re := by
    simpa only [Finset.sum_singleton, pow_zero, mul_one] using
      sum_le_hasSum ({0} : Finset ℕ)
        (fun n _ => mul_nonneg (realCoeff_pos hnu n).le (pow_nonneg hx n)) hsRe
  exact (realCoeff_pos hnu 0).trans_le hzero

/-- The literal principal-power I series is real and strictly positive
for every real nu>-1 and q>0. -/
theorem generalI_real_positive {nu q : ℝ} (hnu : -1 < nu) (hq : 0 < q) :
    (generalI (nu : ℂ) q).im = 0 ∧ 0 < (generalI (nu : ℂ) q).re := by
  have hhalf : 0 < q / 2 := by positivity
  have hc := generalICore_real_positive hnu (sq_nonneg (q / 2))
  have hpower : (((q / 2 : ℝ) : ℂ) ^ (nu : ℂ)) = ((q / 2) ^ nu : ℝ) :=
    (Complex.ofReal_cpow hhalf.le nu).symm
  rw [generalI, hpower, ← Complex.ofReal_pow]
  constructor
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      hc.1, zero_mul, mul_zero, add_zero]
  · simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] using
      mul_pos (Real.rpow_pos_of_pos hhalf nu) hc.2

/-- The actual radial mode in additive logarithmic coordinate. -/
def realILogMode (nu r : ℝ) : ℂ := generalI (nu : ℂ) (Real.exp r)

private theorem order_legal {nu : ℝ} (hnu : 0 < nu) : -1 < (nu : ℂ).re := by
  simp only [Complex.ofReal_re]
  linarith

theorem realILogMode_deriv {nu : ℝ} (hnu : 0 < nu) (r : ℝ) :
    deriv (realILogMode nu) r =
      (Real.exp r : ℂ) * deriv (generalI (nu : ℂ)) (Real.exp r) := by
  have h := (generalI_differentiableAt (order_legal hnu) (Real.exp_pos r)).hasDerivAt.scomp
    r (Real.hasDerivAt_exp r)
  simpa only [realILogMode, Function.comp_def, Complex.real_smul] using h.deriv

private theorem realILogMode_continuous {nu : ℝ} (hnu : 0 < nu) :
    Continuous (realILogMode nu) := by
  apply continuous_iff_continuousAt.mpr
  intro r
  exact (generalI_differentiableAt (order_legal hnu) (Real.exp_pos r)).continuousAt.comp
    Real.continuous_exp.continuousAt

private theorem realILogMode_deriv_continuous {nu : ℝ} (hnu : 0 < nu) :
    Continuous (deriv (realILogMode nu)) := by
  have heq : deriv (realILogMode nu) = fun r : ℝ =>
      (Real.exp r : ℂ) * deriv (generalI (nu : ℂ)) (Real.exp r) := by
    funext r
    exact realILogMode_deriv hnu r
  rw [heq]
  apply Continuous.mul (by fun_prop)
  apply continuous_iff_continuousAt.mpr
  intro r
  exact (generalI_deriv_differentiableAt (order_legal hnu) (Real.exp_pos r)).continuousAt.comp
    Real.continuous_exp.continuousAt

private theorem norm_unscale (nu q : ℝ) (hq : 0 < q) (v : ℂ) :
    ‖v‖ = (q / 2) ^ nu * ‖(((q / 2 : ℝ) : ℂ) ^ (-(nu : ℂ))) * v‖ := by
  have hb : ((q / 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (div_pos hq (by norm_num)).ne'
  have hc : (((q / 2 : ℝ) : ℂ) ^ (nu : ℂ)) *
      (((q / 2 : ℝ) : ℂ) ^ (-(nu : ℂ))) = 1 := by
    rw [← Complex.cpow_add _ _ hb, add_neg_cancel, Complex.cpow_zero]
  calc
    ‖v‖ = ‖(((q / 2 : ℝ) : ℂ) ^ (nu : ℂ)) *
        ((((q / 2 : ℝ) : ℂ) ^ (-(nu : ℂ))) * v)‖ := by rw [← mul_assoc, hc, one_mul]
    _ = _ := by
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (div_pos hq (by norm_num))]
      rfl

private theorem unscale_bound {nu C : ℝ} (hnu : 0 < nu) (hC : 0 ≤ C)
    (r : ℝ) (v : ℂ)
    (hv : ‖(((Real.exp r / 2 : ℝ) : ℂ) ^ (-(nu : ℂ))) * v‖ ≤ C) :
    ‖v‖ ≤ C * Real.exp (nu * r) := by
  have hp : (Real.exp r / 2) ^ nu ≤ Real.exp (nu * r) := by
    calc
      _ ≤ (Real.exp r) ^ nu := Real.rpow_le_rpow (by positivity)
        (by nlinarith [Real.exp_pos r]) hnu.le
      _ = _ := by
        rw [Real.rpow_def_of_pos (Real.exp_pos r), Real.log_exp]
        congr 1
        ring
  rw [norm_unscale nu (Real.exp r) (Real.exp_pos r) v]
  exact (mul_le_mul_of_nonneg_left hv (Real.rpow_nonneg (by positivity) _)).trans
    (by simpa only [mul_comm] using mul_le_mul_of_nonneg_right hp hC)

/-- The two actual normalized limits give a genuine local exponential
bound for the mode and its actual first log derivative. -/
theorem exists_left_exponential_bound {nu : ℝ} (hnu : 0 < nu) :
    ∃ C R : ℝ, 0 < C ∧ ∀ r ≤ R,
      ‖realILogMode nu r‖ ≤ C * Real.exp (nu * r) ∧
        ‖deriv (realILogMode nu) r‖ ≤ C * Real.exp (nu * r) := by
  let A : ℂ := (Complex.Gamma ((nu : ℂ) + 1))⁻¹
  let B : ℂ := (nu : ℂ) * A
  let C : ℝ := ‖A‖ + ‖B‖ + 2
  have hC : 0 < C := by dsimp [C]; positivity
  have hlimI := Real.tendsto_comp_exp_atBot.mpr
    (tendsto_scaled_generalI_zero (order_legal hnu)).norm
  have hlimD := Real.tendsto_comp_exp_atBot.mpr
    (tendsto_scaled_generalI_deriv_zero (order_legal hnu)).norm
  have hI := hlimI.eventually (gt_mem_nhds (lt_add_one ‖A‖))
  have hD := hlimD.eventually (gt_mem_nhds (lt_add_one ‖B‖))
  have hb : ∀ᶠ r : ℝ in atBot,
      ‖(((Real.exp r / 2 : ℝ) : ℂ) ^ (-(nu : ℂ))) * generalI (nu : ℂ) (Real.exp r)‖ ≤ C ∧
      ‖(Real.exp r : ℂ) * (((Real.exp r / 2 : ℝ) : ℂ) ^ (-(nu : ℂ))) *
        deriv (generalI (nu : ℂ)) (Real.exp r)‖ ≤ C := by
    filter_upwards [hI, hD] with r hi hd
    dsimp only [A, B] at hi hd ⊢
    constructor <;> dsimp [C, A, B] <;> linarith [norm_nonneg A, norm_nonneg B]
  obtain ⟨R, hR⟩ := eventually_atBot.mp hb
  refine ⟨C, R, hC, ?_⟩
  intro r hr
  have hh := hR r hr
  refine ⟨unscale_bound hnu hC.le r _ hh.1, ?_⟩
  rw [realILogMode_deriv hnu r]
  apply unscale_bound hnu hC.le r
  simpa only [mul_comm, mul_left_comm, mul_assoc] using hh.2

private theorem square_integrable_left {g : ℝ → ℂ} (hg : Continuous g)
    {nu C R : ℝ} (hnu : 0 < nu)
    (hbound : ∀ r ≤ R, ‖g r‖ ≤ C * Real.exp (nu * r)) :
    IntegrableOn (fun r : ℝ => ‖g r‖ ^ 2) (Iic R) := by
  have hmajor : IntegrableOn (fun r : ℝ => C ^ 2 * Real.exp ((2 * nu) * r)) (Iic R) :=
    (integrableOn_exp_mul_Iic (mul_pos (by norm_num) hnu) R).const_mul (C ^ 2)
  apply hmajor.mono' (hg.norm.pow 2).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Iic] with r hr
  have hsq := pow_le_pow_left₀ (norm_nonneg (g r)) (hbound r hr) 2
  have he : (Real.exp (nu * r)) ^ 2 = Real.exp ((2 * nu) * r) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖g r‖), mul_pow, he] using hsq

/-- Actual left-end L2 regularity of both the mode and its native first
log derivative. The strict positive order is the real integrability gain. -/
theorem exists_left_log_L2 {nu : ℝ} (hnu : 0 < nu) :
    ∃ R : ℝ,
      MemLp (realILogMode nu) 2 ((volume : Measure ℝ).restrict (Iic R)) ∧
      MemLp (deriv (realILogMode nu)) 2 ((volume : Measure ℝ).restrict (Iic R)) := by
  obtain ⟨C, R, hC, hb⟩ := exists_left_exponential_bound hnu
  refine ⟨R, ?_, ?_⟩
  · apply (memLp_two_iff_integrable_sq_norm (realILogMode_continuous hnu).aestronglyMeasurable).mpr
    exact square_integrable_left (realILogMode_continuous hnu) hnu (fun r hr => (hb r hr).1)
  · apply (memLp_two_iff_integrable_sq_norm (realILogMode_deriv_continuous hnu).aestronglyMeasurable).mpr
    exact square_integrable_left (realILogMode_deriv_continuous hnu) hnu (fun r hr => (hb r hr).2)

/-- The same regular endpoint in the literal physical dq/q space. The
Euler derivative qI' is exactly the first logarithmic derivative. -/
theorem exists_left_physical_L2 {nu : ℝ} (hnu : 0 < nu) :
    ∃ Q : ℝ, 0 < Q ∧
      MemLp (generalI (nu : ℂ)) 2
        (positiveMultiplicativeMeasure.restrict (Ioc 0 Q)) ∧
      MemLp (fun q : ℝ => (q : ℂ) * deriv (generalI (nu : ℂ)) q) 2
        (positiveMultiplicativeMeasure.restrict (Ioc 0 Q)) := by
  obtain ⟨R, hI, hD⟩ := exists_left_log_L2 hnu
  have hmap := log_measurePreserving.restrict_preimage (measurableSet_Iic : MeasurableSet (Iic R))
  have hsub : Ioc (0 : ℝ) (Real.exp R) ⊆ Real.log ⁻¹' Iic R := by
    intro q hq
    change Real.log q ≤ R
    simpa only [Real.log_exp] using Real.log_le_log hq.1 hq.2
  have hIlog := (hI.comp_measurePreserving hmap).mono_measure (Measure.restrict_mono hsub le_rfl)
  have hDlog := (hD.comp_measurePreserving hmap).mono_measure (Measure.restrict_mono hsub le_rfl)
  refine ⟨Real.exp R, Real.exp_pos R, ?_, ?_⟩
  · apply (memLp_congr_ae (show (realILogMode nu ∘ Real.log) =ᵐ[
        positiveMultiplicativeMeasure.restrict (Ioc 0 (Real.exp R))] generalI (nu : ℂ) from ?_)).mp hIlog
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with q hq
    simp only [Function.comp_def, realILogMode, Real.exp_log hq.1]
  · apply (memLp_congr_ae (show (deriv (realILogMode nu) ∘ Real.log) =ᵐ[
        positiveMultiplicativeMeasure.restrict (Ioc 0 (Real.exp R))]
        (fun q : ℝ => (q : ℂ) * deriv (generalI (nu : ℂ)) q) from ?_)).mp hDlog
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with q hq
    simp only [Function.comp_def, realILogMode_deriv hnu, Real.exp_log hq.1]

end
end ImbalancedChen.Part3.GeneralIRealPositiveEndpoint20261025a