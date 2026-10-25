import ImbalancedChen.Part3RegularizedNegativeGamma

/-! SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
The second actual small-q coefficient on 0<Re nu<1. The finite defect
identity uses the reciprocal substitution t=q^2/(4u), and its limit uses
the absolutely convergent regularized Gamma integral. Positive real bases
fix every principal complex-power branch. -/

namespace ImbalancedChen.Part3.ComplexOrderKSecondSmallArgument20261025a
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open ComplexOrderKBridgeSourceOnly ComplexOrderKPositiveLaplace20261025a
open ComplexOrderKSmallArgument20261025a RegularizedNegativeGamma20261025a

def gammaDefect (ν : ℂ) (q t : ℝ) : ℂ :=
  (Real.exp (-t) : ℂ) * (t : ℂ) ^ (ν - 1) *
    ((Real.exp (-(q ^ 2 / (4 * t))) : ℂ) - 1)

theorem reciprocal_power_jacobian (ν : ℂ) {s u : ℝ} (hs : 0 < s) (hu : 0 < u) :
    ((s / u ^ 2 : ℝ) : ℂ) * ((s / u : ℝ) : ℂ) ^ (ν - 1) =
      (s : ℂ) ^ ν * (u : ℂ) ^ (-ν - 1) := by
  have hsC : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  have huC : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
  have hup : (u : ℂ) ^ (ν - 1) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl huC)
  have hsp : (s : ℂ) * (s : ℂ) ^ (ν - 1) = (s : ℂ) ^ ν := by
    calc
      _ = (s : ℂ) ^ (1 : ℂ) * (s : ℂ) ^ (ν - 1) := by rw [Complex.cpow_one]
      _ = (s : ℂ) ^ ((1 : ℂ) + (ν - 1)) := (Complex.cpow_add _ _ hsC).symm
      _ = _ := by congr 1; ring
  have hcomb : (u : ℂ) ^ (ν - 1) * (u : ℂ) ^ (-ν - 1) =
      (u : ℂ) ^ (-2 : ℂ) := by
    rw [← Complex.cpow_add _ _ huC]
    congr 1
    ring
  have hunit : (u : ℂ) ^ 2 *
      ((u : ℂ) ^ (ν - 1) * (u : ℂ) ^ (-ν - 1)) = 1 := by
    rw [hcomb, Complex.cpow_neg, Complex.cpow_two]
    exact mul_inv_cancel₀ (pow_ne_zero 2 huC)
  have hinv : 1 / ((u : ℂ) ^ 2 * (u : ℂ) ^ (ν - 1)) = (u : ℂ) ^ (-ν - 1) := by
    apply (div_eq_iff (mul_ne_zero (pow_ne_zero 2 huC) hup)).mpr
    calc
      _ = (u : ℂ) ^ 2 * ((u : ℂ) ^ (ν - 1) * (u : ℂ) ^ (-ν - 1)) := hunit.symm
      _ = _ := by ring
  rw [Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_div,
    Complex.div_cpow_ofReal_nonneg hs.le hu.le]
  calc
    _ = ((s : ℂ) * (s : ℂ) ^ (ν - 1)) *
        (1 / ((u : ℂ) ^ 2 * (u : ℂ) ^ (ν - 1))) := by ring
    _ = _ := by rw [hsp, hinv]

theorem gammaDefect_reciprocal_pullback (ν : ℂ) {q u : ℝ} (hq : 0 < q) (hu : 0 < u) :
    ((q ^ 2 / 4 / u ^ 2 : ℝ) : ℂ) * gammaDefect ν q (q ^ 2 / 4 / u) =
      ((q ^ 2 / 4 : ℝ) : ℂ) ^ ν * dampedRegularizedKernel ν q u := by
  have hs : 0 < q ^ 2 / 4 := by positivity
  have he1 : q ^ 2 / 4 / u = q ^ 2 / (4 * u) := by
    field_simp [hu.ne'] <;> ring
  have he2 : q ^ 2 / (4 * (q ^ 2 / 4 / u)) = u := by
    field_simp [hq.ne', hu.ne'] <;> ring
  unfold gammaDefect dampedRegularizedKernel regularizedKernel
  rw [he2]
  calc
    _ = (((q ^ 2 / 4 / u ^ 2 : ℝ) : ℂ) *
        ((q ^ 2 / 4 / u : ℝ) : ℂ) ^ (ν - 1)) *
        (Real.exp (-(q ^ 2 / 4 / u)) : ℂ) * ((Real.exp (-u) : ℂ) - 1) := by ring
    _ = _ := by rw [reciprocal_power_jacobian ν hs hu, he1]; ring

/-- Exact defect inversion; no limiting argument is used here. -/
theorem gammaDefect_integral (ν : ℂ) {q : ℝ} (hq : 0 < q) :
    (∫ t in Ioi (0 : ℝ), gammaDefect ν q t) =
      ((q ^ 2 / 4 : ℝ) : ℂ) ^ ν *
        ∫ u in Ioi (0 : ℝ), dampedRegularizedKernel ν q u := by
  let s : ℝ := q ^ 2 / 4
  have hs : 0 < s := by dsimp [s]; positivity
  have hder : ∀ u ∈ Ioi (0 : ℝ), HasDerivAt (fun t : ℝ => s / t) (-s / u ^ 2) u := by
    intro u hu
    convert (hasDerivAt_const u s).div (hasDerivAt_id u) hu.ne' using 1 <;> simp <;> ring
  have hinj : Set.InjOn (fun u : ℝ => s / u) (Ioi 0) := by
    intro u hu v hv he
    have hh := (div_eq_div_iff hu.ne' hv.ne').mp he
    exact (mul_left_cancel₀ hs.ne') hh.symm
  have himage : (fun u : ℝ => s / u) '' Ioi 0 = Ioi 0 := by
    ext t
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact div_pos hs hu
    · intro ht
      refine ⟨s / t, div_pos hs ht, ?_⟩
      field_simp [hs.ne', ht.ne'] <;> ring
  have hsub := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun u hu => (hder u hu).hasDerivWithinAt) hinj (gammaDefect ν q)
  rw [himage] at hsub
  rw [hsub, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  have hn : -s / u ^ 2 ≤ 0 := div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs.le) (sq_nonneg u)
  rw [abs_of_nonpos hn, neg_div, neg_neg, Complex.real_smul]
  exact gammaDefect_reciprocal_pullback ν hq hu

theorem gammaDefect_integral_eq_difference {ν : ℂ} (hν : 0 < ν.re) (q : ℝ) :
    (∫ t in Ioi (0 : ℝ), gammaDefect ν q t) =
      (∫ t in Ioi (0 : ℝ), dampedGammaDensity ν q t) - Complex.Gamma ν := by
  rw [Complex.Gamma_eq_integral hν]
  unfold Complex.GammaIntegral
  rw [← integral_sub (dampedGammaDensity_integrable hν q) (Complex.GammaIntegral_convergent hν)]
  apply integral_congr_ae
  exact Eventually.of_forall (fun t => by unfold gammaDefect dampedGammaDensity; ring)

/-- The finite second renormalization is exactly a regularized Gamma integral. -/
theorem second_normalized_K_eq_integral {ν : ℂ} (hν : 0 < ν.re) {q : ℝ} (hq : 0 < q) :
    (q : ℂ) ^ (-ν) * (complexOrderK ν q -
      (2 : ℂ) ^ (ν - 1) * Complex.Gamma ν * (q : ℂ) ^ (-ν)) =
      (2 : ℂ) ^ (-ν - 1) *
        ∫ u in Ioi (0 : ℝ), dampedRegularizedKernel ν q u := by
  let C : ℂ := ((q / 2 : ℝ) : ℂ) ^ ν
  let T : ℂ := (2 : ℂ) ^ ν
  let J : ℂ := ∫ u in Ioi (0 : ℝ), dampedRegularizedKernel ν q u
  have hc : 0 < q / 2 := half_pos hq
  have hC : C ≠ 0 := Complex.cpow_ne_zero_iff.mpr
    (Or.inl (Complex.ofReal_ne_zero.mpr hc.ne'))
  have hT : T ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  have hqpow : (q : ℂ) ^ ν = T * C := by
    have he : (q : ℂ) = ((2 : ℝ) : ℂ) * ((q / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [he]
    exact Complex.mul_cpow_ofReal_nonneg (by norm_num) hc.le ν
  have hspow : ((q ^ 2 / 4 : ℝ) : ℂ) ^ ν = C * C := by
    have he : ((q ^ 2 / 4 : ℝ) : ℂ) = ((q / 2 : ℝ) : ℂ) * ((q / 2 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [he]
    exact Complex.mul_cpow_ofReal_nonneg hc.le hc.le ν
  have hfirst : (2 : ℂ) ^ (ν - 1) = T / 2 := by
    rw [Complex.cpow_sub _ _ (by norm_num : (2 : ℂ) ≠ 0), Complex.cpow_one]
  have hsecond : (2 : ℂ) ^ (-ν - 1) = T⁻¹ / 2 := by
    rw [Complex.cpow_sub _ _ (by norm_num : (2 : ℂ) ≠ 0), Complex.cpow_one, Complex.cpow_neg]
  have hdef := gammaDefect_integral_eq_difference hν q
  rw [gammaDefect_integral ν hq, dampedGammaDensity_integral ν hq, hspow] at hdef
  have hdiff : complexOrderK ν q - Complex.Gamma ν / (2 * C) = C / 2 * J := by
    apply (mul_left_cancel₀ (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) hC))
    calc
      _ = 2 * C * complexOrderK ν q - Complex.Gamma ν := by field_simp [hC] <;> ring
      _ = C * C * J := hdef.symm
      _ = _ := by ring
  simp only [Complex.cpow_neg, hqpow, hfirst, hsecond]
  have hlead : T / 2 * Complex.Gamma ν * (T * C)⁻¹ = Complex.Gamma ν / (2 * C) := by
    field_simp [hT, hC] <;> ring
  rw [hlead, hdiff]
  change (T * C)⁻¹ * (C / 2 * J) = T⁻¹ / 2 * J
  field_simp [hT, hC] <;> ring

/-- The genuine second small-argument coefficient, with its exact branch
and order-strip hypotheses and no assumed asymptotic or connection. -/
theorem complexOrderK_second_small_argument {ν : ℂ}
    (hν : 0 < ν.re) (hν1 : ν.re < 1) :
    Tendsto (fun q : ℝ => (q : ℂ) ^ (-ν) * (complexOrderK ν q -
      (2 : ℂ) ^ (ν - 1) * Complex.Gamma ν * (q : ℂ) ^ (-ν)))
      (𝓝[>] (0 : ℝ)) (𝓝 ((2 : ℂ) ^ (-ν - 1) * Complex.Gamma (-ν))) := by
  have hlim := (dampedRegularizedKernel_integral_tendsto hν hν1).mono_left nhdsWithin_le_nhds
  have hmul : Tendsto (fun q : ℝ => (2 : ℂ) ^ (-ν - 1) *
      ∫ u in Ioi (0 : ℝ), dampedRegularizedKernel ν q u)
      (𝓝[>] (0 : ℝ)) (𝓝 ((2 : ℂ) ^ (-ν - 1) * Complex.Gamma (-ν))) :=
    tendsto_const_nhds.mul hlim
  apply hmul.congr'
  filter_upwards [self_mem_nhdsWithin] with q hq
  exact (second_normalized_K_eq_integral hν hq).symm

end
end ImbalancedChen.Part3.ComplexOrderKSecondSmallArgument20261025a
