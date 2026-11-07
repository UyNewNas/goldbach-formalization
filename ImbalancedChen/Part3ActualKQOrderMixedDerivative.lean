import ImbalancedChen.Part3ActualSpatialJetParameterSeries

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

Honest mixed q/order differentiation of every ACTUAL K q-moment integral.
The common mixed jet is a literal (-cosh)^k*u*sinh(nu*u) Laplace integral.
A proved tilted-cosh envelope absorbs both the q-jet factor and u. Pinned
dominated differentiation is applied separately in complex order and real
q; their identical actual integral proves commutation. No hMixed, formal
jet equality, or connection/asymptotic formula is supplied as a premise.
-/

namespace ImbalancedChen.Part3.ActualKQOrderMixedDerivative20261026b
noncomputable section
open Set Complex MeasureTheory Filter Topology
open ComplexOrderKQCalculus ComplexOrderKHolomorphicSourceOnly RealOrderKPositiveLaplace

def qOrderIntegrand (k : ℕ) (nu : ℂ) (q u : ℝ) : ℂ :=
  (-(Real.cosh u : ℂ)) ^ k * (Real.exp (-q * Real.cosh u) : ℂ) *
    (u : ℂ) * Complex.sinh (nu * (u : ℂ))

def qOrderIntegral (k : ℕ) (nu : ℂ) (q : ℝ) : ℂ :=
  ∫ u in Ioi (0 : ℝ), qOrderIntegrand k nu q u

/-- A genuine common integrable envelope for both derivative operations. -/
theorem qOrderIntegrand_norm_bound (k : ℕ) (nu : ℂ) {a q R u : ℝ}
    (hq : a ≤ q) (hnu : |nu.re| ≤ R) (hu : 0 ≤ u) :
    ‖qOrderIntegrand k nu q u‖ ≤ tiltedCoshDensity ((k : ℝ) + R + 1) a u := by
  have hcosh : Real.cosh u ≤ Real.exp u := by
    simpa only [one_mul, abs_one] using cosh_le_exp_abs_mul 1 hu
  have hp : Real.cosh u ^ k ≤ Real.exp ((k : ℝ) * u) := by
    simpa only [Real.exp_nat_mul] using pow_le_pow_left₀ (Real.cosh_pos u).le hcosh k
  have hsinh : ‖Complex.sinh (nu * (u : ℂ))‖ ≤ Real.exp (R * u) := by
    have h := norm_complex_sinh_le_real_cosh (nu * (u : ℂ))
    have hbase := cosh_le_exp_abs_mul nu.re hu
    have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hnu hu)
    exact (by simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero] using h).trans (hbase.trans he)
  have hexp : Real.exp (-q * Real.cosh u) ≤ Real.exp (-a * Real.cosh u) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hq (Real.cosh_pos u).le]
  have huExp : u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
  calc
    ‖qOrderIntegrand k nu q u‖ =
        (Real.cosh u ^ k * Real.exp (-q * Real.cosh u)) * u * ‖Complex.sinh (nu * (u : ℂ))‖ := by
      simp only [qOrderIntegrand, norm_mul, norm_pow, norm_neg, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (Real.cosh_pos u), abs_of_pos (Real.exp_pos _), abs_of_nonneg hu]
    _ ≤ (Real.exp ((k : ℝ) * u) * Real.exp (-a * Real.cosh u)) * Real.exp u * Real.exp (R * u) :=
      mul_le_mul (mul_le_mul (mul_le_mul hp hexp (Real.exp_pos _).le (Real.exp_pos _).le)
        huExp hu (by positivity)) hsinh (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      unfold tiltedCoshDensity
      congr 1
      ring

theorem qOrderIntegrand_integrable (k : ℕ) (nu : ℂ) {q : ℝ} (hq : 0 < q) :
    IntegrableOn (qOrderIntegrand k nu q) (Ioi (0 : ℝ)) := by
  have hc : Continuous (qOrderIntegrand k nu q) := by unfold qOrderIntegrand; fun_prop
  apply (tiltedCoshDensity_integrable ((k : ℝ) + |nu.re| + 1) hq).integrableOn.mono' hc.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact qOrderIntegrand_norm_bound k nu le_rfl le_rfl hu.le

theorem qMomentIntegrand_hasDerivAt_order (k : ℕ) (nu : ℂ) (q u : ℝ) :
    HasDerivAt (fun w : ℂ => qMomentIntegrand k w q u) (qOrderIntegrand k nu q u) nu := by
  have h := (((hasDerivAt_id nu).mul_const (u : ℂ)).ccosh).const_mul
    ((-(Real.cosh u : ℂ)) ^ k * (Real.exp (-q * Real.cosh u) : ℂ))
  convert h using 1 <;> simp only [qMomentIntegrand, qOrderIntegrand] <;> ring

/-- True complex-order derivative of the actual q-moment integral. -/
theorem qMoment_hasDerivAt_order_integral (k : ℕ) (nu : ℂ) {q : ℝ} (hq : 0 < q) :
    HasDerivAt (fun w : ℂ => qMoment k w q) (qOrderIntegral k nu q) nu := by
  let R : ℝ := |nu.re| + 1
  let U : Set ℂ := {w | |w.re| < R}
  have hU : IsOpen U := isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const
  have hnu : nu ∈ U := by dsimp [U, R]; linarith
  have hm : ∀ᶠ w : ℂ in 𝓝 nu, AEStronglyMeasurable (qMomentIntegrand k w q) (volume.restrict (Ioi (0 : ℝ))) := by
    apply Filter.Eventually.of_forall
    intro w
    have hc : Continuous (qMomentIntegrand k w q) := by unfold qMomentIntegrand; fun_prop
    exact hc.aestronglyMeasurable
  have hb : ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)), ∀ w ∈ U,
      ‖qOrderIntegrand k w q u‖ ≤ tiltedCoshDensity ((k : ℝ) + R + 1) q u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    intro w hw
    exact qOrderIntegrand_norm_bound k w le_rfl hw.le hu.le
  have hd : ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)), ∀ w ∈ U,
      HasDerivAt (fun z : ℂ => qMomentIntegrand k z q u) (qOrderIntegrand k w q u) w :=
    Filter.Eventually.of_forall (fun u w hw => qMomentIntegrand_hasDerivAt_order k w q u)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun w u => qMomentIntegrand k w q u) (F' := fun w u => qOrderIntegrand k w q u)
    (bound := tiltedCoshDensity ((k : ℝ) + R + 1) q) (μ := volume.restrict (Ioi (0 : ℝ)))
    (hU.mem_nhds hnu) hm (qMomentIntegrand_integrable k nu hq)
    (qOrderIntegrand_integrable k nu hq).aestronglyMeasurable hb
    (tiltedCoshDensity_integrable _ hq).integrableOn hd).2

theorem qOrderIntegrand_hasDerivAt_q (k : ℕ) (nu : ℂ) (q u : ℝ) :
    HasDerivAt (fun r : ℝ => qOrderIntegrand k nu r u) (qOrderIntegrand (k + 1) nu q u) q := by
  have h := (((((hasDerivAt_id q).neg.mul_const (Real.cosh u)).exp).ofReal_comp)
    .const_mul ((-(Real.cosh u : ℂ)) ^ k)).mul_const ((u : ℂ) * Complex.sinh (nu * (u : ℂ)))
  convert h using 1 <;> simp only [qOrderIntegrand, Complex.ofReal_mul, Complex.ofReal_neg, pow_succ] <;> ring

/-- True q derivative of the actual complex-order derivative integral. -/
theorem qOrderIntegral_hasDerivAt_q (k : ℕ) (nu : ℂ) {q : ℝ} (hq : 0 < q) :
    HasDerivAt (qOrderIntegral k nu) (qOrderIntegral (k + 1) nu q) q := by
  have ha : 0 < q / 2 := half_pos hq
  let bound := tiltedCoshDensity (((k + 1 : ℕ) : ℝ) + |nu.re| + 1) (q / 2)
  have hm : ∀ᶠ r : ℝ in 𝓝 q, AEStronglyMeasurable (qOrderIntegrand k nu r) (volume.restrict (Ioi (0 : ℝ))) := by
    apply Filter.Eventually.of_forall
    intro r
    have hc : Continuous (qOrderIntegrand k nu r) := by unfold qOrderIntegrand; fun_prop
    exact hc.aestronglyMeasurable
  have hb : ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)), ∀ r ∈ Ioi (q / 2),
      ‖qOrderIntegrand (k + 1) nu r u‖ ≤ bound u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    intro r hr
    exact qOrderIntegrand_norm_bound (k + 1) nu hr.le le_rfl hu.le
  have hd : ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)), ∀ r ∈ Ioi (q / 2),
      HasDerivAt (fun t : ℝ => qOrderIntegrand k nu t u) (qOrderIntegrand (k + 1) nu r u) r :=
    Filter.Eventually.of_forall (fun u r hr => qOrderIntegrand_hasDerivAt_q k nu r u)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun r u => qOrderIntegrand k nu r u) (F' := fun r u => qOrderIntegrand (k + 1) nu r u)
    (bound := bound) (μ := volume.restrict (Ioi (0 : ℝ)))
    (Ioi_mem_nhds (by linarith : q / 2 < q)) hm (qOrderIntegrand_integrable k nu hq)
    (qOrderIntegrand_integrable (k + 1) nu hq).aestronglyMeasurable hb
    (tiltedCoshDensity_integrable _ ha).integrableOn hd).2

/-- HONEST commutation of complex order and real q derivatives of the
actual moment integral. Both sides equal the same dominated mixed integral. -/
theorem qMoment_order_q_derivatives_commute (k : ℕ) (nu : ℂ) {q : ℝ} (hq : 0 < q) :
    deriv (fun r : ℝ => deriv (fun w : ℂ => qMoment k w r) nu) q =
      deriv (fun w : ℂ => deriv (qMoment k w) q) nu := by
  have he : (fun r : ℝ => deriv (fun w : ℂ => qMoment k w r) nu) =ᶠ[𝓝 q] qOrderIntegral k nu := by
    filter_upwards [Ioi_mem_nhds hq] with r hr
    exact (qMoment_hasDerivAt_order_integral k nu hr).deriv
  have hleft := ((qOrderIntegral_hasDerivAt_q k nu hq).congr_of_eventuallyEq he).deriv
  have hqfun : (fun w : ℂ => deriv (qMoment k w) q) = fun w : ℂ => qMoment (k + 1) w q :=
    funext (fun w => (qMoment_hasDerivAt k w hq).deriv)
  rw [hqfun, (qMoment_hasDerivAt_order_integral (k + 1) nu hq).deriv]
  exact hleft

end
end ImbalancedChen.Part3.ActualKQOrderMixedDerivative20261026b
