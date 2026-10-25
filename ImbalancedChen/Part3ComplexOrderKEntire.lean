import ImbalancedChen.Part3ComplexOrderKHolomorphic

/-!
# Entire dependence of the actual positive-axis K integral on its order

CODE_ONLY / SOURCE_ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The previous derivative theorem was restricted to |Re nu|<7/32. Here a
quadratic cosh bound supplies an explicit integrable envelope on EVERY
closed real-part strip, uniform for q>=a>0. Polynomial order moments are
also absolutely integrable. Dominated differentiation then proves the
literal complex-order K integral differentiable at every complex order.
The existing real and imaginary identities use this same actual integral.
No q derivative, spectral identity, or spectral estimate is asserted.
-/

namespace ImbalancedChen.Part3.ComplexOrderKEntire20261025a

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology
open ComplexOrderKBridgeSourceOnly
open ComplexOrderKHolomorphicSourceOnly

private theorem quadratic_cosh_lower {u : ℝ} (hu : 0 ≤ u) :
    u ^ 2 / 8 ≤ Real.cosh u := by
  have he := Real.add_one_le_exp (u / 2)
  have hb : 0 ≤ u / 2 + 1 := by linarith only [hu]
  have hs : (u / 2 + 1) ^ 2 ≤ (Real.exp (u / 2)) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr he)
      (add_nonneg (Real.exp_nonneg _) hb)]
  have hexp : Real.exp u = (Real.exp (u / 2)) ^ 2 := by
    calc
      Real.exp u = Real.exp (u / 2 + u / 2) := by congr 1 <;> ring
      _ = Real.exp (u / 2) * Real.exp (u / 2) := Real.exp_add _ _
      _ = (Real.exp (u / 2)) ^ 2 := by ring
  rw [Real.cosh_eq, hexp]
  nlinarith [Real.exp_pos (-u)]

/-- The order-strip growth is absorbed by the quadratic Laplace exponent. -/
theorem real_cosh_strip_envelope {a q R x u : ℝ}
    (ha : 0 < a) (hq : a ≤ q) (hx : |x| ≤ R) (hu : 0 ≤ u) :
    Real.exp (-q * Real.cosh u) * Real.cosh (x * u) ≤
      Real.exp (2 * (R + 1) ^ 2 / a) * Real.exp (-u) := by
  have hxP : x ≤ R := (le_abs_self x).trans hx
  have hxN : -x ≤ R := (neg_le_abs x).trans hx
  have hcosh : Real.cosh (x * u) ≤ Real.exp (R * u) := by
    have hp := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hxP hu)
    have hn : Real.exp (-(x * u)) ≤ Real.exp (R * u) := by
      apply Real.exp_le_exp.mpr
      nlinarith only [mul_le_mul_of_nonneg_right hxN hu]
    rw [Real.cosh_eq]
    linarith only [hp, hn]
  have hc := quadratic_cosh_lower hu
  have hqcosh := mul_le_mul_of_nonneg_right hq (Real.cosh_pos u).le
  have hcancel : a * (2 * (R + 1) ^ 2 / a) = 2 * (R + 1) ^ 2 := by
    field_simp [ha.ne']
  have hsq := sq_nonneg (a * u - 4 * (R + 1))
  have hcs : 0 ≤ a ^ 2 * (Real.cosh u - u ^ 2 / 8) :=
    mul_nonneg (sq_nonneg a) (sub_nonneg.mpr hc)
  have hlinear : (R + 1) * u - 2 * (R + 1) ^ 2 / a ≤ a * Real.cosh u := by
    have hmul : 0 ≤ a * (a * Real.cosh u - (R + 1) * u +
        2 * (R + 1) ^ 2 / a) := by
      nlinarith only [hcs, hsq, hcancel]
    nlinarith only [hmul, ha]
  calc
    Real.exp (-q * Real.cosh u) * Real.cosh (x * u) ≤
        Real.exp (-q * Real.cosh u) * Real.exp (R * u) :=
      mul_le_mul_of_nonneg_left hcosh (Real.exp_pos _).le
    _ = Real.exp (-q * Real.cosh u + R * u) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (2 * (R + 1) ^ 2 / a - u) := by
      apply Real.exp_le_exp.mpr
      nlinarith only [hlinear, hqcosh]
    _ = Real.exp (2 * (R + 1) ^ 2 / a) * Real.exp (-u) := by
      rw [← Real.exp_add]
      congr 1 <;> ring

/-- A factorial polynomial damping bound for every natural order moment. -/
theorem polynomial_exp_damping (k : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    u ^ k * Real.exp (-u) ≤
      (k.factorial : ℝ) * 2 ^ k * Real.exp (-(u / 2)) := by
  have hfac : 0 < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hp0 := Real.pow_div_factorial_le_exp (by positivity : 0 ≤ u / 2) k
  have hp : (u / 2) ^ k ≤ (k.factorial : ℝ) * Real.exp (u / 2) := by
    simpa only [mul_comm] using (div_le_iff₀ hfac).mp hp0
  have hpower : u ^ k ≤ (k.factorial : ℝ) * 2 ^ k * Real.exp (u / 2) := by
    have hh := mul_le_mul_of_nonneg_right hp (by positivity : (0 : ℝ) ≤ 2 ^ k)
    have hcancel : (u / 2) ^ k * (2 : ℝ) ^ k = u ^ k := by
      rw [← mul_pow]
      congr 1
      ring
    rw [hcancel] at hh
    nlinarith only [hh]
  calc
    u ^ k * Real.exp (-u) ≤
        ((k.factorial : ℝ) * 2 ^ k * Real.exp (u / 2)) * Real.exp (-u) :=
      mul_le_mul_of_nonneg_right hpower (Real.exp_pos _).le
    _ = (k.factorial : ℝ) * 2 ^ k * Real.exp (-(u / 2)) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 1 <;> ring

def orderMomentEnvelope (k : ℕ) (a R u : ℝ) : ℝ :=
  (k.factorial : ℝ) * 2 ^ k * Real.exp (2 * (R + 1) ^ 2 / a) *
    Real.exp (-(u / 2))

theorem orderMomentEnvelope_integrable (k : ℕ) (a R : ℝ) :
    IntegrableOn (orderMomentEnvelope k a R) (Ioi 0) := by
  have h : IntegrableOn (fun u : ℝ => Real.exp ((-(1 / 2) : ℝ) * u)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (by norm_num : (-(1 / 2) : ℝ) < 0) 0
  have heq : (fun u : ℝ => Real.exp ((-(1 / 2) : ℝ) * u)) =
      (fun u : ℝ => Real.exp (-(u / 2))) := by
    funext u
    congr 1 <;> ring
  rw [heq] at h
  exact h.const_mul _

/-- Uniform domination of every cosh order moment on an arbitrary strip. -/
theorem complexOrderMoment_norm_le (k : ℕ) {a q R u : ℝ} {ν : ℂ}
    (ha : 0 < a) (hq : a ≤ q) (hν : |ν.re| ≤ R) (hu : 0 ≤ u) :
    ‖(u : ℂ) ^ k * complexOrderIntegrand ν q u‖ ≤ orderMomentEnvelope k a R u := by
  have hbase := (complexOrderIntegrand_norm_le_real ν q u).trans
    (real_cosh_strip_envelope ha hq hν hu)
  have hnorm : ‖(u : ℂ) ^ k‖ = u ^ k := by
    simp only [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu]
  rw [norm_mul, hnorm]
  calc
    u ^ k * ‖complexOrderIntegrand ν q u‖ ≤
        u ^ k * (Real.exp (2 * (R + 1) ^ 2 / a) * Real.exp (-u)) :=
      mul_le_mul_of_nonneg_left hbase (pow_nonneg hu k)
    _ ≤ orderMomentEnvelope k a R u := by
      have hh := mul_le_mul_of_nonneg_left (polynomial_exp_damping k hu)
        (Real.exp_pos (2 * (R + 1) ^ 2 / a)).le
      unfold orderMomentEnvelope
      nlinarith only [hh]

theorem complexOrderMoment_integrable (k : ℕ) (ν : ℂ) {q : ℝ} (hq : 0 < q) :
    IntegrableOn (fun u : ℝ => (u : ℂ) ^ k * complexOrderIntegrand ν q u) (Ioi 0) := by
  have hc : Continuous (fun u : ℝ => (u : ℂ) ^ k * complexOrderIntegrand ν q u) := by
    unfold complexOrderIntegrand
    fun_prop
  apply (orderMomentEnvelope_integrable k q |ν.re|).mono' hc.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact complexOrderMoment_norm_le k hq le_rfl le_rfl hu.le

/-- The literal derivative integrand has the k=1 strip envelope. -/
theorem complexOrderDeriv_norm_le {a q R u : ℝ} {ν : ℂ}
    (ha : 0 < a) (hq : a ≤ q) (hν : |ν.re| ≤ R) (hu : 0 ≤ u) :
    ‖complexOrderDerivIntegrand ν q u‖ ≤ orderMomentEnvelope 1 a R u := by
  have hs : ‖Complex.sinh (ν * (u : ℂ))‖ ≤ Real.cosh (ν.re * u) := by
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero] using norm_complex_sinh_le_real_cosh (ν * (u : ℂ))
  have hm : ‖complexOrderDerivIntegrand ν q u‖ ≤
      u * (Real.exp (-q * Real.cosh u) * Real.cosh (ν.re * u)) := by
    calc
      ‖complexOrderDerivIntegrand ν q u‖ =
          u * (Real.exp (-q * Real.cosh u) * ‖Complex.sinh (ν * (u : ℂ))‖) := by
        simp only [complexOrderDerivIntegrand, norm_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_of_nonneg hu]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le) hu
  have hb := mul_le_mul_of_nonneg_left (real_cosh_strip_envelope ha hq hν hu) hu
  have hd := mul_le_mul_of_nonneg_left (polynomial_exp_damping 1 hu)
    (Real.exp_pos (2 * (R + 1) ^ 2 / a)).le
  unfold orderMomentEnvelope
  simp only [pow_one] at hd ⊢
  nlinarith only [hm, hb, hd]

private theorem integrand_order_derivative (ν : ℂ) (q u : ℝ) :
    HasDerivAt (fun z : ℂ => complexOrderIntegrand z q u)
      (complexOrderDerivIntegrand ν q u) ν := by
  have hm : HasDerivAt (fun z : ℂ => z * (u : ℂ)) (u : ℂ) ν := by
    simpa using (hasDerivAt_id ν).mul_const (u : ℂ)
  have hd := hm.ccosh.const_mul (Real.exp (-q * Real.cosh u) : ℂ)
  simpa only [complexOrderIntegrand, complexOrderDerivIntegrand,
    mul_assoc, mul_comm, mul_left_comm] using hd

/-- Genuine order derivative, at every complex order, of the actual K. -/
theorem complexOrderK_hasDerivAt_all (ν : ℂ) {q : ℝ} (hq : 0 < q) :
    HasDerivAt (fun z : ℂ => complexOrderK z q)
      (∫ u in Ioi (0 : ℝ), complexOrderDerivIntegrand ν q u) ν := by
  let R : ℝ := |ν.re| + 1
  let s : Set ℂ := {z | |z.re| < R}
  have hsOpen : IsOpen s :=
    isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const
  have hs : s ∈ 𝓝 ν := hsOpen.mem_nhds (by dsimp [s, R]; linarith)
  have hFmeas : ∀ᶠ z in 𝓝 ν,
      AEStronglyMeasurable (complexOrderIntegrand z q) (volume.restrict (Ioi (0 : ℝ))) := by
    apply Eventually.of_forall
    intro z
    have hc : Continuous (complexOrderIntegrand z q) := by
      unfold complexOrderIntegrand
      fun_prop
    exact hc.aestronglyMeasurable
  have hFint : IntegrableOn (complexOrderIntegrand ν q) (Ioi 0) := by
    simpa only [pow_zero, one_mul] using complexOrderMoment_integrable 0 ν hq
  have hF'meas : AEStronglyMeasurable (complexOrderDerivIntegrand ν q)
      (volume.restrict (Ioi (0 : ℝ))) := by
    have hc : Continuous (complexOrderDerivIntegrand ν q) := by
      unfold complexOrderDerivIntegrand
      fun_prop
    exact hc.aestronglyMeasurable
  have hbound : ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)),
      ∀ z ∈ s, ‖complexOrderDerivIntegrand z q u‖ ≤ orderMomentEnvelope 1 q R u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    intro z hz
    exact complexOrderDeriv_norm_le hq le_rfl (le_of_lt hz) hu.le
  have hdiff : ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)), ∀ z ∈ s,
      HasDerivAt (fun w : ℂ => complexOrderIntegrand w q u)
        (complexOrderDerivIntegrand z q u) z :=
    Eventually.of_forall (fun u z _ => integrand_order_derivative z q u)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z u => complexOrderIntegrand z q u)
    (F' := fun z u => complexOrderDerivIntegrand z q u)
    (bound := orderMomentEnvelope 1 q R)
    hs hFmeas hFint hF'meas hbound (orderMomentEnvelope_integrable 1 q R) hdiff).2

theorem complexOrderK_differentiable_all {q : ℝ} (hq : 0 < q) :
    Differentiable ℂ (fun ν : ℂ => complexOrderK ν q) :=
  fun ν => (complexOrderK_hasDerivAt_all ν hq).differentiableAt

end
end ImbalancedChen.Part3.ComplexOrderKEntire20261025a
