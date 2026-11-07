import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

/-!
CODE_ONLY / SOURCEONLY / UNCOMPILED, 2026-10-25. No acceptance credit.

Scalar Poisson/Stieltjes interval inversion for every finite Borel measure
on R. The exact interval kernel is evaluated by arctan, bounded between
zero and one, and converges pointwise to the interval indicator with half
weight at each endpoint. Finite-measure dominated convergence and genuine
product Fubini prove the double-integral limit, including endpoint atoms.

The interval is explicitly nondegenerate a<b. No Poisson inversion,
spectral measure, resolvent boundary value or target identity is a premise.
This supplies scalar measure inversion, not a spectral theorem or Stone
formula for an operator.
-/

namespace ImbalancedChen.Part3.ScalarStieltjesPoissonInversion20261025a

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

def poissonKernel (ε t x : ℝ) : ℝ :=
  ε / (Real.pi * ((x - t) ^ 2 + ε ^ 2))

def intervalWeight (a b ε x : ℝ) : ℝ :=
  (Real.arctan ((b - x) / ε) - Real.arctan ((a - x) / ε)) / Real.pi

def endpointProfile (a b x : ℝ) : ℝ :=
  (Ioo a b).indicator (fun _ : ℝ => 1) x +
    ({a} : Set ℝ).indicator (fun _ : ℝ => (1 / 2 : ℝ)) x +
    ({b} : Set ℝ).indicator (fun _ : ℝ => (1 / 2 : ℝ)) x

private def arctanJump (c : ℝ) : ℝ :=
  if 0 < c then Real.pi / 2 else if c < 0 then -(Real.pi / 2) else 0

private theorem tendsto_arctan_div (c : ℝ) :
    Tendsto (fun ε : ℝ => Real.arctan (c / ε)) (𝓝[>] 0) (𝓝 (arctanJump c)) := by
  rcases lt_trichotomy c 0 with hc | rfl | hc
  · have hdiv : Tendsto (fun ε : ℝ => c / ε) (𝓝[>] 0) atBot := by
      simpa only [div_eq_mul_inv] using
        (tendsto_inv_nhdsGT_zero.const_mul_atTop_of_neg hc)
    simpa only [arctanJump, if_neg (not_lt_of_ge hc.le), if_pos hc] using
      (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atBot).comp hdiv
  · simpa [arctanJump] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[>] 0) (𝓝 0))
  · have hdiv : Tendsto (fun ε : ℝ => c / ε) (𝓝[>] 0) atTop := by
      simpa only [div_eq_mul_inv] using
        (tendsto_inv_nhdsGT_zero.const_mul_atTop hc)
    simpa only [arctanJump, if_pos hc] using
      (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop).comp hdiv

private theorem arctanJump_difference {a b : ℝ} (hab : a < b) (x : ℝ) :
    (arctanJump (b - x) - arctanJump (a - x)) / Real.pi = endpointProfile a b x := by
  rcases lt_trichotomy x a with hxa | rfl | hax
  · have hxb : x < b := hxa.trans hab
    have hnot : ¬a < x := not_lt_of_ge hxa.le
    simp [arctanJump, endpointProfile, sub_pos.mpr hxa, sub_pos.mpr hxb,
      hxa.ne, hxb.ne, hnot]
  · simp [arctanJump, endpointProfile, sub_pos.mpr hab, hab.ne, hab.ne'] <;>
      field_simp [Real.pi_ne_zero] <;> ring
  · rcases lt_trichotomy x b with hxb | rfl | hbx
    · have ha : a - x < 0 := sub_neg.mpr hax
      have hb : 0 < b - x := sub_pos.mpr hxb
      simp [arctanJump, endpointProfile, ha, hb, not_lt_of_ge ha.le,
        hax, hxb, hax.ne', hxb.ne] <;> field_simp [Real.pi_ne_zero] <;> ring
    · have ha : a - b < 0 := sub_neg.mpr hab
      simp [arctanJump, endpointProfile, ha, not_lt_of_ge ha.le, hab.ne, hab.ne'] <;>
        field_simp [Real.pi_ne_zero] <;> ring
    · have ha : a - x < 0 := sub_neg.mpr (hab.trans hbx)
      have hb : b - x < 0 := sub_neg.mpr hbx
      have hnot : ¬x < b := not_lt_of_ge hbx.le
      simp [arctanJump, endpointProfile, ha, hb, not_lt_of_ge ha.le,
        not_lt_of_ge hb.le, (hab.trans hbx).ne', hbx.ne', hnot]

theorem intervalWeight_tendsto {a b : ℝ} (hab : a < b) (x : ℝ) :
    Tendsto (fun ε : ℝ => intervalWeight a b ε x) (𝓝[>] 0)
      (𝓝 (endpointProfile a b x)) := by
  have h := ((tendsto_arctan_div (b - x)).sub (tendsto_arctan_div (a - x))).div_const Real.pi
  simpa only [intervalWeight, arctanJump_difference hab x] using h

theorem intervalWeight_nonneg_le_one {a b ε : ℝ} (hab : a ≤ b) (hε : 0 < ε) (x : ℝ) :
    0 ≤ intervalWeight a b ε x ∧ intervalWeight a b ε x ≤ 1 := by
  have hmono : Real.arctan ((a - x) / ε) ≤ Real.arctan ((b - x) / ε) :=
    Real.arctan_mono (div_le_div_of_nonneg_right (by linarith) hε.le)
  have hdiff : Real.arctan ((b - x) / ε) - Real.arctan ((a - x) / ε) ≤ Real.pi := by
    linarith [Real.arctan_lt_pi_div_two ((b - x) / ε),
      Real.neg_pi_div_two_lt_arctan ((a - x) / ε)]
  exact ⟨div_nonneg (sub_nonneg.mpr hmono) Real.pi_pos.le,
    (div_le_one Real.pi_pos).2 hdiff⟩

theorem intervalWeight_continuous (a b ε : ℝ) : Continuous (intervalWeight a b ε) := by
  unfold intervalWeight
  fun_prop

private theorem endpointProfile_integral (μ : Measure ℝ) [IsFiniteMeasure μ] (a b : ℝ) :
    (∫ x, endpointProfile a b x ∂μ) =
      μ.real (Ioo a b) + (μ.real {a} + μ.real {b}) / 2 := by
  have hI : Integrable ((Ioo a b).indicator (fun _ : ℝ => (1 : ℝ))) μ :=
    (integrable_const 1).indicator measurableSet_Ioo
  have ha : Integrable (({a} : Set ℝ).indicator (fun _ : ℝ => (1 / 2 : ℝ))) μ :=
    (integrable_const (1 / 2 : ℝ)).indicator (measurableSet_singleton a)
  have hb : Integrable (({b} : Set ℝ).indicator (fun _ : ℝ => (1 / 2 : ℝ))) μ :=
    (integrable_const (1 / 2 : ℝ)).indicator (measurableSet_singleton b)
  unfold endpointProfile
  rw [integral_add (hI.add ha) hb, integral_add hI ha,
    integral_indicator_const 1 measurableSet_Ioo,
    integral_indicator_const (1 / 2 : ℝ) (measurableSet_singleton a),
    integral_indicator_const (1 / 2 : ℝ) (measurableSet_singleton b)]
  simp only [smul_eq_mul]
  ring

/-- The scalar approximate-identity limit with the exact endpoint atoms. -/
theorem intervalWeight_integral_tendsto (μ : Measure ℝ) [IsFiniteMeasure μ]
    {a b : ℝ} (hab : a < b) :
    Tendsto (fun ε : ℝ => ∫ x, intervalWeight a b ε x ∂μ) (𝓝[>] 0)
      (𝓝 (μ.real (Ioo a b) + (μ.real {a} + μ.real {b}) / 2)) := by
  rw [← endpointProfile_integral μ a b]
  apply tendsto_integral_filter_of_dominated_convergence (fun _ : ℝ => (1 : ℝ))
  · exact Eventually.of_forall (fun ε => (intervalWeight_continuous a b ε).aestronglyMeasurable)
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact ae_of_all _ (fun x => by
      have h := intervalWeight_nonneg_le_one hab.le hε x
      simpa only [Real.norm_eq_abs, abs_of_nonneg h.1] using h.2)
  · exact integrable_const 1
  · exact ae_of_all _ (intervalWeight_tendsto hab)

private theorem kernel_den_pos {ε : ℝ} (hε : 0 < ε) (t x : ℝ) :
    0 < (x - t) ^ 2 + ε ^ 2 := by positivity

theorem poissonKernel_continuous {ε : ℝ} (hε : 0 < ε) :
    Continuous (fun p : ℝ × ℝ => poissonKernel ε p.2 p.1) := by
  unfold poissonKernel
  fun_prop (disch := positivity)

theorem poissonKernel_nonneg_bound {ε : ℝ} (hε : 0 < ε) (t x : ℝ) :
    0 ≤ poissonKernel ε t x ∧ poissonKernel ε t x ≤ 1 / (Real.pi * ε) := by
  have hd := kernel_den_pos hε t x
  have hratio : ε / ((x - t) ^ 2 + ε ^ 2) ≤ 1 / ε := by
    apply (div_le_div_iff₀ hd hε).2
    nlinarith [sq_nonneg (x - t)]
  constructor
  · exact div_nonneg hε.le (mul_nonneg Real.pi_pos.le hd.le)
  · calc
      poissonKernel ε t x = (1 / Real.pi) * (ε / ((x - t) ^ 2 + ε ^ 2)) := by
        dsimp only [poissonKernel]
        ring
      _ ≤ (1 / Real.pi) * (1 / ε) :=
        mul_le_mul_of_nonneg_left hratio (one_div_pos.mpr Real.pi_pos).le
      _ = 1 / (Real.pi * ε) := by ring

private theorem arctanPrimitive_hasDerivAt {ε : ℝ} (hε : 0 < ε) (x t : ℝ) :
    HasDerivAt (fun v : ℝ => Real.arctan ((v - x) / ε) / Real.pi)
      (poissonKernel ε t x) t := by
  have h := ((((hasDerivAt_id t).sub_const x).div_const ε).arctan).div_const Real.pi
  apply h.congr_deriv
  dsimp only [poissonKernel]
  have hden := (kernel_den_pos hε t x).ne'
  have hatan : 1 + ((t - x) / ε) ^ 2 ≠ 0 := by positivity
  field_simp [hε.ne', Real.pi_ne_zero, hden, hatan] <;> ring

/-- The interval Poisson kernel is evaluated by its actual arctan primitive. -/
theorem poissonKernel_intervalIntegral (a b : ℝ) {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    (∫ t in a..b, poissonKernel ε t x) = intervalWeight a b ε x := by
  have hc : Continuous (fun t : ℝ => poissonKernel ε t x) :=
    (poissonKernel_continuous hε).comp (continuous_const.prodMk continuous_id)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => arctanPrimitive_hasDerivAt hε x t) hc.intervalIntegrable
  exact h.trans (by dsimp only [intervalWeight]; ring)

private theorem poissonKernel_joint_integrable (μ : Measure ℝ) [IsFiniteMeasure μ]
    (a b : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun p : ℝ × ℝ => poissonKernel ε p.2 p.1)
      (μ.prod (volume.restrict (Ioc a b))) := by
  apply (integrable_const (1 / (Real.pi * ε))).mono'
    (poissonKernel_continuous hε).aestronglyMeasurable
  exact ae_of_all _ (fun p => by
    have h := poissonKernel_nonneg_bound hε p.2 p.1
    simpa only [Real.norm_eq_abs, abs_of_nonneg h.1] using h.2)

def poissonIntervalMass (μ : Measure ℝ) (a b ε : ℝ) : ℝ :=
  ∫ t in a..b, ∫ x, poissonKernel ε t x ∂μ

/-- Genuine finite-measure Fubini identifies the double integral with the
bounded arctan weight. -/
theorem poissonIntervalMass_eq_weight (μ : Measure ℝ) [IsFiniteMeasure μ]
    {a b ε : ℝ} (hab : a ≤ b) (hε : 0 < ε) :
    poissonIntervalMass μ a b ε = ∫ x, intervalWeight a b ε x ∂μ := by
  have h := integral_integral_swap (poissonKernel_joint_integrable μ a b hε)
  rw [poissonIntervalMass, intervalIntegral.integral_of_le hab]
  calc
    (∫ t in Ioc a b, ∫ x, poissonKernel ε t x ∂μ) =
        ∫ x, ∫ t in Ioc a b, poissonKernel ε t x ∂μ := h.symm
    _ = ∫ x, intervalWeight a b ε x ∂μ := by
      apply integral_congr_ae
      exact ae_of_all _ (fun x => by
        rw [← intervalIntegral.integral_of_le hab]
        exact poissonKernel_intervalIntegral a b hε x)

theorem poissonIntervalMass_tendsto (μ : Measure ℝ) [IsFiniteMeasure μ]
    {a b : ℝ} (hab : a < b) :
    Tendsto (poissonIntervalMass μ a b) (𝓝[>] 0)
      (𝓝 (μ.real (Ioo a b) + (μ.real {a} + μ.real {b}) / 2)) := by
  apply (intervalWeight_integral_tendsto μ hab).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (poissonIntervalMass_eq_weight μ hab.le hε).symm

theorem poissonIntervalMass_eq_scaled_inverse (μ : Measure ℝ) (a b ε : ℝ) :
    poissonIntervalMass μ a b ε = (ε / Real.pi) *
      ∫ t in a..b, ∫ x, 1 / ((x - t) ^ 2 + ε ^ 2) ∂μ := by
  have hk (t x : ℝ) : poissonKernel ε t x =
      (ε / Real.pi) * (1 / ((x - t) ^ 2 + ε ^ 2)) := by
    dsimp only [poissonKernel]
    ring
  unfold poissonIntervalMass
  simp_rw [hk, integral_const_mul]
  rw [intervalIntegral.integral_const_mul]

/-- Scalar Stieltjes/Poisson inversion, with no atom restriction and the
two endpoint half-masses retained. -/
theorem stieltjes_poisson_interval_inversion (μ : Measure ℝ) [IsFiniteMeasure μ]
    {a b : ℝ} (hab : a < b) :
    Tendsto (fun ε : ℝ => (ε / Real.pi) *
      ∫ t in a..b, ∫ x, 1 / ((x - t) ^ 2 + ε ^ 2) ∂μ) (𝓝[>] 0)
      (𝓝 (μ.real (Ioo a b) + (μ.real {a} + μ.real {b}) / 2)) := by
  apply (poissonIntervalMass_tendsto μ hab).congr'
  exact Eventually.of_forall (poissonIntervalMass_eq_scaled_inverse μ a b)

end
end ImbalancedChen.Part3.ScalarStieltjesPoissonInversion20261025a
