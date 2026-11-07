import ImbalancedChen.P4BSmoothPrimeVariableProfile
import ImbalancedChen.P4BSmoothProfileDirectionalDerivativeBudget
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Measurability, integration, and positive-band Lipschitz control of the actual prime profile

SOURCE ONLY / UNCOMPILED / ZERO PROOF CREDIT (2026-10-25).

The varying prime coordinates are real variables throughout. The actual
normalized-log pullback is measurable even at the totalized logarithm's
zero coordinates. Its proved [0,1] bound gives integrability on every set
of finite measure. On positive compact prime boxes the actual harmonic
factor is continuous and hence integrable with the profile.

The quantitative result uses the scalar logarithm's genuine derivative,
then the physical profile's proved Lipschitz budget. On p_i >= a > 0,
one constant works for all N >= 2 and T. The inverse log N of the pullback
pays the physical upper wall's log N. No PP or spectral input is assumed.
-/

namespace ImbalancedChen.P0VariableProfileLipschitzIntegration

noncomputable section

open Set MeasureTheory
open scoped BigOperators
open ImbalancedChen.P4B
open ImbalancedChen.P4BSmoothProfileCommonCompactSupport

/-- The actual coordinate logarithms are globally measurable, including
zero coordinates where the real logarithm is totalized. -/
theorem measurable_primeVariableLogPoint (N : ℕ) :
    Measurable (primeVariableLogPoint N) := by
  apply measurable_pi_lambda
  intro i
  exact (measurable_pi_apply i).log.div_const (Real.log (N : ℝ))

/-- Global measurability of the defined genuine prime-variable weight. -/
theorem measurable_smoothPrimeVariableProfile (b : ℝ) (N : ℕ) (T width : ℝ) :
    Measurable (smoothPrimeVariableProfile b N T width) := by
  change Measurable (smoothPhysicalProfile b N T width ∘ primeVariableLogPoint N)
  exact (contDiff_smoothPhysicalProfile (n := 0) b N T width).continuous.measurable.comp
    (measurable_primeVariableLogPoint N)

/-- Every finite-measure region admits the actual prime-variable integral.
No positive-domain or width restriction is needed for this bounded fact. -/
theorem integrableOn_smoothPrimeVariableProfile_of_measure_ne_top
    (b : ℝ) (N : ℕ) (T width : ℝ)
    (μ : Measure (Fin 2 → ℝ)) (s : Set (Fin 2 → ℝ)) (hs : μ s ≠ ∞) :
    IntegrableOn (smoothPrimeVariableProfile b N T width) s μ := by
  have hconst : IntegrableOn (fun _ : Fin 2 → ℝ => (1 : ℝ)) s μ :=
    integrableOn_const hs
  apply hconst.mono'
    (measurable_smoothPrimeVariableProfile b N T width).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun p => by
    change ‖smoothPhysicalProfile b N T width (primeVariableLogPoint N p)‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg
      (smoothPhysicalProfile_bounds b N T width (primeVariableLogPoint N p)).1]
    exact (smoothPhysicalProfile_bounds b N T width (primeVariableLogPoint N p)).2)

/-- In particular every finite real prime box has an integral for any
locally finite measure. The box may meet the coordinate axes. -/
theorem integrableOn_smoothPrimeVariableProfile_Icc
    (b : ℝ) (N : ℕ) (T width : ℝ) (lo hi : Fin 2 → ℝ)
    (μ : Measure (Fin 2 → ℝ)) [IsLocallyFiniteMeasure μ] :
    IntegrableOn (smoothPrimeVariableProfile b N T width) (Icc lo hi) μ := by
  exact integrableOn_smoothPrimeVariableProfile_of_measure_ne_top b N T width μ
    (Icc lo hi) (isCompact_Icc : IsCompact (Icc lo hi)).measure_ne_top

/-- The exact prime-harmonic integrand is integrable on every positive
compact box. This is the actual varying-log weight times its harmonic
density, not a sampled or constant profile. -/
theorem integrableOn_smoothPrimeVariableProfile_harmonic_Icc
    (b : ℝ) (N : ℕ) (T width a u : ℝ) (ha : 0 < a)
    (μ : Measure (Fin 2 → ℝ)) [IsLocallyFiniteMeasure μ] :
    IntegrableOn (fun p : Fin 2 → ℝ =>
      smoothPrimeVariableProfile b N T width p * ∏ i : Fin 2, 1 / p i)
      (Icc (fun _ => a) (fun _ => u)) μ := by
  let S : Set (Fin 2 → ℝ) := Icc (fun _ => a) (fun _ => u)
  have hpositive : ∀ p ∈ S, ∀ i : Fin 2, 0 < p i := by
    intro p hp i
    exact ha.trans_le (hp.1 i)
  have hprofile : ContinuousOn (smoothPrimeVariableProfile b N T width) S :=
    (contDiffOn_smoothPrimeVariableProfile (n := 0) b N T width).continuousOn.mono
      (fun p hp => hpositive p hp)
  have hcoord (i : Fin 2) : ContinuousOn (fun p : Fin 2 → ℝ => 1 / p i) S :=
    continuousOn_const.div
      (continuous_apply i : Continuous (fun p : Fin 2 → ℝ => p i)).continuousOn
      (fun p hp => (hpositive p hp i).ne')
  have hharmonic : ContinuousOn (fun p : Fin 2 → ℝ => ∏ i : Fin 2, 1 / p i) S := by
    simpa only [Fin.prod_univ_two] using (hcoord 0).mul (hcoord 1)
  exact (hprofile.mul hharmonic).integrableOn_compact
    (isCompact_Icc : IsCompact S)

/-- Real logarithms on the same positive lower band have the genuine
inverse-band Lipschitz constant, from the derivative 1/x. -/
theorem abs_log_sub_log_le_lower_inverse
    {a p q : ℝ} (ha : 0 < a) (hp : a ≤ p) (hq : a ≤ q) :
    |Real.log p - Real.log q| ≤ a⁻¹ * |p - q| := by
  have hd : ∀ x ∈ Ici a, DifferentiableAt ℝ Real.log x := by
    intro x hx
    exact (Real.hasDerivAt_log (ha.trans_le hx).ne').differentiableAt
  have hb : ∀ x ∈ Ici a, ‖deriv Real.log x‖ ≤ a⁻¹ := by
    intro x hx
    rw [Real.deriv_log, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (ha.trans_le hx))]
    exact inv_anti₀ ha hx
  have h := (convex_Ici a).norm_image_sub_le_of_norm_deriv_le hd hb hq hp
  simpa only [Real.norm_eq_abs] using h

/-- The actual normalized-log map has one exact N-dependent Lipschitz
bound in the original Pi sup norm, simultaneously in both coordinates. -/
theorem norm_primeVariableLogPoint_sub_le
    {a : ℝ} (ha : 0 < a) (N : ℕ) (hN : 2 ≤ N)
    (p q : Fin 2 → ℝ) (hp : ∀ i, a ≤ p i) (hq : ∀ i, a ≤ q i) :
    ‖primeVariableLogPoint N p - primeVariableLogPoint N q‖ ≤
      (a⁻¹ / Real.log (N : ℝ)) * ‖p - q‖ := by
  have hN1 : (1 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 1 < N by omega)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hscale : 0 ≤ a⁻¹ / Real.log (N : ℝ) :=
    div_nonneg (inv_nonneg.mpr ha.le) hlog.le
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hscale (norm_nonneg (p - q)))).mpr
  intro i
  change ‖Real.log (p i) / Real.log (N : ℝ) -
    Real.log (q i) / Real.log (N : ℝ)‖ ≤ _
  rw [Real.norm_eq_abs, ← sub_div, abs_div, abs_of_pos hlog]
  calc
    |Real.log (p i) - Real.log (q i)| / Real.log (N : ℝ) ≤
        (a⁻¹ * |p i - q i|) / Real.log (N : ℝ) :=
      div_le_div_of_nonneg_right (abs_log_sub_log_le_lower_inverse ha (hp i) (hq i))
        hlog.le
    _ ≤ (a⁻¹ * ‖p - q‖) / Real.log (N : ℝ) := by
      apply div_le_div_of_nonneg_right _ hlog.le
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr ha.le)
      simpa only [Real.norm_eq_abs, Pi.sub_apply] using norm_le_pi_norm (p - q) i
    _ = (a⁻¹ / Real.log (N : ℝ)) * ‖p - q‖ := by ring

/-- One genuine scalar constant controls every actual varying-prime
profile on p_i >= a > 0, uniformly in N >= 2 and cutoff T. The normalized
logarithm exactly absorbs the physical upper wall's log N factor. -/
theorem exists_uniform_smoothPrimeVariableProfile_lower_band_Lipschitz_budget :
    ∃ C1 : ℝ, 1 ≤ C1 ∧ ∀ b width a : ℝ, 0 < width → 0 < a →
      ∀ N : ℕ, 2 ≤ N → ∀ T : ℝ, ∀ p q : Fin 2 → ℝ,
      (∀ i, a ≤ p i) → (∀ i, a ≤ q i) →
        |smoothPrimeVariableProfile b N T width p -
          smoothPrimeVariableProfile b N T width q| ≤
          ((4 * C1 * (2 + |b|) / width) * a⁻¹ * (1 + 1 / Real.log 2)) * ‖p - q‖ := by
  obtain ⟨C1, hC1, hphysical⟩ := exists_smoothPhysicalProfile_Lipschitz_budget
  refine ⟨C1, hC1, ?_⟩
  intro b width a hwidth ha N hN T p q hp hq
  have hN1 : (1 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 1 < N by omega)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hrecip : 1 / Real.log (N : ℝ) ≤ 1 / Real.log 2 :=
    width_div_log_nat_le_log_two zero_le_one hN
  have hratio : (1 + Real.log (N : ℝ)) / Real.log (N : ℝ) ≤
      1 + 1 / Real.log 2 := by
    calc
      _ = 1 + 1 / Real.log (N : ℝ) := by field_simp [hlog.ne']; ring
      _ ≤ 1 + 1 / Real.log 2 := add_le_add_left hrecip 1
  have hC10 : 0 ≤ C1 := zero_le_one.trans hC1
  have hK : 0 ≤ 4 * C1 * (2 + |b|) / width :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC10) (by positivity)) hwidth.le
  have hphysicalScale : 0 ≤
      (4 * C1 * (2 + |b|) / width) * (1 + Real.log (N : ℝ)) :=
    mul_nonneg hK (by linarith)
  change |smoothPhysicalProfile b N T width (primeVariableLogPoint N p) -
    smoothPhysicalProfile b N T width (primeVariableLogPoint N q)| ≤ _
  calc
    _ ≤ ((4 * C1 * (2 + |b|) / width) * (1 + Real.log (N : ℝ))) *
        ‖primeVariableLogPoint N p - primeVariableLogPoint N q‖ :=
      hphysical b width hwidth N hN T _ _
    _ ≤ ((4 * C1 * (2 + |b|) / width) * (1 + Real.log (N : ℝ))) *
        ((a⁻¹ / Real.log (N : ℝ)) * ‖p - q‖) :=
      mul_le_mul_of_nonneg_left (norm_primeVariableLogPoint_sub_le ha N hN p q hp hq)
        hphysicalScale
    _ = ((4 * C1 * (2 + |b|) / width) * a⁻¹ *
        ((1 + Real.log (N : ℝ)) / Real.log (N : ℝ))) * ‖p - q‖ := by ring
    _ ≤ ((4 * C1 * (2 + |b|) / width) * a⁻¹ *
        (1 + 1 / Real.log 2)) * ‖p - q‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hratio (mul_nonneg hK (inv_nonneg.mpr ha.le)))
        (norm_nonneg (p - q))

end

end ImbalancedChen.P0VariableProfileLipschitzIntegration