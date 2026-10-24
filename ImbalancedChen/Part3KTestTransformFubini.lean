import ImbalancedChen.Part3ActualCommonHeightKFactorizationFullGram
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

/-!
SOURCEONLY / UNCOMPILED, 2026-10-24.  This is the Fubini step for the
literal packet's K transform.  The physical q support and the already
proved positive-axis K integrand majorant supply product integrability.
No integrability or Fubini assertion about this product is a premise.
-/

namespace ImbalancedChen.Part3.ActualKTransformFubiniSourceOnly
noncomputable section

open Classical Set MeasureTheory
open P3ActualLiteralPacketIntegralSourceOnly
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralTest spectralMode)
open ImaginaryOrderKBesselSourceOnly
open ActualCommonHeightKGramSourceOnly (kTestTransform)

variable {ι : Type*}

/-- A continuous realization of the actual `spectralTest(q)/q`: the cutoff
is invisible on the physical q interval and the numerator is zero outside. -/
private def qWeight (P : PacketData ι) (k : D4 → ℤ) (q : ℝ) : ℂ :=
  spectralTest k P.Y0 q / ((max q (P.Y0 / 32) : ℝ) : ℂ)

private lemma qWeight_continuous (P : PacketData ι) (k : D4 → ℤ) :
    Continuous (qWeight P k) := by
  have hs : Continuous (spectralTest k P.Y0) :=
    (P3Period64NativeReconstructionSourceOnly.spectralTest_contDiff k P.Y0).continuous
  have hm : Continuous (fun q : ℝ => max q (P.Y0 / 32)) :=
    continuous_id.max continuous_const
  have hz : ∀ q : ℝ, ((max q (P.Y0 / 32) : ℝ) : ℂ) ≠ 0 := by
    intro q
    apply Complex.ofReal_ne_zero.mpr
    have hY := P.Y0_pos
    have hq : 0 < max q (P.Y0 / 32) :=
      lt_of_lt_of_le (by positivity : 0 < P.Y0 / 32) (le_max_right q _)
    exact hq.ne'
  exact hs.div (Complex.continuous_ofReal.comp hm) hz

private lemma qWeight_zero_off_region (P : PacketData ι) (k : D4 → ℤ)
    {q : ℝ} (hq : q ∉ P.region) : qWeight P k q = 0 := by
  simp only [qWeight, spectralTest, spectralMode,
    P.chi_scaled_zero_off q hq, Complex.ofReal_zero, zero_mul, zero_div]

private lemma qWeight_eq_actual (P : PacketData ι) (k : D4 → ℤ) (q : ℝ) :
    qWeight P k q = spectralTest k P.Y0 q / (q : ℂ) := by
  by_cases hq : q ∈ P.region
  · have hqlo : P.Y0 / 16 ≤ q := hq.1
    have hmax : max q (P.Y0 / 32) = q :=
      max_eq_left (by linarith [P.Y0_pos] : P.Y0 / 32 ≤ q)
    simp only [qWeight, hmax]
  · rw [qWeight_zero_off_region P k hq]
    have hs : spectralTest k P.Y0 q = 0 := by
      simp only [spectralTest, spectralMode, P.chi_scaled_zero_off q hq,
        Complex.ofReal_zero, zero_mul]
    simp [hs]

private lemma qWeight_integrable (P : PacketData ι) (k : D4 → ℤ) :
    Integrable (qWeight P k) := by
  apply (qWeight_continuous P k).integrable_of_hasCompactSupport
  apply (isCompact_Icc : IsCompact P.region).of_isClosed_subset isClosed_closure
  apply closure_minimal _ (isClosed_Icc : IsClosed P.region)
  intro q hq
  by_contra hn
  exact hq (qWeight_zero_off_region P k hn)

/-- The product is measured with Lebesgue dq and Lebesgue du restricted to
`u>0`.  On the support of `qWeight`, `q ≥ Y0/16`, giving the uniform
`exp (-(Y0/32)u)` majorant. -/
private def doubleIntegrand (P : PacketData ι) (k : D4 → ℤ)
    (t : ℝ) (p : ℝ × ℝ) : ℂ :=
  qWeight P k p.1 * (kIntegrand t p.1 p.2 : ℂ)

private lemma doubleIntegrand_norm_le (P : PacketData ι)
    (k : D4 → ℤ) (t q u : ℝ) :
    ‖doubleIntegrand P k t (q, u)‖ ≤
      ‖qWeight P k q‖ * Real.exp (-(P.Y0 / 32) * u) := by
  by_cases hq : q ∈ P.region
  · have hqlo : P.Y0 / 16 ≤ q := hq.1
    have ha : 0 < P.Y0 / 16 := by
      have h := P.Y0_pos
      positivity
    have hk := kIntegrand_norm_le ha hqlo t u
    change ‖qWeight P k q * (kIntegrand t q u : ℂ)‖ ≤ _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left
      (by simpa only [Real.norm_eq_abs,
        show -(P.Y0 / 16 / 2) = -(P.Y0 / 32) by ring] using hk) (norm_nonneg _)
  · simp only [doubleIntegrand, qWeight_zero_off_region P k hq,
      zero_mul, norm_zero, le_refl]

/-- Actual absolute integrability on the q/u product.  The proof uses a
product of two independently established L¹ functions, not a Fubini
hypothesis. -/
theorem doubleIntegrand_integrable (P : PacketData ι)
    (k : D4 → ℤ) (t : ℝ) :
    Integrable (doubleIntegrand P k t)
      (volume.prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hq : Integrable (fun q : ℝ => ‖qWeight P k q‖) :=
    (qWeight_integrable P k).norm
  have hu : Integrable (fun u : ℝ => Real.exp (-(P.Y0 / 32) * u))
      (volume.restrict (Ioi (0 : ℝ))) := by
    have ha : 0 < P.Y0 / 16 := by
      have h := P.Y0_pos
      positivity
    have h := exponential_majorant_integrable (a := P.Y0 / 16) ha
    simpa only [show -(P.Y0 / 16 / 2) = -(P.Y0 / 32) by ring] using h
  have hmaj : Integrable
      (fun p : ℝ × ℝ => ‖qWeight P k p.1‖ *
        Real.exp (-(P.Y0 / 32) * p.2))
      (volume.prod (volume.restrict (Ioi (0 : ℝ)))) :=
    hq.mul_prod hu
  have hc : Continuous (doubleIntegrand P k t) := by
    have hw : Continuous (fun p : ℝ × ℝ => qWeight P k p.1) :=
      (qWeight_continuous P k).comp continuous_fst
    have hk : Continuous (fun p : ℝ × ℝ => (kIntegrand t p.1 p.2 : ℂ)) := by
      unfold kIntegrand
      fun_prop
    exact hw.mul hk
  exact hmaj.mono' hc.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun p => doubleIntegrand_norm_le P k t p.1 p.2))

/-- Integrability stated directly for the requested literal quotient and
literal cosine-Laplace integrand, including q outside the physical interval. -/
theorem literal_doubleIntegrand_integrable (P : PacketData ι)
    (k : D4 → ℤ) (t : ℝ) :
    Integrable (fun p : ℝ × ℝ =>
      (spectralTest k P.Y0 p.1 / (p.1 : ℂ)) *
        ((Real.exp (-p.1 * Real.cosh p.2) * Real.cos (2*t*p.2) : ℝ) : ℂ))
      (volume.prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have he : (fun p : ℝ × ℝ =>
      (spectralTest k P.Y0 p.1 / (p.1 : ℂ)) *
        ((Real.exp (-p.1 * Real.cosh p.2) * Real.cos (2*t*p.2) : ℝ) : ℂ)) =
      doubleIntegrand P k t := by
    funext p
    simp only [doubleIntegrand, qWeight_eq_actual, kIntegrand]
  rw [he]
  exact doubleIntegrand_integrable P k t

/-- The original, unrestricted q integral is exactly the positive-u
cosine-Laplace integral.  Thus the exchange of q and u is justified for
the literal K transform and its literal `dq/q` normalization. -/
theorem kTestTransform_cosineLaplace (P : PacketData ι)
    (k : D4 → ℤ) (t : ℝ) :
    kTestTransform P k t =
      ∫ u in Ioi (0 : ℝ), ∫ q : ℝ,
        qWeight P k q * (kIntegrand t q u : ℂ) := by
  have hf := doubleIntegrand_integrable P k t
  have hinner (q : ℝ) :
      (∫ u in Ioi (0 : ℝ), doubleIntegrand P k t (q, u)) =
        qWeight P k q * (imaginaryOrderK t q : ℂ) := by
    simp only [doubleIntegrand, integral_const_mul, integral_complex_ofReal,
      imaginaryOrderK]
  have hrewrite (q : ℝ) :
      qWeight P k q * (imaginaryOrderK t q : ℂ) =
        spectralTest k P.Y0 q * ((imaginaryOrderK t q : ℂ) / (q : ℂ)) := by
    rw [qWeight_eq_actual]
    ring
  calc
    kTestTransform P k t =
        ∫ q : ℝ, ∫ u in Ioi (0 : ℝ), doubleIntegrand P k t (q, u) := by
      simp only [hinner, hrewrite, kTestTransform]
    _ = ∫ p : ℝ × ℝ, doubleIntegrand P k t p
          ∂(volume.prod (volume.restrict (Ioi (0 : ℝ)))) :=
      (integral_prod _ hf).symm
    _ = ∫ u in Ioi (0 : ℝ), ∫ q : ℝ,
          qWeight P k q * (kIntegrand t q u : ℂ) := by
      simpa only [doubleIntegrand] using integral_prod_symm _ hf

/-- Public literal formula with the original `spectralTest`, q denominator,
and `exp(-q cosh u) cos(2tu)` displayed without the continuous cutoff. -/
theorem kTestTransform_cosineLaplace_literal (P : PacketData ι)
    (k : D4 → ℤ) (t : ℝ) :
    kTestTransform P k t =
      ∫ u in Ioi (0 : ℝ), ∫ q : ℝ,
        (spectralTest k P.Y0 q / (q : ℂ)) *
          ((Real.exp (-q * Real.cosh u) * Real.cos (2*t*u) : ℝ) : ℂ) := by
  simpa only [qWeight_eq_actual, kIntegrand] using
    kTestTransform_cosineLaplace P k t

end
end ImbalancedChen.Part3.ActualKTransformFubiniSourceOnly
