import ImbalancedChen.Part3GenericComplexCFCScalarMeasure
import ImbalancedChen.Part3GenericResolventUnboundedScalarMeasure
import ImbalancedChen.Part3ScalarCauchyResolventInversion
import Mathlib.Tactic

/-!
CODE_ONLY / SOURCEONLY / UNCOMPILED, 2026-10-25. No acceptance credit.

For an arbitrary injective positive self-adjoint contraction R, the actual
complex CFC graph resolvent is represented by the literal Cauchy transform
of the genuinely constructed lambda=1/t-1 scalar measure. The imported
generic zero-atom theorem removes the sole exceptional t=0 fiber.

The actual diagonal operator interval integral then satisfies scalar Stone
inversion, including half-atoms at the endpoints. No resolvent, measure,
no-atom, representation or inversion identity is supplied as a premise.
Identifying a concrete differential Green resolvent with this operator,
and any automorphic spectral normalization, remain separate obligations.
-/

namespace ImbalancedChen.Part3.GenericComplexResolventStone20261025a

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open GenericResolventScalarMeasure20261025a
open GenericResolventUnboundedScalarMeasure20261025a
open ComplexContractionResolvent20261025a
open GenericComplexCFCScalarMeasure20261025a
open ScalarCauchyResolventInversion20261025a

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem real_sub_nonreal_ne_zero {z : ℂ} (hz : z.im ≠ 0) (λ : ℝ) :
    (λ : ℂ) - z ≠ 0 := by
  intro hzero
  have h := congrArg Complex.im hzero
  simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, Complex.zero_im, neg_eq_zero] at h
  exact hz h

private theorem cauchyKernel_continuous {z : ℂ} (hz : z.im ≠ 0) :
    Continuous (fun λ : ℝ => ((λ : ℂ) - z)⁻¹) := by
  exact (Complex.continuous_ofReal.sub continuous_const).inv₀ (real_sub_nonreal_ne_zero hz)

private theorem cauchyKernel_norm_le {z : ℂ} (hz : z.im ≠ 0) (λ : ℝ) :
    ‖((λ : ℂ) - z)⁻¹‖ ≤ 1 / |z.im| := by
  have him : 0 < |z.im| := abs_pos.mpr hz
  have hnorm : |z.im| ≤ ‖(λ : ℂ) - z‖ := by
    have h := Complex.abs_im_le_norm ((λ : ℂ) - z)
    simpa only [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg] using h
  rw [norm_inv, one_div]
  exact (inv_le_inv₀ (lt_of_lt_of_le him hnorm) him).2 hnorm

private theorem cauchy_lambda_eq_ratio (R : H →L[ℂ] H)
    {z : ℂ} (hz : z.im ≠ 0) {t : ResolventSpectrum R} (ht : 0 < (t : ℝ)) :
    (((spectralLambda R t : ℝ) : ℂ) - z)⁻¹ =
      complexResolventRatio z ((t : ℝ) : ℂ) := by
  have htC : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hd := complexDenominator_real_ne_zero hz (t : ℝ)
  have hλ := real_sub_nonreal_ne_zero hz (spectralLambda R t)
  dsimp only [complexResolventRatio, complexDenominator] at hd ⊢
  dsimp only [spectralLambda] at hλ ⊢
  simp only [Complex.ofReal_sub, Complex.ofReal_inv, Complex.ofReal_one] at hλ ⊢
  field_simp [htC, hd, hλ] <;> ring

theorem unboundedScalarMeasure_cauchy_integrable (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R)
    (u : H) {z : ℂ} (hz : z.im ≠ 0) :
    Integrable (fun λ : ℝ => ((λ : ℂ) - z)⁻¹) (unboundedScalarMeasure R hSA u) := by
  exact (integrable_const (1 / |z.im|)).mono'
    (cauchyKernel_continuous hz).aestronglyMeasurable
    (ae_of_all _ (cauchyKernel_norm_le hz))

/-- The actual generic complex graph resolvent equals the Cauchy transform
of the actual lambda spectral measure in every diagonal coefficient. -/
theorem complexResolvent_scalarCoefficient_cauchy (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R)
    (hpos : 0 ≤ R) (hnorm : ‖R‖ ≤ 1) (hinj : Function.Injective R)
    (u : H) {z : ℂ} (hz : z.im ≠ 0) :
    inner ℂ u (complexResolvent R z u) =
      cauchyResolvent (unboundedScalarMeasure R hSA u) z := by
  have hm := (cauchyKernel_continuous hz).measurable
  rw [complexResolvent_scalarCoefficient R hSA u hz, cauchyResolvent,
    unboundedScalarMeasure,
    integral_map_of_stronglyMeasurable (measurable_spectralLambda R) hm.stronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [scalarMeasure_coordinate_pos_ae R hSA hpos hnorm hinj u] with t ht
  exact (cauchy_lambda_eq_ratio R hz ht).symm

def diagonalResolventIntervalMass (R : H →L[ℂ] H) (u : H) (a b ε : ℝ) : ℝ :=
  (1 / Real.pi) * ∫ t in a..b,
    (inner ℂ u (complexResolvent R ((t : ℂ) + (ε : ℂ) * Complex.I) u)).im

theorem diagonalResolventIntervalMass_eq_cauchy (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R)
    (hpos : 0 ≤ R) (hnorm : ‖R‖ ≤ 1) (hinj : Function.Injective R)
    (u : H) (a b : ℝ) {ε : ℝ} (hε : 0 < ε) :
    diagonalResolventIntervalMass R u a b ε =
      cauchyIntervalMass (unboundedScalarMeasure R hSA u) a b ε := by
  unfold diagonalResolventIntervalMass cauchyIntervalMass
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  have hz : ((t : ℂ) + (ε : ℂ) * Complex.I).im ≠ 0 := by
    simpa using hε.ne'
  rw [complexResolvent_scalarCoefficient_cauchy R hSA hpos hnorm hinj u hz]

/-- Actual generic diagonal Stone interval inversion, with half-atoms.
Every operator and measure in the conclusion is explicitly constructed. -/
theorem diagonalResolvent_Stone_interval (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R)
    (hpos : 0 ≤ R) (hnorm : ‖R‖ ≤ 1) (hinj : Function.Injective R)
    (u : H) {a b : ℝ} (hab : a < b) :
    Tendsto (diagonalResolventIntervalMass R u a b) (𝓝[>] 0)
      (𝓝 ((unboundedScalarMeasure R hSA u).real (Ioo a b) +
        ((unboundedScalarMeasure R hSA u).real {a} +
          (unboundedScalarMeasure R hSA u).real {b}) / 2)) := by
  apply (cauchyResolvent_interval_inversion (unboundedScalarMeasure R hSA u) hab).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (diagonalResolventIntervalMass_eq_cauchy R hSA hpos hnorm hinj u a b hε).symm

end
end ImbalancedChen.Part3.GenericComplexResolventStone20261025a
