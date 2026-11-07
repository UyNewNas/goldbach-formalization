import ImbalancedChen.Part3ActualResolventScalarMeasure
import Mathlib.MeasureTheory.Measure.Real

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The genuine scalar measures of the actual completed-energy resolvent satisfy
the parallelogram law and complex homogeneity. The proof compares their
continuous compactly supported integrals, expands the actual CFC matrix
coefficients, and invokes native uniqueness of finite regular measures.

Every Borel set therefore supplies a nonnegative bounded quadratic function
on the actual Hilbert space. The scale of a complex scalar is exactly
ENNReal.ofReal (norm squared), not the scalar or its real part.

No spectral projection operator, multiplicative projection law, orthogonal
resolution of identity, or automorphic spectral decomposition is asserted.
-/

namespace ImbalancedChen.Part3.ActualScalarMeasureQuadratic20261025a

noncomputable section
open MeasureTheory
open ImbalancedChen.Part3.MaassFiniteCoreL2Graph20261025a
open ImbalancedChen.Part3.ActualResolventScalarMeasure20261025a

/-- Parallelogram identity for the actual CFC quadratic coefficient.
No positivity estimate or spectral representation is used in this algebra. -/
theorem cfcCoefficient_parallelogram (u v : HyperbolicL2)
    (φ : C(ResolventSpectrum, ℝ)) :
    (inner ℂ (u + v) ((resolventCFC φ) (u + v))).re +
        (inner ℂ (u - v) ((resolventCFC φ) (u - v))).re =
      2 * (inner ℂ u ((resolventCFC φ) u)).re +
        2 * (inner ℂ v ((resolventCFC φ) v)).re := by
  simp only [map_add, map_sub, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right, Complex.add_re, Complex.sub_re]
  ring

/-- Conjugate linearity in the first slot supplies the norm-square scale. -/
theorem cfcCoefficient_smul (z : ℂ) (f : HyperbolicL2)
    (φ : C(ResolventSpectrum, ℝ)) :
    (inner ℂ (z • f) ((resolventCFC φ) (z • f))).re =
      ‖z‖ ^ 2 * (inner ℂ f ((resolventCFC φ) f)).re := by
  have hz : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    simpa only [Complex.normSq_eq_norm_sq] using
      (@Complex.normSq_eq_conj_mul_self z).symm
  rw [map_smul, inner_smul_left, inner_smul_right, ← mul_assoc, hz]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- Equality of the actual finite measures, with ENNReal scaling explicit. -/
theorem scalarMeasure_parallelogram (u v : HyperbolicL2) :
    scalarMeasure (u + v) + scalarMeasure (u - v) =
      (2 : ℝ≥0∞) • scalarMeasure u + (2 : ℝ≥0∞) • scalarMeasure v := by
  letI : IsFiniteMeasure ((2 : ℝ≥0∞) • scalarMeasure u) :=
    (scalarMeasure u).smul_finite (by norm_num)
  letI : IsFiniteMeasure ((2 : ℝ≥0∞) • scalarMeasure v) :=
    (scalarMeasure v).smul_finite (by norm_num)
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro φ
  rw [integral_add_measure (φ.integrable (μ := scalarMeasure (u + v)))
      (φ.integrable (μ := scalarMeasure (u - v))),
    integral_add_measure (φ.integrable (μ := (2 : ℝ≥0∞) • scalarMeasure u))
      (φ.integrable (μ := (2 : ℝ≥0∞) • scalarMeasure v)),
    integral_smul_measure, integral_smul_measure]
  rw [scalarMeasure_integral (u + v) φ.toContinuousMap,
    scalarMeasure_integral (u - v) φ.toContinuousMap,
    scalarMeasure_integral u φ.toContinuousMap,
    scalarMeasure_integral v φ.toContinuousMap]
  simpa only [ENNReal.toReal_ofNat, smul_eq_mul] using
    cfcCoefficient_parallelogram u v φ.toContinuousMap

/-- Complex homogeneity of the genuine measure, including the zero scalar. -/
theorem scalarMeasure_smul (z : ℂ) (f : HyperbolicL2) :
    scalarMeasure (z • f) = ENNReal.ofReal (‖z‖ ^ 2) • scalarMeasure f := by
  letI : IsFiniteMeasure (ENNReal.ofReal (‖z‖ ^ 2) • scalarMeasure f) :=
    (scalarMeasure f).smul_finite ENNReal.ofReal_ne_top
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro φ
  rw [integral_smul_measure,
    scalarMeasure_integral (z • f) φ.toContinuousMap,
    scalarMeasure_integral f φ.toContinuousMap,
    ENNReal.toReal_ofReal (sq_nonneg ‖z‖)]
  exact cfcCoefficient_smul z f φ.toContinuousMap

theorem scalarMeasure_zero : scalarMeasure (0 : HyperbolicL2) = 0 := by
  simpa using scalarMeasure_smul (0 : ℂ) (0 : HyperbolicL2)

/-- Pointwise ENNReal identity; no measurable-set premise is needed. -/
theorem scalarMeasure_smul_apply (z : ℂ) (f : HyperbolicL2)
    (B : Set ResolventSpectrum) :
    scalarMeasure (z • f) B = ENNReal.ofReal (‖z‖ ^ 2) * scalarMeasure f B := by
  rw [scalarMeasure_smul, Measure.smul_apply]
  rfl

/-- Pointwise parallelogram identity with the same actual scalar measures. -/
theorem scalarMeasure_parallelogram_apply (u v : HyperbolicL2)
    (B : Set ResolventSpectrum) :
    scalarMeasure (u + v) B + scalarMeasure (u - v) B =
      2 * scalarMeasure u B + 2 * scalarMeasure v B := by
  have h := congrArg (fun μ : Measure ResolventSpectrum => μ B)
    (scalarMeasure_parallelogram u v)
  simpa only [Measure.add_apply, Measure.smul_apply, smul_eq_mul] using h

/-- The actual real quadratic function associated to a spectral set. -/
def spectralQuadratic (B : Set ResolventSpectrum) (f : HyperbolicL2) : ℝ :=
  (scalarMeasure f).real B

theorem spectralQuadratic_nonneg (B : Set ResolventSpectrum) (f : HyperbolicL2) :
    0 ≤ spectralQuadratic B f := measureReal_nonneg

theorem spectralQuadratic_univ (f : HyperbolicL2) :
    spectralQuadratic Set.univ f = ‖f‖ ^ 2 := scalarMeasure_mass f

theorem spectralQuadratic_le_norm_sq (B : Set ResolventSpectrum) (f : HyperbolicL2) :
    spectralQuadratic B f ≤ ‖f‖ ^ 2 := by
  change (scalarMeasure f).real B ≤ _
  calc
    _ ≤ (scalarMeasure f).real Set.univ := measureReal_mono (Set.subset_univ B)
    _ = _ := scalarMeasure_mass f

theorem spectralQuadratic_smul (B : Set ResolventSpectrum) (z : ℂ) (f : HyperbolicL2) :
    spectralQuadratic B (z • f) = ‖z‖ ^ 2 * spectralQuadratic B f := by
  unfold spectralQuadratic
  rw [scalarMeasure_smul, measureReal_ennreal_smul_apply,
    ENNReal.toReal_ofReal (sq_nonneg ‖z‖)]

theorem spectralQuadratic_zero (B : Set ResolventSpectrum) :
    spectralQuadratic B 0 = 0 := by
  simp only [spectralQuadratic, scalarMeasure_zero, measureReal_zero_apply]

theorem spectralQuadratic_parallelogram (B : Set ResolventSpectrum)
    (u v : HyperbolicL2) :
    spectralQuadratic B (u + v) + spectralQuadratic B (u - v) =
      2 * spectralQuadratic B u + 2 * spectralQuadratic B v := by
  letI : IsFiniteMeasure ((2 : ℝ≥0∞) • scalarMeasure u) :=
    (scalarMeasure u).smul_finite (by norm_num)
  letI : IsFiniteMeasure ((2 : ℝ≥0∞) • scalarMeasure v) :=
    (scalarMeasure v).smul_finite (by norm_num)
  have h := congrArg (fun μ : Measure ResolventSpectrum => μ.real B)
    (scalarMeasure_parallelogram u v)
  simpa only [measureReal_add_apply, measureReal_ennreal_smul_apply,
    ENNReal.toReal_ofNat, spectralQuadratic] using h

theorem spectralQuadratic_mono {A B : Set ResolventSpectrum} (hAB : A ⊆ B)
    (f : HyperbolicL2) : spectralQuadratic A f ≤ spectralQuadratic B f :=
  measureReal_mono hAB

/-- Complementation splits the actual total mass exactly. This is a
quadratic identity, not a claim that operators multiply as projections. -/
theorem spectralQuadratic_add_compl (B : Set ResolventSpectrum)
    (hB : MeasurableSet B) (f : HyperbolicL2) :
    spectralQuadratic B f + spectralQuadratic Bᶜ f = ‖f‖ ^ 2 := by
  change (scalarMeasure f).real B + (scalarMeasure f).real Bᶜ = _
  rw [measureReal_add_measureReal_compl hB, scalarMeasure_mass]

end
end ImbalancedChen.Part3.ActualScalarMeasureQuadratic20261025a
