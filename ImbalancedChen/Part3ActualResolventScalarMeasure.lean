import ImbalancedChen.Part3ActualCompletedEnergyResolvent
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

The actual bounded energy resolvent has a genuine finite positive scalar
Borel measure for every actual vector. Real continuous functional calculus
constructs the positive functional, and the pinned real Riesz--Markov--Kakutani
theorem constructs its measure. The representation formula, total mass and
all nonnegative integral moments are proved. No spectral-measure premise is used.

This concerns the actual canonical completed-energy resolvent and does not
identify a Γ₀ automorphic spectral decomposition.
-/

namespace ImbalancedChen.Part3.ActualResolventScalarMeasure20261025a

noncomputable section

open MeasureTheory
open ImbalancedChen.Part3.MaassFiniteCoreL2Graph20261025a
open ImbalancedChen.Part3.ActualCompletedEnergyResolvent20261025a

abbrev ResolventAlgebra := HyperbolicL2 →L[ℂ] HyperbolicL2

abbrev ResolventSpectrum := {t : ℝ // t ∈ spectrum ℝ actualWeakResolvent}

/-- The actual real continuous functional calculus of the genuine
positive self-adjoint bounded energy resolvent. -/
def resolventCFC : C(ResolventSpectrum, ℝ) →⋆ₐ[ℝ] ResolventAlgebra :=
  cfcHom actualWeakResolvent_selfAdjoint

theorem resolventCFC_selfAdjoint (φ : C(ResolventSpectrum, ℝ)) :
    IsSelfAdjoint (resolventCFC φ) :=
  cfcHom_predicate actualWeakResolvent_selfAdjoint φ

theorem scalarCoefficient_im_zero (f : HyperbolicL2) (φ : C(ResolventSpectrum, ℝ)) :
    (inner ℂ f ((resolventCFC φ) f)).im = 0 :=
  (resolventCFC_selfAdjoint φ).isSymmetric.im_inner_self_apply f

theorem resolventSpectrum_subset_unitInterval :
    spectrum ℝ actualWeakResolvent ⊆ Set.Icc (0 : ℝ) 1 := by
  intro t ht
  have hnonneg : (0 : ResolventAlgebra) ≤ actualWeakResolvent :=
    (ContinuousLinearMap.nonneg_iff_isPositive actualWeakResolvent).mpr
      actualWeakResolvent_positive
  refine ⟨spectrum_nonneg_of_nonneg hnonneg ht, ?_⟩
  have hnorm : ‖t‖ ≤ ‖actualWeakResolvent‖ * ‖(1 : ResolventAlgebra)‖ :=
    spectrum.norm_le_norm_mul_of_mem ht
  have hone : ‖(1 : ResolventAlgebra)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hbound : ‖actualWeakResolvent‖ * ‖(1 : ResolventAlgebra)‖ ≤ 1 := by
    calc
      _ ≤ 1 * 1 := mul_le_mul actualWeakResolvent_opNorm_le_one hone
        (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  exact (Real.le_norm_self t).trans (hnorm.trans hbound)

theorem spectrum_coordinate_mem_unitInterval (t : ResolventSpectrum) :
    (t : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
  resolventSpectrum_subset_unitInterval t.property

/-- Every continuous real function on the actual compact spectrum is a
compactly supported continuous function, as required by the pinned RMK API. -/
def compactLift (φ : C(ResolventSpectrum, ℝ)) : C_c(ResolventSpectrum, ℝ) :=
  ⟨φ, HasCompactSupport.of_compactSpace φ⟩

/-- The actual vector positive functional. Positivity is proved through
the genuine Loewner order of actual Hilbert-space operators. -/
def scalarPositiveFunctional (f : HyperbolicL2) :
    C_c(ResolventSpectrum, ℝ) →ₚ[ℝ] ℝ where
  toFun φ := (inner ℂ f ((resolventCFC φ.toContinuousMap) f)).re
  map_add' φ ψ := by
    change (inner ℂ f ((resolventCFC (φ.toContinuousMap + ψ.toContinuousMap)) f)).re = _
    rw [map_add, ContinuousLinearMap.add_apply, inner_add_right, Complex.add_re]
  map_smul' c φ := by
    change (inner ℂ f ((resolventCFC (c • φ.toContinuousMap)) f)).re =
      c * (inner ℂ f ((resolventCFC φ.toContinuousMap) f)).re
    rw [map_smul, ContinuousLinearMap.smul_apply,
      RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_right]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  monotone' := by
    intro φ ψ hφψ
    have hle : resolventCFC φ.toContinuousMap ≤ resolventCFC ψ.toContinuousMap :=
      cfcHom_mono actualWeakResolvent_selfAdjoint hφψ
    have hpositive := (ContinuousLinearMap.le_def _ _).mp hle
    have hpair := hpositive.re_inner_nonneg_right f
    rw [ContinuousLinearMap.sub_apply, inner_sub_right, Complex.sub_re] at hpair
    exact sub_nonneg.mp hpair

theorem scalarPositiveFunctional_apply (f : HyperbolicL2) (φ : C_c(ResolventSpectrum, ℝ)) :
    scalarPositiveFunctional f φ =
      (inner ℂ f ((resolventCFC φ.toContinuousMap) f)).re := rfl

theorem scalarPositiveFunctional_one (f : HyperbolicL2) :
    scalarPositiveFunctional f (compactLift 1) = ‖f‖ ^ 2 := by
  change (inner ℂ f ((resolventCFC 1) f)).re = _
  rw [map_one]
  change (inner ℂ f f).re = ‖f‖ ^ 2
  rw [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow, Complex.ofReal_re]

/-- The genuine finite positive Borel measure on the actual real spectrum,
constructed by Riesz--Markov--Kakutani from the actual vector functional. -/
def scalarMeasure (f : HyperbolicL2) : Measure ResolventSpectrum :=
  RealRMK.rieszMeasure (scalarPositiveFunctional f)

instance scalarMeasure_finite (f : HyperbolicL2) : IsFiniteMeasure (scalarMeasure f) := by
  unfold scalarMeasure
  infer_instance

instance scalarMeasure_regular (f : HyperbolicL2) : (scalarMeasure f).Regular :=
  RealRMK.regular_rieszMeasure (scalarPositiveFunctional f)

/-- Exact integral representation for every continuous real function on
the actual spectrum, with no measure representation assumption. -/
theorem scalarMeasure_integral (f : HyperbolicL2) (φ : C(ResolventSpectrum, ℝ)) :
    (∫ t : ResolventSpectrum, φ t ∂scalarMeasure f) =
      (inner ℂ f ((resolventCFC φ) f)).re :=
  RealRMK.integral_rieszMeasure (scalarPositiveFunctional f) (compactLift φ)

/-- The same representation with the genuine complex matrix coefficient;
real CFC values have zero imaginary scalar coefficient. -/
theorem scalarMeasure_complex_integral (f : HyperbolicL2) (φ : C(ResolventSpectrum, ℝ)) :
    (∫ t : ResolventSpectrum, (φ t : ℂ) ∂scalarMeasure f) =
      inner ℂ f ((resolventCFC φ) f) := by
  rw [integral_complex_ofReal]
  apply Complex.ext
  · simpa only [Complex.ofReal_re] using scalarMeasure_integral f φ
  · simp only [Complex.ofReal_im, scalarCoefficient_im_zero]

theorem scalarMeasure_mass (f : HyperbolicL2) :
    (scalarMeasure f).real Set.univ = ‖f‖ ^ 2 := by
  have h : (∫ _t : ResolventSpectrum, (1 : ℝ) ∂scalarMeasure f) = ‖f‖ ^ 2 := by
    calc
      _ = scalarPositiveFunctional f (compactLift 1) :=
        RealRMK.integral_rieszMeasure (scalarPositiveFunctional f) (compactLift 1)
      _ = _ := scalarPositiveFunctional_one f
  simpa [Measure.real] using h

theorem scalarMeasure_univ (f : HyperbolicL2) :
    scalarMeasure f Set.univ = ENNReal.ofReal (‖f‖ ^ 2) := by
  have hm := scalarMeasure_mass f
  change (scalarMeasure f Set.univ).toReal = ‖f‖ ^ 2 at hm
  rw [← hm]
  exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm

def spectrumCoordinate : C(ResolventSpectrum, ℝ) :=
  (ContinuousMap.id ℝ).restrict (spectrum ℝ actualWeakResolvent)

theorem resolventCFC_coordinate : resolventCFC spectrumCoordinate = actualWeakResolvent :=
  cfcHom_id actualWeakResolvent_selfAdjoint

/-- Every nonnegative integral moment is the actual resolvent power
matrix coefficient. -/
theorem scalarMeasure_moment (f : HyperbolicL2) (n : ℕ) :
    (∫ t : ResolventSpectrum, (t : ℝ) ^ n ∂scalarMeasure f) =
      (inner ℂ f ((actualWeakResolvent ^ n) f)).re := by
  have h := scalarMeasure_integral f (spectrumCoordinate ^ n)
  rw [map_pow, resolventCFC_coordinate] at h
  simpa [spectrumCoordinate] using h

/-- Survival moments for the genuine positive contraction; this identity
does not assume a spectral measure or a strong-limit statement. -/
theorem scalarMeasure_survival_moment (f : HyperbolicL2) (n : ℕ) :
    (∫ t : ResolventSpectrum, (1 - (t : ℝ)) ^ n ∂scalarMeasure f) =
      (inner ℂ f (((1 - actualWeakResolvent) ^ n) f)).re := by
  have h := scalarMeasure_integral f ((1 - spectrumCoordinate) ^ n)
  rw [map_pow, map_sub, map_one, resolventCFC_coordinate] at h
  simpa [spectrumCoordinate] using h

end

end ImbalancedChen.Part3.ActualResolventScalarMeasure20261025a
