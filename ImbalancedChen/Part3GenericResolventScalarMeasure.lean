import ImbalancedChen.Part3PositiveContractionResolventCalculus
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

Scalar spectral measures on an arbitrary complex Hilbert space. For every
genuine bounded self-adjoint operator R and vector f, real CFC and the
pinned RMK theorem construct the actual finite regular positive measure,
with exact representation, mass and moments. Positivity and the norm bound
of R are used only for the separate real-spectrum containment in [0,1].
No concrete whole-plane space, automorphic realization or assumed spectral
measure occurs in the definitions or proofs.
-/

namespace ImbalancedChen.Part3.GenericResolventScalarMeasure20261025a

noncomputable section

open MeasureTheory
open ImbalancedChen.Part3.PositiveContractionResolventCalculus20261025a

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

abbrev ResolventSpectrum (R : H →L[ℂ] H) := {t : ℝ // t ∈ spectrum ℝ R}

variable (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R)

def resolventCFC : C(ResolventSpectrum R, ℝ) →⋆ₐ[ℝ] (H →L[ℂ] H) := cfcHom hSA

theorem resolventCFC_selfAdjoint (φ : C(ResolventSpectrum R, ℝ)) :
    IsSelfAdjoint (resolventCFC R hSA φ) := cfcHom_predicate hSA φ

theorem scalarCoefficient_im_zero (f : H) (φ : C(ResolventSpectrum R, ℝ)) :
    (inner ℂ f ((resolventCFC R hSA φ) f)).im = 0 :=
  (resolventCFC_selfAdjoint R hSA φ).isSymmetric.im_inner_self_apply f

theorem resolventSpectrum_subset_unitInterval (hpos : 0 ≤ R) (hnorm : ‖R‖ ≤ 1) :
    spectrum ℝ R ⊆ Set.Icc (0 : ℝ) 1 :=
  fun _ ht => spectrum_mem_unitInterval R hpos hnorm ht

theorem spectrum_coordinate_mem_unitInterval (hpos : 0 ≤ R) (hnorm : ‖R‖ ≤ 1)
    (t : ResolventSpectrum R) : (t : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
  spectrum_mem_unitInterval R hpos hnorm t.property

def compactLift (φ : C(ResolventSpectrum R, ℝ)) : C_c(ResolventSpectrum R, ℝ) :=
  ⟨φ, HasCompactSupport.of_compactSpace φ⟩

/-- The genuinely constructed positive vector functional for arbitrary R,f. -/
def scalarPositiveFunctional (f : H) : C_c(ResolventSpectrum R, ℝ) →ₚ[ℝ] ℝ where
  toFun φ := (inner ℂ f ((resolventCFC R hSA φ.toContinuousMap) f)).re
  map_add' φ ψ := by
    change (inner ℂ f ((resolventCFC R hSA
      (φ.toContinuousMap + ψ.toContinuousMap)) f)).re = _
    rw [map_add, ContinuousLinearMap.add_apply, inner_add_right, Complex.add_re]
  map_smul' c φ := by
    change (inner ℂ f ((resolventCFC R hSA (c • φ.toContinuousMap)) f)).re =
      c * (inner ℂ f ((resolventCFC R hSA φ.toContinuousMap) f)).re
    rw [map_smul, ContinuousLinearMap.smul_apply,
      RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_right]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  monotone' := by
    intro φ ψ hφψ
    have hle : resolventCFC R hSA φ.toContinuousMap ≤ resolventCFC R hSA ψ.toContinuousMap :=
      cfcHom_mono hSA hφψ
    have hpositive := (ContinuousLinearMap.le_def _ _).mp hle
    have hpair := hpositive.re_inner_nonneg_right f
    rw [ContinuousLinearMap.sub_apply, inner_sub_right, Complex.sub_re] at hpair
    exact sub_nonneg.mp hpair

theorem scalarPositiveFunctional_apply (f : H) (φ : C_c(ResolventSpectrum R, ℝ)) :
    scalarPositiveFunctional R hSA f φ =
      (inner ℂ f ((resolventCFC R hSA φ.toContinuousMap) f)).re := rfl

theorem scalarPositiveFunctional_one (f : H) :
    scalarPositiveFunctional R hSA f (compactLift R 1) = ‖f‖ ^ 2 := by
  change (inner ℂ f ((resolventCFC R hSA 1) f)).re = _
  rw [map_one]
  change (inner ℂ f f).re = ‖f‖ ^ 2
  rw [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow, Complex.ofReal_re]

/-- Actual RMK measure for arbitrary bounded self-adjoint R and actual f. -/
def scalarMeasure (f : H) : Measure (ResolventSpectrum R) :=
  RealRMK.rieszMeasure (scalarPositiveFunctional R hSA f)

instance scalarMeasure_finite (f : H) : IsFiniteMeasure (scalarMeasure R hSA f) := by
  unfold scalarMeasure
  infer_instance

instance scalarMeasure_regular (f : H) : (scalarMeasure R hSA f).Regular :=
  RealRMK.regular_rieszMeasure (scalarPositiveFunctional R hSA f)

theorem scalarMeasure_integral (f : H) (φ : C(ResolventSpectrum R, ℝ)) :
    (∫ t : ResolventSpectrum R, φ t ∂scalarMeasure R hSA f) =
      (inner ℂ f ((resolventCFC R hSA φ) f)).re :=
  RealRMK.integral_rieszMeasure (scalarPositiveFunctional R hSA f) (compactLift R φ)

theorem scalarMeasure_complex_integral (f : H) (φ : C(ResolventSpectrum R, ℝ)) :
    (∫ t : ResolventSpectrum R, (φ t : ℂ) ∂scalarMeasure R hSA f) =
      inner ℂ f ((resolventCFC R hSA φ) f) := by
  rw [integral_complex_ofReal]
  apply Complex.ext
  · simpa only [Complex.ofReal_re] using scalarMeasure_integral R hSA f φ
  · simp only [Complex.ofReal_im, scalarCoefficient_im_zero]

theorem scalarMeasure_mass (f : H) :
    (scalarMeasure R hSA f).real Set.univ = ‖f‖ ^ 2 := by
  have h : (∫ _t : ResolventSpectrum R, (1 : ℝ) ∂scalarMeasure R hSA f) = ‖f‖ ^ 2 := by
    calc
      _ = scalarPositiveFunctional R hSA f (compactLift R 1) :=
        RealRMK.integral_rieszMeasure (scalarPositiveFunctional R hSA f) (compactLift R 1)
      _ = _ := scalarPositiveFunctional_one R hSA f
  simpa [Measure.real] using h

theorem scalarMeasure_univ (f : H) :
    scalarMeasure R hSA f Set.univ = ENNReal.ofReal (‖f‖ ^ 2) := by
  have hm := scalarMeasure_mass R hSA f
  change (scalarMeasure R hSA f Set.univ).toReal = ‖f‖ ^ 2 at hm
  rw [← hm]
  exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm

def spectrumCoordinate : C(ResolventSpectrum R, ℝ) :=
  (ContinuousMap.id ℝ).restrict (spectrum ℝ R)

theorem resolventCFC_coordinate : resolventCFC R hSA (spectrumCoordinate R) = R := cfcHom_id hSA

theorem scalarMeasure_moment (f : H) (n : ℕ) :
    (∫ t : ResolventSpectrum R, (t : ℝ) ^ n ∂scalarMeasure R hSA f) =
      (inner ℂ f ((R ^ n) f)).re := by
  have h := scalarMeasure_integral R hSA f (spectrumCoordinate R ^ n)
  rw [map_pow, resolventCFC_coordinate] at h
  simpa [spectrumCoordinate] using h

theorem scalarMeasure_survival_moment (f : H) (n : ℕ) :
    (∫ t : ResolventSpectrum R, (1 - (t : ℝ)) ^ n ∂scalarMeasure R hSA f) =
      (inner ℂ f (((1 - R) ^ n) f)).re := by
  have h := scalarMeasure_integral R hSA f ((1 - spectrumCoordinate R) ^ n)
  rw [map_pow, map_sub, map_one, resolventCFC_coordinate] at h
  simpa [spectrumCoordinate] using h

end

end ImbalancedChen.Part3.GenericResolventScalarMeasure20261025a
