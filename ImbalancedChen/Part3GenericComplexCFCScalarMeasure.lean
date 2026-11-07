import ImbalancedChen.Part3ComplexContractionResolvent
import ImbalancedChen.Part3GenericResolventScalarMeasure
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic

/-!
CODE_ONLY / SOURCEONLY / UNCOMPILED, 2026-10-25. No acceptance credit.

The genuinely constructed generic RMK scalar measure now represents
complex-valued CFC functions on the self-adjoint spectrum. Real/imaginary
decomposition and the pinned real-to-complex CFC restriction identify
the actual complex operator, rather than defining an unrelated integral
operator. In particular the actual complex graph resolvent has its exact
scalar coefficient represented by t/(1-(1+z)t).

The lambda=1/t-1 pushforward and removal of the zero atom are separate
dependencies; no Cauchy representation or spectral conclusion is assumed.
-/

namespace ImbalancedChen.Part3.GenericComplexCFCScalarMeasure20261025a

noncomputable section
open Set MeasureTheory
open GenericResolventScalarMeasure20261025a
open ComplexContractionResolvent20261025a

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private def realRestriction (ψ : ℂ → ℂ) (t : ℝ) : ℝ := (ψ (t : ℂ)).re
private def imagRestriction (ψ : ℂ → ℂ) (t : ℝ) : ℝ := (ψ (t : ℂ)).im

private theorem restriction_continuousOn (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R)
    (ψ : ℂ → ℂ) (hψ : ContinuousOn ψ (spectrum ℂ R)) :
    ContinuousOn (fun t : ℝ => ψ (t : ℂ)) (spectrum ℝ R) :=
  hψ.comp Complex.continuous_ofReal.continuousOn
    (fun _ ht => hSA.coe_mem_spectrum_complex.mpr ht)

/-- Complex CFC is exactly the complex linear combination of its genuine
real and imaginary real-CFC operators. -/
theorem complex_cfc_eq_real_imag (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R)
    (ψ : ℂ → ℂ) (hψ : ContinuousOn ψ (spectrum ℂ R)) :
    cfc ψ R = cfc (realRestriction ψ) R + Complex.I • cfc (imagRestriction ψ) R := by
  have hψR := restriction_continuousOn R hSA ψ hψ
  have hre : ContinuousOn (realRestriction ψ) (spectrum ℝ R) :=
    Complex.continuous_re.comp_continuousOn hψR
  have him : ContinuousOn (imagRestriction ψ) (spectrum ℝ R) :=
    Complex.continuous_im.comp_continuousOn hψR
  have hmap : MapsTo Complex.re (spectrum ℂ R) (spectrum ℝ R) := by
    intro w hw
    apply hSA.coe_mem_spectrum_complex.mp
    rw [← hSA.mem_spectrum_eq_re hw]
    exact hw
  have hReLift : ContinuousOn (fun w : ℂ => (realRestriction ψ w.re : ℂ)) (spectrum ℂ R) :=
    Complex.continuous_ofReal.comp_continuousOn
      (hre.comp Complex.continuous_re.continuousOn hmap)
  have hImLift : ContinuousOn (fun w : ℂ => (imagRestriction ψ w.re : ℂ)) (spectrum ℂ R) :=
    Complex.continuous_ofReal.comp_continuousOn
      (him.comp Complex.continuous_re.continuousOn hmap)
  have heq : (spectrum ℂ R).EqOn ψ (fun w : ℂ =>
      (realRestriction ψ w.re : ℂ) + Complex.I * (imagRestriction ψ w.re : ℂ)) := by
    intro w hw
    dsimp only [realRestriction, imagRestriction]
    rw [← hSA.mem_spectrum_eq_re hw]
    simpa only [mul_comm] using (Complex.re_add_im (ψ w)).symm
  rw [cfc_congr heq,
    cfc_add (hf := hReLift) (hg := continuousOn_const.mul hImLift),
    cfc_const_mul Complex.I (fun w : ℂ => (imagRestriction ψ w.re : ℂ)) R hImLift,
    ← cfc_real_eq_complex (realRestriction ψ) hSA,
    ← cfc_real_eq_complex (imagRestriction ψ) hSA]

/-- Exact complex-valued integration formula for the actual generic scalar
RMK measure. Only continuity of the arbitrary CFC function is an input. -/
theorem scalarMeasure_complex_cfc_integral (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R)
    (u : H) (ψ : ℂ → ℂ) (hψ : ContinuousOn ψ (spectrum ℂ R)) :
    (∫ t : ResolventSpectrum R, ψ ((t : ℝ) : ℂ) ∂scalarMeasure R hSA u) =
      inner ℂ u ((cfc ψ R) u) := by
  have hψR := restriction_continuousOn R hSA ψ hψ
  have hre : ContinuousOn (realRestriction ψ) (spectrum ℝ R) :=
    Complex.continuous_re.comp_continuousOn hψR
  have him : ContinuousOn (imagRestriction ψ) (spectrum ℝ R) :=
    Complex.continuous_im.comp_continuousOn hψR
  let φre : C(ResolventSpectrum R, ℝ) := ⟨_, hre.domRestrict⟩
  let φim : C(ResolventSpectrum R, ℝ) := ⟨_, him.domRestrict⟩
  have hCre : resolventCFC R hSA φre = cfc (realRestriction ψ) R :=
    (cfc_apply (realRestriction ψ) R hSA hre).symm
  have hCim : resolventCFC R hSA φim = cfc (imagRestriction ψ) R :=
    (cfc_apply (imagRestriction ψ) R hSA him).symm
  have hrepRe := scalarMeasure_complex_integral R hSA u φre
  have hrepIm := scalarMeasure_complex_integral R hSA u φim
  rw [hCre] at hrepRe
  rw [hCim] at hrepIm
  have hReCont : Continuous (fun t : ResolventSpectrum R => (φre t : ℂ)) :=
    Complex.continuous_ofReal.comp φre.continuous
  have hImCont : Continuous (fun t : ResolventSpectrum R => (φim t : ℂ)) :=
    Complex.continuous_ofReal.comp φim.continuous
  have hReInt : Integrable (fun t : ResolventSpectrum R => (φre t : ℂ)) (scalarMeasure R hSA u) :=
    hReCont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hImInt : Integrable (fun t : ResolventSpectrum R => (φim t : ℂ)) (scalarMeasure R hSA u) :=
    hImCont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc
    (∫ t : ResolventSpectrum R, ψ ((t : ℝ) : ℂ) ∂scalarMeasure R hSA u) =
        ∫ t : ResolventSpectrum R, (φre t : ℂ) + Complex.I * (φim t : ℂ)
          ∂scalarMeasure R hSA u := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun t => by
        dsimp only [φre, φim, realRestriction, imagRestriction, ContinuousMap.coe_mk]
        simpa only [mul_comm] using (Complex.re_add_im (ψ ((t : ℝ) : ℂ))).symm)
    _ = (∫ t : ResolventSpectrum R, (φre t : ℂ) ∂scalarMeasure R hSA u) +
        Complex.I * ∫ t : ResolventSpectrum R, (φim t : ℂ) ∂scalarMeasure R hSA u := by
      rw [integral_add hReInt (hImInt.const_mul Complex.I), integral_const_mul]
    _ = inner ℂ u ((cfc (realRestriction ψ) R) u) +
        Complex.I * inner ℂ u ((cfc (imagRestriction ψ) R) u) := by rw [hrepRe, hrepIm]
    _ = inner ℂ u ((cfc ψ R) u) := by
      rw [complex_cfc_eq_real_imag R hSA ψ hψ,
        ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        inner_add_right, inner_smul_right]

/-- The actual complex graph resolvent has its exact scalar measure
coefficient, before the lambda=1/t-1 pushforward. -/
theorem complexResolvent_scalarCoefficient (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R)
    (u : H) {z : ℂ} (hz : z.im ≠ 0) :
    inner ℂ u (complexResolvent R z u) =
      ∫ t : ResolventSpectrum R, complexResolventRatio z ((t : ℝ) : ℂ)
        ∂scalarMeasure R hSA u := by
  exact (scalarMeasure_complex_cfc_integral R hSA u (complexResolventRatio z)
    (complexResolventRatio_continuousOn R hSA hz)).symm

end
end ImbalancedChen.Part3.GenericComplexCFCScalarMeasure20261025a
