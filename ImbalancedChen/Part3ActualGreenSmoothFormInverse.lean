import ImbalancedChen.Part3ActualGreenFormCoreIdentification
import ImbalancedChen.Part3ActualGreenForcingRegularity
import ImbalancedChen.Part3ActualGreenForcingEnergy
import ImbalancedChen.Part3RadialWeightedSmoothCutoffDensity
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
Actual smooth compact forcing/form identification. The literal I/K Green
convolution has proved smoothness and all three L2 energy coordinates.
The actual cutoff-density construction places it in the closed energy
domain. Conjugate Green pairing and genuine form-core density establish
its full variational equation and identify it with the actual Riesz map.
No assumed energy membership, inverse, or operator-image density is used.
-/
namespace ImbalancedChen.Part3.ActualGreenSmoothFormInverse20261025a
noncomputable section
open Set MeasureTheory
open RadialSchrodingerL2Form20261025a ActualGreenFormCoreIdentification20261025a
open GeneralActualRadialGreenSourceOnly ComplexCompactGreenGluingSourceOnly
open ActualGreenCompactForcing20261025a ActualGreenForcingRegularity20261025a
open ActualGreenForcingEnergy20261025a RadialWeightedCutoffDensity20261025a

private theorem real_operator_star (kappa : ℝ) (phi : ℝ → ℂ) (r : ℝ) :
    operator (potential (kappa : ℂ)) (fun x => star (phi x)) r =
      star (operator (potential (kappa : ℂ)) phi r) := by
  simp only [operator, potential, deriv.star', map_add, map_neg, map_mul, map_pow,
    Complex.star_def, Complex.conj_ofReal]

private theorem greenForcing_conjugate_pairing {kappa : ℝ}
    (hkappa : 0 < kappa) (hkappaUpper : kappa < 1) (F T : RadialTest) :
    (∫ r : ℝ, star (greenForcing (kappa : ℂ) F.function r) *
      operator (potential (kappa : ℂ)) T.function r) =
      ∫ r : ℝ, star (F.function r) * T.function r := by
  have hs : ContDiff ℝ 2 (fun r => star (T.function r)) :=
    T.smooth.star.of_le (by simp)
  have hc : HasCompactSupport (fun r => star (T.function r)) :=
    T.compact.comp_left (star_zero ℂ)
  have h := greenForcing_weak_equation (by simpa using hkappa)
    (by simpa using hkappaUpper) F.smooth.continuous F.compact
    (fun r => star (T.function r)) hs hc
  simp only [real_operator_star] at h
  have hh := congrArg (starRingEnd ℂ) h
  simpa only [← integral_conj, map_mul, starRingEnd_apply, star_star] using hh

private theorem actual_green_L2_pairing {kappa : ℝ}
    (hkappa : 0 < kappa) (hkappaUpper : kappa < 1) (F T : RadialTest)
    (hU : MemLp (greenForcing (kappa : ℂ) F.function) 2 (volume : Measure ℝ)) :
    inner ℂ (hU.toLp (greenForcing (kappa : ℂ) F.function))
      (radialCoreOperatorL2 kappa T) = inner ℂ (radialCoreL2 F) (radialCoreL2 T) := by
  calc
    _ = ∫ r : ℝ, star (greenForcing (kappa : ℂ) F.function r) *
        operator (potential (kappa : ℂ)) T.function r := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hU.coeFn_toLp, radialCoreOperatorL2_coe kappa T] with r hu ht
      rw [hu, ht]
      exact RCLike.inner_apply' _ _
    _ = ∫ r : ℝ, star (F.function r) * T.function r :=
      greenForcing_conjugate_pairing hkappa hkappaUpper F T
    _ = _ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [F.function_memLp.coeFn_toLp, T.function_memLp.coeFn_toLp] with r hf ht
      rw [hf, ht]
      exact (RCLike.inner_apply' _ _).symm

/-- Actual form-core density only. No density of the differential image
L(C_c^infty) is used or claimed. -/
private theorem form_identity_of_core_pairings (kappa : ℝ) (hkappa : 0 < kappa)
    (F : RadialL2) (u : radialClosedEnergyDomain kappa)
    (hcore : ∀ T : RadialTest, inner ℂ u (radialCoreEnergy kappa T) =
      inner ℂ F (radialCoreL2 T)) :
    ∀ v : radialClosedEnergyDomain kappa,
      inner ℂ u v = inner ℂ F (radialPhysicalEmbedding kappa v) := by
  let L : RadialEnergyHilbert →L[ℂ] ℂ :=
    innerSL ℂ (u : RadialEnergyHilbert) -
      (innerSL ℂ F).comp (energyPhysicalCoordinate kappa)
  let S : Submodule ℂ RadialEnergyHilbert := L.toLinearMap.ker
  have hs : IsClosed (S : Set RadialEnergyHilbert) := by
    exact isClosed_eq L.continuous continuous_const
  have hspan : radialEnergyCoreSpan kappa ≤ S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨T, rfl⟩
    change inner ℂ (u : RadialEnergyHilbert) (radialEnergyCoreVector kappa T) -
      inner ℂ F (energyPhysicalCoordinate kappa (radialEnergyCoreVector kappa T)) = 0
    rw [energyPhysical_core kappa hkappa T]
    exact sub_eq_zero.mpr (hcore T)
  have hdomain : radialClosedEnergyDomain kappa ≤ S :=
    (radialEnergyCoreSpan kappa).topologicalClosure_minimal hspan hs
  intro v
  have hv := hdomain v.2
  change inner ℂ u v - inner ℂ F (radialPhysicalEmbedding kappa v) = 0 at hv
  exact sub_eq_zero.mp hv

/-- The actual Green convolution in the actual closed radial form domain;
all input regularity and energy bounds come from the same literal kernel. -/
def actualGreenEnergyElement (kappa : ℝ) (hkappa : 0 < kappa)
    (hkappaUpper : kappa < 1) (F : RadialTest) : radialClosedEnergyDomain kappa :=
  smoothFiniteEnergyElement kappa hkappa (greenForcing (kappa : ℂ) F.function)
    (greenForcing_smooth (by simpa using hkappa) (by simpa using hkappaUpper)
      F.smooth F.compact)
    (greenForcing_memLp_two hkappa hkappaUpper F.smooth.continuous F.compact)
    (greenForcing_deriv_memLp_two hkappa hkappaUpper F.smooth.continuous F.compact)
    (greenForcing_exponential_memLp_two hkappa hkappaUpper F.smooth.continuous F.compact)

theorem actualGreenEnergyElement_physical (kappa : ℝ) (hkappa : 0 < kappa)
    (hkappaUpper : kappa < 1) (F : RadialTest) :
    radialPhysicalEmbedding kappa (actualGreenEnergyElement kappa hkappa hkappaUpper F) =
      (greenForcing_memLp_two hkappa hkappaUpper F.smooth.continuous F.compact).toLp
        (greenForcing (kappa : ℂ) F.function) := by
  exact smoothFiniteEnergyElement_physical _ _ _ _ _ _ _

/-- Pairing with every actual completed energy vector, not merely with
compact tests. The extension uses the closed span of actual form cores. -/
theorem actualGreenEnergyElement_variational (kappa : ℝ) (hkappa : 0 < kappa)
    (hkappaUpper : kappa < 1) (F : RadialTest) (v : radialClosedEnergyDomain kappa) :
    inner ℂ (actualGreenEnergyElement kappa hkappa hkappaUpper F) v =
      inner ℂ (radialCoreL2 F) (radialPhysicalEmbedding kappa v) := by
  apply form_identity_of_core_pairings kappa hkappa
  intro T
  calc
    _ = inner ℂ
        (radialPhysicalEmbedding kappa (actualGreenEnergyElement kappa hkappa hkappaUpper F))
        (radialCoreOperatorL2 kappa T) := by
      have h := radialCoreEnergy_operator_pairing kappa hkappa T
        (actualGreenEnergyElement kappa hkappa hkappaUpper F)
      simpa only [inner_conj_symm] using congrArg (starRingEnd ℂ) h
    _ = _ := by
      rw [actualGreenEnergyElement_physical]
      exact actual_green_L2_pairing hkappa hkappaUpper F T _

theorem actualGreenEnergyElement_eq_Riesz (kappa : ℝ) (hkappa : 0 < kappa)
    (hkappaUpper : kappa < 1) (F : RadialTest) :
    actualGreenEnergyElement kappa hkappa hkappaUpper F =
      radialFormRieszSolution kappa (radialCoreL2 F) := by
  exact radialFormRieszSolution_unique kappa (radialCoreL2 F)
    (actualGreenEnergyElement kappa hkappa hkappaUpper F)
    (actualGreenEnergyElement_variational kappa hkappa hkappaUpper F)

/-- True Green/form equality for every smooth compact forcing. The input
is the forcing itself, with no differential-image restriction. -/
theorem actualGreen_eq_form_inverse_smooth {kappa : ℝ}
    (hkappa : 0 < kappa) (hkappaUpper : kappa < 1) (F : RadialTest) :
    greenForcing (kappa : ℂ) F.function =ᵐ[(volume : Measure ℝ)]
      (radialShiftedVariationalInverse kappa (radialCoreL2 F) : ℝ → ℂ) := by
  have he : radialShiftedVariationalInverse kappa (radialCoreL2 F) =
      (greenForcing_memLp_two hkappa hkappaUpper F.smooth.continuous F.compact).toLp
        (greenForcing (kappa : ℂ) F.function) := by
    change radialPhysicalEmbedding kappa (radialFormRieszSolution kappa (radialCoreL2 F)) = _
    rw [← actualGreenEnergyElement_eq_Riesz kappa hkappa hkappaUpper F]
    exact actualGreenEnergyElement_physical kappa hkappa hkappaUpper F
  rw [he]
  exact (greenForcing_memLp_two hkappa hkappaUpper F.smooth.continuous F.compact).coeFn_toLp.symm

end
end ImbalancedChen.Part3.ActualGreenSmoothFormInverse20261025a
