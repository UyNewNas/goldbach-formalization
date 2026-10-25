import ImbalancedChen.Part3ActualCuspFourierSection
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

The manuscript uses R(n)=sqrt(|n|)*rho(n). This module proves the precise
weighted Parseval bookkeeping for the ACTUAL normalized-Haar Fourier
coefficients of the actual Gamma0 cusp sections. The zero mode is restored
explicitly: division by |0| must not erase its mass. The phase relating the
two actual cusp charts preserves this weighted coefficient energy.

This is transverse Fourier analysis at a fixed positive geometric height.
It does not identify these section coefficients with Maass/Eisenstein rho,
remove the Bessel factor, construct a spectral resolution, or supply the
canonical continuous spectral measure dt/cosh(pi*t) or its 1/(4*pi) factor.
-/

namespace ImbalancedChen.Part3.ActualCuspWeightedFourierParseval20261025a
noncomputable section

open MeasureTheory AddCircle
open scoped MatrixGroups UpperHalfPlane
open ImbalancedChen.Part3.ActualCuspFourierSectionSourceOnly

/-- Literal square-root normalization of an actual circle Fourier integral. -/
def normalizedSectionCoefficient (F : UnitAddCircle → ℂ) (n : ℤ) : ℂ :=
  (Real.sqrt |(n : ℝ)| : ℂ) * AddCircle.fourierCoeff F n

/-- The coefficient weight includes the original zero Fourier coefficient. -/
def restoredCoefficientEnergy (F : UnitAddCircle → ℂ) (n : ℤ) : ℝ :=
  if n = 0 then ‖AddCircle.fourierCoeff F 0‖ ^ 2
  else ‖normalizedSectionCoefficient F n‖ ^ 2 / |(n : ℝ)|

theorem normalizedSectionCoefficient_norm_sq (F : UnitAddCircle → ℂ) (n : ℤ) :
    ‖normalizedSectionCoefficient F n‖ ^ 2 =
      |(n : ℝ)| * ‖AddCircle.fourierCoeff F n‖ ^ 2 := by
  simp only [normalizedSectionCoefficient, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (abs_nonneg _)]

theorem restoredCoefficientEnergy_eq (F : UnitAddCircle → ℂ) (n : ℤ) :
    restoredCoefficientEnergy F n = ‖AddCircle.fourierCoeff F n‖ ^ 2 := by
  by_cases hn : n = 0
  · simp [restoredCoefficientEnergy, hn]
  · have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have hweight : |(n : ℝ)| ≠ 0 := abs_ne_zero.mpr hnR
    rw [restoredCoefficientEnergy, if_neg hn, normalizedSectionCoefficient_norm_sq]
    field_simp

/-- Pinned Mathlib Parseval transported from its Lp representative to the
literal function; continuity supplies all needed square integrability. -/
theorem hasSum_restoredCoefficientEnergy (F : UnitAddCircle → ℂ)
    (hF : Continuous F) :
    HasSum (restoredCoefficientEnergy F)
      (∫ x : UnitAddCircle, ‖F x‖ ^ 2 ∂AddCircle.haarAddCircle) := by
  have hc : HasCompactSupport F := isClosed_tsupport.isCompact
  have hL2 : MemLp F 2 AddCircle.haarAddCircle :=
    hF.memLp_of_hasCompactSupport hc
  have hcoeff (n : ℤ) :
      AddCircle.fourierCoeff (hL2.toLp F) n = AddCircle.fourierCoeff F n :=
    congrFun (AddCircle.fourierCoeff_congr_ae hL2.coeFn_toLp) n
  have hint :
      (∫ x : UnitAddCircle, ‖(hL2.toLp F) x‖ ^ 2 ∂AddCircle.haarAddCircle) =
        ∫ x : UnitAddCircle, ‖F x‖ ^ 2 ∂AddCircle.haarAddCircle := by
    apply integral_congr_ae
    filter_upwards [hL2.coeFn_toLp] with x hx
    rw [hx]
  simpa only [restoredCoefficientEnergy_eq, hcoeff, hint] using
    AddCircle.hasSum_sq_fourierCoeff (hL2.toLp F)

theorem tsum_restoredCoefficientEnergy (F : UnitAddCircle → ℂ)
    (hF : Continuous F) :
    (∑' n : ℤ, restoredCoefficientEnergy F n) =
      ∫ x : UnitAddCircle, ‖F x‖ ^ 2 ∂AddCircle.haarAddCircle :=
  (hasSum_restoredCoefficientEnergy F hF).tsum_eq

variable (N : ℕ) (hN : 0 < N) (f : ℍ → ℂ)
  (hfΓ : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N →
    ∀ z : ℍ, f (γ • z) = f z) (y : ℝ) (hy : 0 < y)

/-- The old/new actual cusp matrices give equal energies at EVERY mode,
including zero. No spectral realization of f is assumed. -/
theorem actual_old_new_restored_energy (n : ℤ) :
    restoredCoefficientEnergy (oldSection N hN f hfΓ y hy) n =
      restoredCoefficientEnergy (newSection N hN f hfΓ y hy) n := by
  rw [restoredCoefficientEnergy_eq, restoredCoefficientEnergy_eq]
  change ‖oldFourierCoeff N hN f hfΓ y hy n‖ ^ 2 =
    ‖newFourierCoeff N hN f hfΓ y hy n‖ ^ 2
  rw [oldFourierCoeff_phase, norm_mul]
  simp only [AddCircle.fourier_apply, ContinuousMap.coe_mk, Circle.norm_coe, one_mul]

/-- Actual Gamma0 cusp trace, with the sqrt(|n|) normalization and its
inverse weight, retains all of its normalized-Haar transverse L2 mass. -/
theorem actual_new_section_weighted_parseval (hf : Continuous f) :
    (∑' n : ℤ, restoredCoefficientEnergy (newSection N hN f hfΓ y hy) n) =
      ∫ x : UnitAddCircle, ‖newSection N hN f hfΓ y hy x‖ ^ 2
        ∂AddCircle.haarAddCircle :=
  tsum_restoredCoefficientEnergy _ (newSection_continuous N hN f hf hfΓ y hy)

theorem actual_old_section_weighted_parseval (hf : Continuous f) :
    (∑' n : ℤ, restoredCoefficientEnergy (oldSection N hN f hfΓ y hy) n) =
      ∫ x : UnitAddCircle, ‖oldSection N hN f hfΓ y hy x‖ ^ 2
        ∂AddCircle.haarAddCircle :=
  tsum_restoredCoefficientEnergy _ (oldSection_continuous N hN f hf hfΓ y hy)

/-- Geometric cusp-chart change preserves the full transverse norm. -/
theorem actual_old_new_section_energy (hf : Continuous f) :
    (∫ x : UnitAddCircle, ‖oldSection N hN f hfΓ y hy x‖ ^ 2
      ∂AddCircle.haarAddCircle) =
      ∫ x : UnitAddCircle, ‖newSection N hN f hfΓ y hy x‖ ^ 2
        ∂AddCircle.haarAddCircle := by
  rw [← actual_old_section_weighted_parseval N hN f hfΓ y hy hf,
    ← actual_new_section_weighted_parseval N hN f hfΓ y hy hf]
  exact tsum_congr (actual_old_new_restored_energy N hN f hfΓ y hy)

end
end ImbalancedChen.Part3.ActualCuspWeightedFourierParseval20261025a
