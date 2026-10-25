import ImbalancedChen.Part3FrickeNormalizer
import ImbalancedChen.Part3Gamma0GeneralCuspUnitPeriod

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
The ORIGINAL normalized cuspOne chart is T*W_N*T_(1/N), for the literal
Fricke matrix W_N supplied separately. Genuine Gamma0 T-invariance then
identifies the existing new-chart trace with the literal Fricke trace.
The existing actual normalized-Haar translation theorem is REUSED, not
reproved, to obtain the positive exp(2*pi*i*n/N) Fourier phase at every
integer n. Integrability is transported for the actual fixed-height trace.
No division by a radial K factor or unspecified spectral dt is asserted.
-/

namespace ImbalancedChen.Part3.ActualFrickeCuspPhase20261025a
noncomputable section
open MeasureTheory Matrix Matrix.SpecialLinearGroup MatrixGroups AddCircle
open scoped MatrixGroups ModularGroup UpperHalfPlane
open FrickeNormalizer
open Gamma0ActualCuspsSourceOnly
open Gamma0GeneralCuspUnitPeriod20261025a
open ActualCuspFourierSectionSourceOnly
open P3ActualCuspScalingSourceOnly
open P3CuspTranslationFourierPhaseSourceOnly

/-- Literal matrix product: the old newSL chart is T times the actual
Fricke matrix, with both sqrt(N) factors retained. -/
theorem newSL_eq_translation_fricke (N : ℕ) (hN : 0 < N) :
    newSL (N : ℝ) (by exact_mod_cast hN) = integralReal ModularGroup.T * frickeSL N hN := by
  apply Subtype.ext
  simp [newSL, newScaling, integralReal, frickeSL, frickeMatrix,
    coe_mul, Matrix.mul_fin_two, Matrix.SpecialLinearGroup.map_apply_coe, ModularGroup.coe_T]

/-- Exact ORIGINAL cuspOne normalization, not an assumed scaling identity. -/
theorem original_cuspOneScaling_eq_fricke (N : ℕ) (hN : 0 < N) :
    normalizedScaling N hN cuspOneMatrix =
      (integralReal ModularGroup.T * frickeSL N hN) * translationSL (N : ℝ) := by
  rw [normalizedScaling_cuspOne, oldSL_eq_newSL_mul_translationSL,
    newSL_eq_translation_fricke N hN]

def frickeTrace (N : ℕ) (hN : 0 < N) (F : ℍ → ℂ)
    (y : ℝ) (hy : 0 < y) (x : ℝ) : ℂ :=
  F (frickeSL N hN • horizontal y hy x)

/-- The left T is an ACTUAL Gamma0 matrix, so Gamma0 invariance removes
it from the trace, without requiring a Fricke eigenfunction hypothesis. -/
theorem newTrace_eq_frickeTrace (N : ℕ) (hN : 0 < N) (F : ℍ → ℂ)
    (hF : ∀ g : SL(2, ℤ), g ∈ CongruenceSubgroup.Gamma0 N → ∀ z : ℍ, F (g • z) = F z)
    (y : ℝ) (hy : 0 < y) : newTrace N hN F y hy = frickeTrace N hN F y hy := by
  funext x
  unfold newTrace frickeTrace
  rw [newSL_eq_translation_fricke N hN, mul_smul, integralReal_smul]
  apply hF ModularGroup.T
  simpa only [zpow_one] using translation_mem_gamma0 N 1

theorem frickeTrace_periodic (N : ℕ) (hN : 0 < N) (F : ℍ → ℂ)
    (hF : ∀ g : SL(2, ℤ), g ∈ CongruenceSubgroup.Gamma0 N → ∀ z : ℍ, F (g • z) = F z)
    (y : ℝ) (hy : 0 < y) : Function.Periodic (frickeTrace N hN F y hy) 1 := by
  rw [← newTrace_eq_frickeTrace N hN F hF y hy]
  exact newTrace_periodic N hN F hF y hy

def frickeSection (N : ℕ) (hN : 0 < N) (F : ℍ → ℂ)
    (hF : ∀ g : SL(2, ℤ), g ∈ CongruenceSubgroup.Gamma0 N → ∀ z : ℍ, F (g • z) = F z)
    (y : ℝ) (hy : 0 < y) : UnitAddCircle → ℂ :=
  (frickeTrace_periodic N hN F hF y hy).lift

/-- The section is built from the newly constructed original sigmaOne
matrix, and is subsequently proved equal to the old source section. -/
def sigmaOneSection (N : ℕ) (hN : 0 < N) (F : ℍ → ℂ)
    (hF : ∀ g : SL(2, ℤ), g ∈ CongruenceSubgroup.Gamma0 N → ∀ z : ℍ, F (g • z) = F z)
    (y : ℝ) (hy : 0 < y) : UnitAddCircle → ℂ :=
  (Gamma0GeneralCuspUnitPeriod20261025a.normalizedTrace_periodic N hN cuspOneMatrix F hF y hy).lift

theorem newSection_eq_frickeSection (N : ℕ) (hN : 0 < N) (F : ℍ → ℂ)
    (hF : ∀ g : SL(2, ℤ), g ∈ CongruenceSubgroup.Gamma0 N → ∀ z : ℍ, F (g • z) = F z)
    (y : ℝ) (hy : 0 < y) : newSection N hN F hF y hy = frickeSection N hN F hF y hy := by
  funext z
  induction z using QuotientAddGroup.induction_on with | _ x =>
    change newTrace N hN F y hy x = frickeTrace N hN F y hy x
    exact congrFun (newTrace_eq_frickeTrace N hN F hF y hy) x

theorem sigmaOneSection_eq_oldSection (N : ℕ) (hN : 0 < N) (F : ℍ → ℂ)
    (hF : ∀ g : SL(2, ℤ), g ∈ CongruenceSubgroup.Gamma0 N → ∀ z : ℍ, F (g • z) = F z)
    (y : ℝ) (hy : 0 < y) : sigmaOneSection N hN F hF y hy = oldSection N hN F hF y hy := by
  funext z
  induction z using QuotientAddGroup.induction_on with | _ x =>
    change F (normalizedScaling N hN cuspOneMatrix • horizontal y hy x) =
      F (oldSL (N : ℝ) _ • horizontal y hy x)
    rw [normalizedScaling_cuspOne]

theorem sigmaOneSection_eq_translated_frickeSection (N : ℕ) (hN : 0 < N) (F : ℍ → ℂ)
    (hF : ∀ g : SL(2, ℤ), g ∈ CongruenceSubgroup.Gamma0 N → ∀ z : ℍ, F (g • z) = F z)
    (y : ℝ) (hy : 0 < y) :
    sigmaOneSection N hN F hF y hy =
      translated (frickeSection N hN F hF y hy) (cuspShift N) := by
  rw [sigmaOneSection_eq_oldSection, oldSection_eq_translated_newSection,
    newSection_eq_frickeSection]

def frickeFourierCoeff (N : ℕ) (hN : 0 < N) (F : ℍ → ℂ)
    (hF : ∀ g : SL(2, ℤ), g ∈ CongruenceSubgroup.Gamma0 N → ∀ z : ℍ, F (g • z) = F z)
    (y : ℝ) (hy : 0 < y) (n : ℤ) : ℂ :=
  AddCircle.fourierCoeff (frickeSection N hN F hF y hy) n

theorem fourier_cuspShift_int (N : ℕ) (n : ℤ) :
    AddCircle.fourier n (cuspShift N) =
      Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) / (N : ℂ)) := by
  simp [cuspShift, AddCircle.fourier_coe_apply, div_eq_mul_inv] <;> ring

/-- Reuse the genuine normalized-Haar translation integral, now bound
to the original sigmaOne and the literal actual Fricke trace. -/
theorem sigmaOne_fourierCoeff_fricke_phase (N : ℕ) (hN : 0 < N) (F : ℍ → ℂ)
    (hF : ∀ g : SL(2, ℤ), g ∈ CongruenceSubgroup.Gamma0 N → ∀ z : ℍ, F (g • z) = F z)
    (y : ℝ) (hy : 0 < y) (n : ℤ) :
    AddCircle.fourierCoeff (sigmaOneSection N hN F hF y hy) n =
      Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) / (N : ℂ)) *
        frickeFourierCoeff N hN F hF y hy n := by
  rw [sigmaOneSection_eq_translated_frickeSection]
  simpa only [fourier_cuspShift_int, frickeFourierCoeff] using
    fourierCoeff_translated (frickeSection N hN F hF y hy) (cuspShift N) n

theorem integrable_sigmaOneSection (N : ℕ) (hN : 0 < N) (F : ℍ → ℂ)
    (hF : ∀ g : SL(2, ℤ), g ∈ CongruenceSubgroup.Gamma0 N → ∀ z : ℍ, F (g • z) = F z)
    (y : ℝ) (hy : 0 < y)
    (htrace : Integrable (frickeSection N hN F hF y hy) AddCircle.haarAddCircle) :
    Integrable (sigmaOneSection N hN F hF y hy) AddCircle.haarAddCircle := by
  rw [sigmaOneSection_eq_translated_frickeSection]
  exact integrable_translated _ htrace _

theorem integrable_sigmaOne_and_phase (N : ℕ) (hN : 0 < N) (F : ℍ → ℂ)
    (hF : ∀ g : SL(2, ℤ), g ∈ CongruenceSubgroup.Gamma0 N → ∀ z : ℍ, F (g • z) = F z)
    (y : ℝ) (hy : 0 < y)
    (htrace : Integrable (frickeSection N hN F hF y hy) AddCircle.haarAddCircle) (n : ℤ) :
    Integrable (sigmaOneSection N hN F hF y hy) AddCircle.haarAddCircle ∧
      AddCircle.fourierCoeff (sigmaOneSection N hN F hF y hy) n =
        Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) / (N : ℂ)) *
          frickeFourierCoeff N hN F hF y hy n :=
  ⟨integrable_sigmaOneSection N hN F hF y hy htrace,
    sigmaOne_fourierCoeff_fricke_phase N hN F hF y hy n⟩

end
end ImbalancedChen.Part3.ActualFrickeCuspPhase20261025a
