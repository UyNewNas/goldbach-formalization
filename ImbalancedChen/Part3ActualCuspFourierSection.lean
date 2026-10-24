import ImbalancedChen.Part3ActualCuspWidthNormalization
import ImbalancedChen.Part3CuspTranslationFourierPhase
import Mathlib.Analysis.Complex.UpperHalfPlane.ProperAction
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Tactic

/-!
SOURCE ONLY, 2026-10-24. UNCOMPILED; no acceptance credit.

For a continuous function on the upper half plane invariant under the actual
Mathlib Gamma0 N, this constructs the continuous unit-circle sections in the
old and new cusp-1 scaling charts. Its Fourier coefficients are the actual
normalized-Haar integrals, and the exact old/new matrix identity produces
the translation phase. No Maass or oldform assertion is used.
-/

namespace ImbalancedChen.Part3.ActualCuspFourierSectionSourceOnly
noncomputable section

open Matrix Matrix.SpecialLinearGroup MatrixGroups AddCircle
open scoped MatrixGroups ModularGroup UpperHalfPlane
open P3ActualCuspScalingSourceOnly
open P3CuspTranslationFourierPhaseSourceOnly
open ImbalancedChen.Part3.ActualCuspWidthNormalizationSourceOnly
open ImbalancedChen.Part3.Gamma0ActualCuspsSourceOnly

private abbrev levelPos (N : ℕ) (hN : 0 < N) : (0 : ℝ) < N := by
  exact_mod_cast hN

/-- The horizontal line of height `y` in the actual upper half plane. -/
def horizontal (y : ℝ) (hy : 0 < y) (x : ℝ) : ℍ :=
  UpperHalfPlane.mk ((x : ℂ) + (y : ℂ) * Complex.I) (by simpa using hy)

theorem horizontal_continuous (y : ℝ) (hy : 0 < y) :
    Continuous (horizontal y hy) := by
  apply Continuous.upperHalfPlaneMk
  · fun_prop
  · intro x
    simpa using hy

private theorem cast_smul (γ : SL(2, ℤ)) (z : ℍ) :
    Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ • z = γ • z := by
  apply UpperHalfPlane.ext
  simp only [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [Matrix.SpecialLinearGroup.map_apply_coe]

private theorem horizontal_integer_translate (y : ℝ) (hy : 0 < y) (x : ℝ) :
    horizontal y hy (x + 1) = realTranslation 1 • horizontal y hy x := by
  change horizontal y hy (x + 1) =
    Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) (ModularGroup.T ^ 1) •
      horizontal y hy x
  rw [cast_smul]
  apply UpperHalfPlane.ext
  rw [ModularGroup.coe_T_zpow_smul_eq (z := horizontal y hy x) (n := 1)]
  simp [horizontal, add_assoc, add_comm, add_left_comm]

private theorem horizontal_fractional_translate (N : ℕ) (y : ℝ)
    (hy : 0 < y) (x : ℝ) :
    translationSL (N : ℝ) • horizontal y hy x =
      horizontal y hy (x + 1 / (N : ℝ)) := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [translationSL, translation, horizontal, Complex.ofReal_div] <;> ring

/-- The actual old-chart trace before descent to the unit circle. -/
def oldTrace (N : ℕ) (hN : 0 < N) (f : ℍ → ℂ)
    (y : ℝ) (hy : 0 < y) (x : ℝ) : ℂ :=
  f (oldSL (N : ℝ) (levelPos N hN) • horizontal y hy x)

/-- The actual new-chart trace before descent to the unit circle. -/
def newTrace (N : ℕ) (hN : 0 < N) (f : ℍ → ℂ)
    (y : ℝ) (hy : 0 < y) (x : ℝ) : ℂ :=
  f (newSL (N : ℝ) (levelPos N hN) • horizontal y hy x)

theorem oldTrace_continuous (N : ℕ) (hN : 0 < N)
    (f : ℍ → ℂ) (hf : Continuous f) (y : ℝ) (hy : 0 < y) :
    Continuous (oldTrace N hN f y hy) := by
  exact hf.comp ((continuous_const_smul _).comp (horizontal_continuous y hy))

theorem newTrace_continuous (N : ℕ) (hN : 0 < N)
    (f : ℍ → ℂ) (hf : Continuous f) (y : ℝ) (hy : 0 < y) :
    Continuous (newTrace N hN f y hy) := by
  exact hf.comp ((continuous_const_smul _).comp (horizontal_continuous y hy))

/-- Gamma0 invariance gives exact period one after old cusp scaling. -/
theorem oldTrace_periodic (N : ℕ) (hN : 0 < N)
    (f : ℍ → ℂ)
    (hfΓ : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N →
      ∀ z : ℍ, f (γ • z) = f z)
    (y : ℝ) (hy : 0 < y) :
    Function.Periodic (oldTrace N hN f y hy) 1 := by
  let s := oldSL (N : ℝ) (levelPos N hN)
  let γ : SL(2, ℤ) :=
    cuspOneMatrix * ModularGroup.T ^ (N : ℤ) * cuspOneMatrix⁻¹
  have hγ : γ ∈ CongruenceSubgroup.Gamma0 N := by
    simpa [γ] using normalized_period_integral_mem_gamma0 N hN 1
  have hc : s * realTranslation 1 =
      Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ * s := by
    have h := oldSL_conj_translation_eq_integral N hN 1
    have h' : s * realTranslation 1 * s⁻¹ =
        Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ := by
      simpa [s, γ] using h
    calc
      s * realTranslation 1 = (s * realTranslation 1 * s⁻¹) * s := by group
      _ = Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ * s := by rw [h']
  intro x
  change f (s • horizontal y hy (x + 1)) =
    f (s • horizontal y hy x)
  rw [horizontal_integer_translate]
  rw [← mul_smul, hc, mul_smul, cast_smul]
  exact hfΓ γ hγ (s • horizontal y hy x)

/-- The matrix identity gives a literal translation of actual traces. -/
theorem oldTrace_eq_newTrace_shift (N : ℕ) (hN : 0 < N)
    (f : ℍ → ℂ) (y : ℝ) (hy : 0 < y) (x : ℝ) :
    oldTrace N hN f y hy x =
      newTrace N hN f y hy (x + 1 / (N : ℝ)) := by
  unfold oldTrace newTrace
  rw [oldSL_smul_eq (N : ℝ) (levelPos N hN)]
  rw [horizontal_fractional_translate]

theorem newTrace_periodic (N : ℕ) (hN : 0 < N)
    (f : ℍ → ℂ)
    (hfΓ : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N →
      ∀ z : ℍ, f (γ • z) = f z)
    (y : ℝ) (hy : 0 < y) :
    Function.Periodic (newTrace N hN f y hy) 1 := by
  intro x
  have h := oldTrace_periodic N hN f hfΓ y hy (x - 1 / (N : ℝ))
  rw [oldTrace_eq_newTrace_shift N hN f y hy] at h
  convert h using 1 <;> congr 1 <;> ring

/-- Both descended sections are genuine functions on `ℝ / ℤ`. -/
def oldSection (N : ℕ) (hN : 0 < N) (f : ℍ → ℂ)
    (hfΓ : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N →
      ∀ z : ℍ, f (γ • z) = f z)
    (y : ℝ) (hy : 0 < y) : UnitAddCircle → ℂ :=
  (oldTrace_periodic N hN f hfΓ y hy).lift

def newSection (N : ℕ) (hN : 0 < N) (f : ℍ → ℂ)
    (hfΓ : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N →
      ∀ z : ℍ, f (γ • z) = f z)
    (y : ℝ) (hy : 0 < y) : UnitAddCircle → ℂ :=
  (newTrace_periodic N hN f hfΓ y hy).lift

theorem oldSection_continuous (N : ℕ) (hN : 0 < N)
    (f : ℍ → ℂ) (hf : Continuous f)
    (hfΓ : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N →
      ∀ z : ℍ, f (γ • z) = f z)
    (y : ℝ) (hy : 0 < y) :
    Continuous (oldSection N hN f hfΓ y hy) := by
  unfold oldSection Function.Periodic.lift
  exact (oldTrace_continuous N hN f hf y hy).quotient_liftOn' _

theorem newSection_continuous (N : ℕ) (hN : 0 < N)
    (f : ℍ → ℂ) (hf : Continuous f)
    (hfΓ : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N →
      ∀ z : ℍ, f (γ • z) = f z)
    (y : ℝ) (hy : 0 < y) :
    Continuous (newSection N hN f hfΓ y hy) := by
  unfold newSection Function.Periodic.lift
  exact (newTrace_continuous N hN f hf y hy).quotient_liftOn' _

/-- The old section is the actual translated new section. -/
theorem oldSection_eq_translated_newSection (N : ℕ) (hN : 0 < N)
    (f : ℍ → ℂ)
    (hfΓ : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N →
      ∀ z : ℍ, f (γ • z) = f z)
    (y : ℝ) (hy : 0 < y) :
    oldSection N hN f hfΓ y hy =
      translated (newSection N hN f hfΓ y hy) (cuspShift N) := by
  funext z
  induction z using QuotientAddGroup.induction_on with | _ x =>
    change oldTrace N hN f y hy x =
      newTrace N hN f y hy (x + 1 / (N : ℝ))
    exact oldTrace_eq_newTrace_shift N hN f y hy x

/-- This is Mathlib's actual integer Fourier coefficient integral. -/
def oldFourierCoeff (N : ℕ) (hN : 0 < N) (f : ℍ → ℂ)
    (hfΓ : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N →
      ∀ z : ℍ, f (γ • z) = f z)
    (y : ℝ) (hy : 0 < y) (n : ℤ) : ℂ :=
  AddCircle.fourierCoeff (oldSection N hN f hfΓ y hy) n

def newFourierCoeff (N : ℕ) (hN : 0 < N) (f : ℍ → ℂ)
    (hfΓ : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N →
      ∀ z : ℍ, f (γ • z) = f z)
    (y : ℝ) (hy : 0 < y) (n : ℤ) : ℂ :=
  AddCircle.fourierCoeff (newSection N hN f hfΓ y hy) n

theorem oldFourierCoeff_phase (N : ℕ) (hN : 0 < N)
    (f : ℍ → ℂ)
    (hfΓ : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N →
      ∀ z : ℍ, f (γ • z) = f z)
    (y : ℝ) (hy : 0 < y) (n : ℤ) :
    oldFourierCoeff N hN f hfΓ y hy n =
      AddCircle.fourier n (cuspShift N) *
        newFourierCoeff N hN f hfΓ y hy n := by
  rw [oldFourierCoeff, newFourierCoeff,
    oldSection_eq_translated_newSection]
  exact fourierCoeff_translated _ _ _

/-- At natural modes the preexisting negative cusp phase cancels. -/
theorem cuspPhase_cancels_actual_section (N : ℕ) (hN : 0 < N)
    (f : ℍ → ℂ)
    (hfΓ : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N →
      ∀ z : ℍ, f (γ • z) = f z)
    (y : ℝ) (hy : 0 < y) (n : ℕ) :
    P3ActualLiteralPacketIntegralSourceOnly.cuspPhase false N n *
      oldFourierCoeff N hN f hfΓ y hy (n : ℤ) =
        newFourierCoeff N hN f hfΓ y hy (n : ℤ) := by
  rw [oldFourierCoeff, newFourierCoeff,
    oldSection_eq_translated_newSection]
  exact cuspPhase_mul_fourierCoeff_translated _ N n

end
end ImbalancedChen.Part3.ActualCuspFourierSectionSourceOnly
