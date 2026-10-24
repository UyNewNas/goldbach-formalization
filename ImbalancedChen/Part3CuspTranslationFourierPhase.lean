import ImbalancedChen.Part3ActualLiteralPacketIntegral
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Tactic

/-!
SOURCE ONLY, 2026-10-24; uncompiled.

The Fourier coefficient below is Mathlib's actual normalized-Haar integral on
`UnitAddCircle`. The shift convention is `f(x + a)`, and the coefficient uses
`fourier (-n)` in its defining integral. Hence this translation multiplies
coefficient `n` by `fourier n a = e(n a)`. At `a=1/z`, multiplication by the
existing negative cuspPhase removes that factor. This is a theorem about any
complex function on the circle, not an assertion that a spectral coefficient
has already been represented by such a function.
-/

noncomputable section

namespace P3CuspTranslationFourierPhaseSourceOnly

open AddCircle MeasureTheory
open P3ActualLiteralPacketIntegralSourceOnly (cuspPhase)
open P3Period64NativeReconstructionSourceOnly (e e_add)

def translated (f : UnitAddCircle → ℂ) (a : UnitAddCircle) : UnitAddCircle → ℂ :=
  fun x => f (x + a)

theorem integrable_translated (f : UnitAddCircle → ℂ)
    (hf : Integrable f AddCircle.haarAddCircle) (a : UnitAddCircle) :
    Integrable (translated f a) AddCircle.haarAddCircle := by
  exact hf.comp_add_right a

/-- A right translation `f(x+a)` has the positive `n` character factor.
The proof uses the defining Fourier integral and normalized Haar invariance. -/
theorem fourierCoeff_translated (f : UnitAddCircle → ℂ)
    (a : UnitAddCircle) (n : ℤ) :
    AddCircle.fourierCoeff (translated f a) n =
      AddCircle.fourier n a * AddCircle.fourierCoeff f n := by
  have hunit : (AddCircle.fourier n a : ℂ) * AddCircle.fourier (-n) a = 1 := by
    rw [← AddCircle.fourier_add]
    simp
  have hpoint (x : UnitAddCircle) :
      (AddCircle.fourier (-n) x : ℂ) * f (x + a) =
        AddCircle.fourier n a *
          (AddCircle.fourier (-n) (x + a) * f (x + a)) := by
    have hchar : (AddCircle.fourier (-n) (x + a) : ℂ) =
        AddCircle.fourier (-n) x * AddCircle.fourier (-n) a := by
      simp only [AddCircle.fourier_apply, zsmul_add, toCircle_add, Circle.coe_mul]
    calc
      (AddCircle.fourier (-n) x : ℂ) * f (x + a) =
          ((AddCircle.fourier n a * AddCircle.fourier (-n) a) *
            AddCircle.fourier (-n) x) * f (x + a) := by rw [hunit, one_mul]
      _ = AddCircle.fourier n a *
            (AddCircle.fourier (-n) (x + a) * f (x + a)) := by rw [hchar]; ring
  simp only [AddCircle.fourierCoeff, translated, smul_eq_mul]
  calc
    (∫ x : UnitAddCircle, (AddCircle.fourier (-n) x : ℂ) * f (x + a)
        ∂AddCircle.haarAddCircle) =
        ∫ x : UnitAddCircle, AddCircle.fourier n a *
          (AddCircle.fourier (-n) (x + a) * f (x + a))
          ∂AddCircle.haarAddCircle := by
            apply integral_congr_ae
            filter_upwards [] with x
            exact hpoint x
    _ = AddCircle.fourier n a *
          ∫ x : UnitAddCircle,
            AddCircle.fourier (-n) (x + a) * f (x + a)
            ∂AddCircle.haarAddCircle := by rw [integral_const_mul]
    _ = AddCircle.fourier n a *
          ∫ x : UnitAddCircle, AddCircle.fourier (-n) x * f x
            ∂AddCircle.haarAddCircle := by
          rw [integral_add_right_eq_self
            (fun x : UnitAddCircle => AddCircle.fourier (-n) x * f x) a]

def cuspShift (z : ℕ) : UnitAddCircle := ((1 / (z : ℝ) : ℝ) : UnitAddCircle)

theorem fourier_cuspShift (z n : ℕ) :
    (AddCircle.fourier (n : ℤ) (cuspShift z) : ℂ) = cuspPhase true z n := by
  rw [cuspShift, AddCircle.fourier_coe_apply]
  simp only [cuspPhase, if_true, one_mul, e, div_one]
  congr 1
  push_cast
  ring

private theorem cuspPhase_false_mul_true (z n : ℕ) :
    cuspPhase false z n * cuspPhase true z n = 1 := by
  simp only [cuspPhase, if_true, if_false, one_mul, neg_one_mul, neg_div]
  rw [← e_add]
  simp [e]

/-- The old-chart translation phase `e(n/z)` cancels the actual packet's
negative chart phase `e(-n/z)` at every natural Fourier index. -/
theorem cuspPhase_mul_fourierCoeff_translated
    (f : UnitAddCircle → ℂ) (z n : ℕ) :
    cuspPhase false z n *
        AddCircle.fourierCoeff (translated f (cuspShift z)) (n : ℤ) =
      AddCircle.fourierCoeff f (n : ℤ) := by
  rw [fourierCoeff_translated, fourier_cuspShift]
  rw [← mul_assoc, cuspPhase_false_mul_true, one_mul]

/-- An integrable-function version that records the analytic domain used by
the eventual cusp coefficient, without assuming its spectral realization. -/
theorem integrable_cusp_translation_and_phase
    (f : UnitAddCircle → ℂ) (hf : Integrable f AddCircle.haarAddCircle)
    (z n : ℕ) :
    Integrable (translated f (cuspShift z)) AddCircle.haarAddCircle ∧
      cuspPhase false z n *
        AddCircle.fourierCoeff (translated f (cuspShift z)) (n : ℤ) =
          AddCircle.fourierCoeff f (n : ℤ) := by
  exact ⟨integrable_translated f hf (cuspShift z),
    cuspPhase_mul_fourierCoeff_translated f z n⟩

end P3CuspTranslationFourierPhaseSourceOnly
