import ImbalancedChen.Part3ActualLiteralPacketIntegral
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Tactic

/-!
SOURCE ONLY, 2026-10-24; uncompiled.

This adapter uses Mathlib's actual Hilbert basis of all integer Fourier modes
on the unit AddCircle with normalized Haar measure. In particular, Parseval
is an infinite HasSum/ℓ² statement, not a finite packet identity. The cusp
translation result applies to arbitrary functions in this Hilbert space; it
does not identify any Maass or Eisenstein coefficient with one of them.
-/

noncomputable section

namespace P3CuspFourierL2PlancherelSourceOnly

open AddCircle MeasureTheory
open P3ActualLiteralPacketIntegralSourceOnly (cuspPhase)
open P3Period64NativeReconstructionSourceOnly (e e_add norm_e)

abbrev CircleL2 := Lp ℂ 2 AddCircle.haarAddCircle

/-- All-integer Fourier coefficients as an actual ℓ² vector. -/
def fourierTransformL2 : CircleL2 ≃ₗᵢ[ℂ] ℓ²(ℤ, ℂ) :=
  (AddCircle.fourierBasis (T := (1 : ℝ))).repr

theorem fourierTransformL2_apply (f : CircleL2) (n : ℤ) :
    fourierTransformL2 f n = AddCircle.fourierCoeff f n := by
  exact AddCircle.fourierBasis_repr f n

theorem fourierTransformL2_norm (f : CircleL2) :
    ‖fourierTransformL2 f‖ = ‖f‖ :=
  fourierTransformL2.norm_map f

/-- Mathlib's infinite Parseval theorem, exposed at the real cusp's period 1. -/
theorem hasSum_sq_allFourierCoeff (f : CircleL2) :
    HasSum (fun n : ℤ => ‖AddCircle.fourierCoeff f n‖ ^ 2)
      (∫ x : UnitAddCircle, ‖f x‖ ^ 2 ∂AddCircle.haarAddCircle) :=
  AddCircle.hasSum_sq_fourierCoeff f

theorem tsum_sq_allFourierCoeff (f : CircleL2) :
    (∑' n : ℤ, ‖AddCircle.fourierCoeff f n‖ ^ 2) =
      ∫ x : UnitAddCircle, ‖f x‖ ^ 2 ∂AddCircle.haarAddCircle :=
  AddCircle.tsum_sq_fourierCoeff f

private theorem fourierCoeff_shift (f : UnitAddCircle → ℂ)
    (a : UnitAddCircle) (n : ℤ) :
    AddCircle.fourierCoeff (fun x => f (x + a)) n =
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
  simp only [AddCircle.fourierCoeff, smul_eq_mul]
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

def cuspTranslateL2 (z : ℕ) : CircleL2 →ₗᵢ[ℂ] CircleL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x : UnitAddCircle => x + cuspShift z)
    (measurePreserving_add_right AddCircle.haarAddCircle (cuspShift z))

theorem cuspTranslateL2_ae (z : ℕ) (f : CircleL2) :
    (cuspTranslateL2 z f : UnitAddCircle → ℂ) =ᵐ[AddCircle.haarAddCircle]
      fun x => f (x + cuspShift z) := by
  simpa only [cuspTranslateL2, Function.comp_def] using
    (Lp.coeFn_compMeasurePreserving f
      (measurePreserving_add_right AddCircle.haarAddCircle (cuspShift z)))

theorem fourierCoeff_cuspTranslateL2 (z : ℕ) (f : CircleL2) (n : ℤ) :
    AddCircle.fourierCoeff (cuspTranslateL2 z f) n =
      AddCircle.fourier n (cuspShift z) * AddCircle.fourierCoeff f n := by
  calc
    AddCircle.fourierCoeff (cuspTranslateL2 z f) n =
        AddCircle.fourierCoeff (fun x => f (x + cuspShift z)) n := by
          exact congrFun (AddCircle.fourierCoeff_congr_ae (cuspTranslateL2_ae z f)) n
    _ = AddCircle.fourier n (cuspShift z) * AddCircle.fourierCoeff f n :=
      fourierCoeff_shift f (cuspShift z) n

theorem fourier_cuspShift_eq_e (z : ℕ) (n : ℤ) :
    (AddCircle.fourier n (cuspShift z) : ℂ) = e ((n : ℝ) / (z : ℝ)) := by
  rw [cuspShift, AddCircle.fourier_coe_apply]
  simp only [e, div_one]
  congr 1
  push_cast
  ring

theorem fourierCoeff_cuspTranslateL2_phase (z : ℕ) (f : CircleL2) (n : ℤ) :
    AddCircle.fourierCoeff (cuspTranslateL2 z f) n =
      e ((n : ℝ) / (z : ℝ)) * AddCircle.fourierCoeff f n := by
  rw [fourierCoeff_cuspTranslateL2, fourier_cuspShift_eq_e]

theorem cuspTranslateL2_phase_norm (z : ℕ) (n : ℤ) :
    ‖e ((n : ℝ) / (z : ℝ))‖ = 1 := norm_e _

/-- Coordinatewise phase identity inside the actual all-integer ℓ² vector. -/
theorem fourierTransformL2_cuspTranslateL2_apply
    (z : ℕ) (f : CircleL2) (n : ℤ) :
    fourierTransformL2 (cuspTranslateL2 z f) n =
      e ((n : ℝ) / (z : ℝ)) * fourierTransformL2 f n := by
  rw [fourierTransformL2_apply, fourierTransformL2_apply,
    fourierCoeff_cuspTranslateL2_phase]

/-- Translation multiplies every integer coefficient by a unit phase and
therefore preserves the norm of the entire ℓ² coefficient vector. -/
theorem allFourierCoeff_cuspTranslateL2_norm (z : ℕ) (f : CircleL2) :
    ‖fourierTransformL2 (cuspTranslateL2 z f)‖ =
      ‖fourierTransformL2 f‖ := by
  rw [fourierTransformL2_norm, fourierTransformL2_norm]
  exact (cuspTranslateL2 z).norm_map f

private theorem cuspPhase_false_mul_e (z n : ℕ) :
    cuspPhase false z n * e ((n : ℝ) / (z : ℝ)) = 1 := by
  simp only [cuspPhase, if_false, neg_one_mul, neg_div]
  rw [← e_add]
  simp [e]

/-- On natural indices, the actual negative packet phase cancels the
positive translation phase of the full L² Fourier coefficient. -/
theorem cuspPhase_cancel_cuspTranslateL2_coefficient
    (z n : ℕ) (f : CircleL2) :
    cuspPhase false z n *
        AddCircle.fourierCoeff (cuspTranslateL2 z f) (n : ℤ) =
      AddCircle.fourierCoeff f (n : ℤ) := by
  rw [fourierCoeff_cuspTranslateL2_phase]
  simp only [Int.cast_natCast]
  rw [← mul_assoc, cuspPhase_false_mul_e, one_mul]

end P3CuspFourierL2PlancherelSourceOnly
