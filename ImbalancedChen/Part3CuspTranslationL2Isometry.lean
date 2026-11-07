import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.Measure

/-!
SOURCE ONLY, 2026-10-24; uncompiled.

Translation by `a` is composition with `x ↦ x+a` on Mathlib's actual
normalized-Haar L² space of complex functions on UnitAddCircle. This is the
Hilbert-space geometry needed before a cusp spectral coefficient is built;
no spectral function or orthonormal packet is assumed here.
-/

noncomputable section

namespace P3CuspTranslationL2IsometrySourceOnly

open AddCircle MeasureTheory

abbrev CircleL2 := Lp ℂ 2 AddCircle.haarAddCircle

def shift (a : UnitAddCircle) : UnitAddCircle → UnitAddCircle := fun x => x + a

theorem shift_measurePreserving (a : UnitAddCircle) :
    MeasurePreserving (shift a) AddCircle.haarAddCircle AddCircle.haarAddCircle := by
  exact measurePreserving_add_right AddCircle.haarAddCircle a

/-- The existing `Lp.compMeasurePreservingₗᵢ` applied to the real circle's
normalized Haar measure. -/
def translateL2 (a : UnitAddCircle) : CircleL2 →ₗᵢ[ℂ] CircleL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ (shift a) (shift_measurePreserving a)

theorem translateL2_ae (a : UnitAddCircle) (f : CircleL2) :
    (translateL2 a f : UnitAddCircle → ℂ) =ᵐ[AddCircle.haarAddCircle]
      fun x => f (x + a) := by
  simpa only [translateL2, shift, Function.comp_def] using
    (Lp.coeFn_compMeasurePreserving f (shift_measurePreserving a))

theorem translateL2_norm (a : UnitAddCircle) (f : CircleL2) :
    ‖translateL2 a f‖ = ‖f‖ := by
  exact (translateL2 a).norm_map f

theorem translateL2_inner (a : UnitAddCircle) (f g : CircleL2) :
    inner ℂ (translateL2 a f) (translateL2 a g) = inner ℂ f g := by
  exact (translateL2 a).inner_map_map f g

/-- Haar translation invariance for the literal squared-norm integral. -/
theorem integral_norm_sq_shift (f : UnitAddCircle → ℂ) (a : UnitAddCircle) :
    (∫ x : UnitAddCircle, ‖f (x + a)‖ ^ 2 ∂AddCircle.haarAddCircle) =
      ∫ x : UnitAddCircle, ‖f x‖ ^ 2 ∂AddCircle.haarAddCircle := by
  exact integral_add_right_eq_self (fun x : UnitAddCircle => ‖f x‖ ^ 2) a

/-- Haar translation invariance for the literal complex inner-product
integral, agreeing with Mathlib's `L2.inner_def`. -/
theorem integral_inner_shift (f g : UnitAddCircle → ℂ) (a : UnitAddCircle) :
    (∫ x : UnitAddCircle, inner ℂ (f (x + a)) (g (x + a))
      ∂AddCircle.haarAddCircle) =
      ∫ x : UnitAddCircle, inner ℂ (f x) (g x)
        ∂AddCircle.haarAddCircle := by
  exact integral_add_right_eq_self
    (fun x : UnitAddCircle => inner ℂ (f x) (g x)) a

/-- The squared-norm integral of an actual L² representative is preserved. -/
theorem translateL2_integral_norm_sq (a : UnitAddCircle) (f : CircleL2) :
    (∫ x : UnitAddCircle, ‖(translateL2 a f) x‖ ^ 2
      ∂AddCircle.haarAddCircle) =
      ∫ x : UnitAddCircle, ‖f x‖ ^ 2 ∂AddCircle.haarAddCircle := by
  calc
    (∫ x : UnitAddCircle, ‖(translateL2 a f) x‖ ^ 2
        ∂AddCircle.haarAddCircle) =
        ∫ x : UnitAddCircle, ‖f (x + a)‖ ^ 2
          ∂AddCircle.haarAddCircle := by
            apply integral_congr_ae
            filter_upwards [translateL2_ae a f] with x hx
            rw [hx]
    _ = ∫ x : UnitAddCircle, ‖f x‖ ^ 2
          ∂AddCircle.haarAddCircle := integral_norm_sq_shift f a

/-- The Hilbert inner product agrees with the preserved pointwise integral. -/
theorem translateL2_inner_integral (a : UnitAddCircle) (f g : CircleL2) :
    (∫ x : UnitAddCircle, inner ℂ ((translateL2 a f) x) ((translateL2 a g) x)
      ∂AddCircle.haarAddCircle) =
      ∫ x : UnitAddCircle, inner ℂ (f x) (g x)
        ∂AddCircle.haarAddCircle := by
  rw [← L2.inner_def, ← L2.inner_def]
  exact translateL2_inner a f g

def cuspShift (z : ℕ) : UnitAddCircle := ((1 / (z : ℝ) : ℝ) : UnitAddCircle)

def cuspTranslateL2 (z : ℕ) : CircleL2 →ₗᵢ[ℂ] CircleL2 :=
  translateL2 (cuspShift z)

theorem cuspTranslateL2_norm (z : ℕ) (f : CircleL2) :
    ‖cuspTranslateL2 z f‖ = ‖f‖ :=
  translateL2_norm (cuspShift z) f

theorem cuspTranslateL2_inner (z : ℕ) (f g : CircleL2) :
    inner ℂ (cuspTranslateL2 z f) (cuspTranslateL2 z g) = inner ℂ f g :=
  translateL2_inner (cuspShift z) f g

theorem cuspTranslateL2_ae (z : ℕ) (f : CircleL2) :
    (cuspTranslateL2 z f : UnitAddCircle → ℂ) =ᵐ[AddCircle.haarAddCircle]
      fun x => f (x + cuspShift z) :=
  translateL2_ae (cuspShift z) f

theorem cuspTranslateL2_integral_norm_sq (z : ℕ) (f : CircleL2) :
    (∫ x : UnitAddCircle, ‖(cuspTranslateL2 z f) x‖ ^ 2
      ∂AddCircle.haarAddCircle) =
      ∫ x : UnitAddCircle, ‖f x‖ ^ 2 ∂AddCircle.haarAddCircle :=
  translateL2_integral_norm_sq (cuspShift z) f

theorem cuspTranslateL2_inner_integral (z : ℕ) (f g : CircleL2) :
    (∫ x : UnitAddCircle,
      inner ℂ ((cuspTranslateL2 z f) x) ((cuspTranslateL2 z g) x)
        ∂AddCircle.haarAddCircle) =
      ∫ x : UnitAddCircle, inner ℂ (f x) (g x)
        ∂AddCircle.haarAddCircle :=
  translateL2_inner_integral (cuspShift z) f g

end P3CuspTranslationL2IsometrySourceOnly
