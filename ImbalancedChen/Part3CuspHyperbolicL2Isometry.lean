import ImbalancedChen.Part3ActualCuspScalingSourceOnly
import ImbalancedChen.Part3UpperHalfPlaneHyperbolicMeasure
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Group.Action

/-!
SOURCEONLY / UNCOMPILED / no acceptance credit, 2026-10-24.
The actual old/new/translation matrices from the cusp-scaling candidate act
on the actual upper half-plane. Pinned mathlib proves its hyperbolic volume
GL(2,R)-invariant. The standard Lp composition construction therefore gives
complex-linear isometries on the genuine hyperbolic L² space. This is a
geometric Hilbert-space bridge only; no cusp Fourier orthogonality follows.
-/

namespace ImbalancedChen.Part3.CuspHyperbolicL2Isometry20261024z

noncomputable section

open MeasureTheory
open scoped UpperHalfPlane MatrixGroups ENNReal InnerProductSpace
open P3ActualCuspScalingSourceOnly
open ImbalancedChen.Part3.UpperHalfPlaneHyperbolicMeasure20261024z

/-- The genuine complex L² space for mathlib's hyperbolic upper-half-plane
measure `dx dy / y²`. -/
abbrev CuspL2 := Lp ℂ 2 hyperbolicMeasure

/-- Every actual SL(2,R) matrix action preserves the pinned hyperbolic
measure. Its action is the restriction of mathlib's GL(2,R) action, whose
invariance is already proved in UpperHalfPlane.Measure. -/
theorem actualSL_measurePreserving (g : SL(2, ℝ)) :
    MeasurePreserving (fun w : UpperHalfPlane => g • w)
      hyperbolicMeasure hyperbolicMeasure := by
  change MeasurePreserving
    (fun w : UpperHalfPlane => (SpecialLinearGroup.mapGL ℝ g) • w)
    (volume : Measure UpperHalfPlane) (volume : Measure UpperHalfPlane)
  exact measurePreserving_smul (SpecialLinearGroup.mapGL ℝ g)
    (volume : Measure UpperHalfPlane)

/-- Pullback by an actual SL(2,R) upper-half-plane action, as a complex
linear isometry of the genuine hyperbolic L² space. -/
def cuspPullback (g : SL(2, ℝ)) : CuspL2 →ₗᵢ[ℂ] CuspL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun w : UpperHalfPlane => g • w)
    (actualSL_measurePreserving g)

theorem cuspPullback_ae (g : SL(2, ℝ)) (f : CuspL2) :
    cuspPullback g f =ᵐ[hyperbolicMeasure]
      fun w : UpperHalfPlane => f (g • w) := by
  exact Lp.coeFn_compMeasurePreserving f (actualSL_measurePreserving g)

theorem cuspPullback_norm (g : SL(2, ℝ)) (f : CuspL2) :
    ‖cuspPullback g f‖ = ‖f‖ :=
  (cuspPullback g).norm_map f

theorem cuspPullback_inner (g : SL(2, ℝ)) (f h : CuspL2) :
    ⟪cuspPullback g f, cuspPullback g h⟫_ℂ = ⟪f, h⟫_ℂ :=
  (cuspPullback g).inner_map_map f h

/-- Pullback reverses the matrix product: composing the point actions
`g • (h • w)` means composing the L² pullbacks in the order `U_h ∘ U_g`. -/
theorem cuspPullback_mul (g h : SL(2, ℝ)) :
    cuspPullback (g * h) = (cuspPullback h).comp (cuspPullback g) := by
  ext f
  have hc := Lp.compMeasurePreserving_comp_apply
    (E := ℂ) (p := (2 : ℝ≥0∞)) f
    (actualSL_measurePreserving g) (actualSL_measurePreserving h)
  change Lp.compMeasurePreserving (fun w : UpperHalfPlane => (g * h) • w)
      (actualSL_measurePreserving (g * h)) f =
    Lp.compMeasurePreserving (fun w : UpperHalfPlane => h • w)
      (actualSL_measurePreserving h)
      (Lp.compMeasurePreserving (fun w : UpperHalfPlane => g • w)
        (actualSL_measurePreserving g) f)
  have hmap : (fun w : UpperHalfPlane => (g * h) • w) =
      ((fun w : UpperHalfPlane => g • w) ∘
        (fun w : UpperHalfPlane => h • w)) := by
    funext w
    exact mul_smul g h w
  rw [hmap]
  exact hc

/-- The actual old/new cusp matrix identity becomes an exact Hilbert-space
factorization. The right-hand translation acts first on points and last on
L² pullback operators. -/
theorem oldPullback_eq_translation_comp_new (z : ℝ) (hz : 0 < z) :
    cuspPullback (oldSL z hz) =
      (cuspPullback (translationSL z)).comp (cuspPullback (newSL z hz)) := by
  rw [oldSL_eq_newSL_mul_translationSL z hz]
  exact cuspPullback_mul (newSL z hz) (translationSL z)

theorem oldPullback_norm (z : ℝ) (hz : 0 < z) (f : CuspL2) :
    ‖cuspPullback (oldSL z hz) f‖ = ‖f‖ :=
  cuspPullback_norm (oldSL z hz) f

theorem newPullback_norm (z : ℝ) (hz : 0 < z) (f : CuspL2) :
    ‖cuspPullback (newSL z hz) f‖ = ‖f‖ :=
  cuspPullback_norm (newSL z hz) f

theorem translationPullback_norm (z : ℝ) (f : CuspL2) :
    ‖cuspPullback (translationSL z) f‖ = ‖f‖ :=
  cuspPullback_norm (translationSL z) f

end
end ImbalancedChen.Part3.CuspHyperbolicL2Isometry20261024z
