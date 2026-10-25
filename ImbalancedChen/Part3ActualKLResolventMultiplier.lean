import ImbalancedChen.Part3ActualKLResolventCoordinate
import ImbalancedChen.Part3ActualKLCoreTransform
import Mathlib.MeasureTheory.Function.L2Space

/-!
CODE_ONLY / SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

Actual multiplication by the kappa=1/2 resolvent coordinate on the raw
tauMeasure L² quotient. Membership, representative independence through
the quotient construction, complex linearity and the operator bound four
are proved. This is the concrete multiplier needed by the independent
full-L² Green-transform intertwining proof. No intertwining or invariant
range is assumed or asserted here.
-/

namespace ImbalancedChen.Part3.ActualKLResolventMultiplier20261025a

noncomputable section
open MeasureTheory
open ActualKLCoordinateMeasures20261025a ActualKLCoreTransform20261025a
open ActualKLResolventCoordinate20261025a

theorem klCoefficient_norm_le (tau : ℝ) : ‖(klResolventCoordinate tau : ℂ)‖ ≤ 4 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (klResolventCoordinate_pos tau)]
  exact klResolventCoordinate_le_four tau

private theorem rawKLResolventMultiply_memLp (u : RawTauL2) :
    MemLp (fun tau : ℝ => (klResolventCoordinate tau : ℂ) * u tau) 2 tauMeasure := by
  apply (Lp.memLp u).of_le_mul
    ((Complex.continuous_ofReal.comp klResolventCoordinate_continuous).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable u))
  apply Filter.Eventually.of_forall
  intro tau
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (klCoefficient_norm_le tau) (norm_nonneg _)

def rawKLResolventMultiply (u : RawTauL2) : RawTauL2 :=
  (rawKLResolventMultiply_memLp u).toLp (fun tau => (klResolventCoordinate tau : ℂ) * u tau)

theorem rawKLResolventMultiply_coe_ae (u : RawTauL2) :
    rawKLResolventMultiply u =ᵐ[tauMeasure]
      (fun tau => (klResolventCoordinate tau : ℂ) * u tau) :=
  (rawKLResolventMultiply_memLp u).coeFn_toLp

def rawKLResolventLinear : RawTauL2 →ₗ[ℂ] RawTauL2 where
  toFun := rawKLResolventMultiply
  map_add' u v := by
    apply Lp.ext
    filter_upwards [rawKLResolventMultiply_coe_ae (u + v), Lp.coeFn_add u v,
      Lp.coeFn_add (rawKLResolventMultiply u) (rawKLResolventMultiply v),
      rawKLResolventMultiply_coe_ae u, rawKLResolventMultiply_coe_ae v]
        with tau hleft hin hright hu hv
    rw [hleft, hright, hu, hv, hin]
    ring
  map_smul' c u := by
    apply Lp.ext
    filter_upwards [rawKLResolventMultiply_coe_ae (c • u), Lp.coeFn_smul c u,
      Lp.coeFn_smul c (rawKLResolventMultiply u), rawKLResolventMultiply_coe_ae u]
        with tau hleft hin hright hu
    rw [hleft, hright, hu, hin]
    simp only [smul_eq_mul]
    ring

theorem rawKLResolventMultiply_norm_le (u : RawTauL2) :
    ‖rawKLResolventMultiply u‖ ≤ 4 * ‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [rawKLResolventMultiply_coe_ae u] with tau htau
  rw [htau, norm_mul]
  exact mul_le_mul_of_nonneg_right (klCoefficient_norm_le tau) (norm_nonneg _)

def rawKLResolventMultiplier : RawTauL2 →L[ℂ] RawTauL2 :=
  rawKLResolventLinear.mkContinuous 4 rawKLResolventMultiply_norm_le

theorem rawKLResolventMultiplier_coe_ae (u : RawTauL2) :
    rawKLResolventMultiplier u =ᵐ[tauMeasure]
      (fun tau => (klResolventCoordinate tau : ℂ) * u tau) :=
  rawKLResolventMultiply_coe_ae u

/-- Real scalar form matching the actual compact-coordinate transport. -/
theorem rawKLResolventMultiplier_smul_ae (u : RawTauL2) :
    rawKLResolventMultiplier u =ᵐ[tauMeasure]
      (fun tau => (klCompactCoordinate tau : ℝ) • u tau) := by
  simpa only [klCompactCoordinate, Complex.real_smul] using
    rawKLResolventMultiplier_coe_ae u

theorem rawKLResolventMultiplier_norm_le (u : RawTauL2) :
    ‖rawKLResolventMultiplier u‖ ≤ 4 * ‖u‖ :=
  rawKLResolventMultiply_norm_le u

theorem rawKLResolventMultiplier_opNorm_le : ‖rawKLResolventMultiplier‖ ≤ 4 :=
  rawKLResolventMultiplier.opNorm_le_bound (by norm_num) rawKLResolventMultiplier_norm_le

end
end ImbalancedChen.Part3.ActualKLResolventMultiplier20261025a
