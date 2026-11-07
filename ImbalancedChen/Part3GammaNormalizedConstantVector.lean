import ImbalancedChen.Part3Gamma0ActualConstantMode
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The genuine unit constant in the actual finite-volume Gamma0 quotient,
normalized by the positive ACTUAL quotient mass. No probability-measure
renormalization or automorphic spectral normalization is introduced.
Form and operator membership belong to the independent cutoff consumer.
-/
namespace ImbalancedChen.Part3.GammaNormalizedConstantVector20261026a

noncomputable section
open Set MeasureTheory
open Gamma0QuotientCellPushforward20261025a
open Gamma0ActualConstantMode20261025a

/-- The positive square root of the actual physical covolume. -/
def volumeRoot (N : ℕ) [NeZero N] : ℝ := Real.sqrt (actualVolume N)

theorem volumeRoot_pos (N : ℕ) [NeZero N] : 0 < volumeRoot N :=
  Real.sqrt_pos.mpr (actualVolume_pos N)

theorem constantL2_norm_eq_volumeRoot (N : ℕ) [NeZero N] :
    ‖constantL2 N‖ = volumeRoot N := by
  apply (sq_eq_sq₀ (norm_nonneg _) (volumeRoot_pos N).le).mp
  exact (constantL2_norm_sq N).trans (Real.sq_sqrt (actualVolume_pos N).le).symm

/-- This scalar is tied to the existing carrierPushforward measure. -/
def constantUnit (N : ℕ) [NeZero N] : QuotientL2 N :=
  ((volumeRoot N)⁻¹ : ℂ) • constantL2 N

theorem constantUnit_ae (N : ℕ) [NeZero N] :
    (constantUnit N : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
      (fun _ => ((volumeRoot N)⁻¹ : ℂ)) := by
  filter_upwards [Lp.coeFn_smul ((volumeRoot N)⁻¹ : ℂ) (constantL2 N),
    constantL2_ae N] with q hs h1
  change ((((volumeRoot N)⁻¹ : ℂ) • constantL2 N) : Gamma0OrbitSpace N → ℂ) q = _
  rw [hs, h1]
  simp only [smul_eq_mul, mul_one]

theorem constantUnit_norm (N : ℕ) [NeZero N] : ‖constantUnit N‖ = 1 := by
  rw [constantUnit, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (volumeRoot_pos N)), constantL2_norm_eq_volumeRoot,
    inv_mul_cancel₀ (volumeRoot_pos N).ne']

theorem constantUnit_ne_zero (N : ℕ) [NeZero N] : constantUnit N ≠ 0 := by
  intro hz
  have hn := constantUnit_norm N
  rw [hz, norm_zero] at hn
  exact zero_ne_one hn

theorem volumeRoot_smul_constantUnit (N : ℕ) [NeZero N] :
    (volumeRoot N : ℂ) • constantUnit N = constantL2 N := by
  rw [constantUnit, smul_smul]
  have hc : (volumeRoot N : ℂ) * ((volumeRoot N)⁻¹ : ℂ) = 1 := by
    exact_mod_cast mul_inv_cancel₀ (volumeRoot_pos N).ne'
  rw [hc, one_smul]

/-- The constant coefficient has the genuine physical covolume factor. -/
theorem constantUnit_inner (N : ℕ) [NeZero N] (f : QuotientL2 N) :
    inner ℂ (constantUnit N) f =
      ((volumeRoot N)⁻¹ : ℂ) * (∫ q, f q ∂carrierPushforward N) := by
  rw [constantUnit, inner_smul_left, constantL2_inner]
  simp

end
end ImbalancedChen.Part3.GammaNormalizedConstantVector20261026a

