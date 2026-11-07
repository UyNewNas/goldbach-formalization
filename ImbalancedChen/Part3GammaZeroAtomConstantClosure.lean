import ImbalancedChen.Part3GammaConstantRankOneProjection
import ImbalancedChen.Part3GammaFriedrichsKernelConstantRigidity

/-!
SOURCE ONLY / UNCOMPILED / NO FORMAL CREDIT.

The genuine zero spectral projection of the original Gamma0 Friedrichs
operator is exactly the rank-one projection onto the original constant
line. Kernel rigidity and cutoff closure are independently proved inputs,
not hypotheses on the vector or on the operator. The resulting scalar
zero atom has the original physical quotient-volume denominator.
No automorphic spectral expansion or whole-plane Hardy bound is asserted.
-/
namespace ImbalancedChen.Part3.GammaZeroAtomConstantClosure20261026a

noncomputable section
open Set MeasureTheory
open Gamma0ActualSmoothQuotientCore20261025a
open Gamma0QuotientCellPushforward20261025a
open Gamma0ActualConstantMode20261025a
open Gamma0ActualFriedrichsOperator20261025a
open Gamma0ActualUnboundedScalarMeasure20261025a
open GammaConstantFormClosure20261026a
open GammaNormalizedConstantVector20261026a
open GammaZeroSpectralProjectionKernel20261026a
open GammaConstantRankOneProjection20261026a
open GammaFriedrichsKernelConstantRigidity20261026a

/-- Equality of the actual ambient native kernel and the actual constant
line, using graph membership to invoke the domain-subtype rigidity result. -/
theorem actualKernel_eq_constantLine (N : ℕ) [NeZero N] :
    ambientFriedrichsKernel N = actualConstantLine N := by
  apply le_antisymm
  · intro f hf
    have hgraph : (f, (0 : QuotientL2 N)) ∈ (actualGammaFriedrichs N).graph :=
      (ambientFriedrichsKernel_mem_iff N f).mp hf
    obtain ⟨u, hu, hzero⟩ := LinearPMap.mem_graph_iff.mp hgraph
    obtain ⟨C, hC⟩ := native_friedrichs_kernel_eq_scalar_constant N u hzero
    have hfC : f = C • constantL2 N := hu.symm.trans hC
    rw [hfC]
    exact (actualConstantLine N).smul_mem C
      (Submodule.mem_span_singleton_self (constantL2 N))
  · exact constantLine_le_friedrichsKernel N

/-- Identification of the already constructed true zero Borel projection;
neither a rank-one premise nor a constancy premise is introduced. -/
theorem actualZeroProjection_eq_constantRankOne (N : ℕ) [NeZero N] :
    actualZeroProjection N = constantRankOne N := by
  rw [actualZeroProjection_eq_kernelOrthogonalProjection,
    actualKernelOrthogonalProjection, actualKernel_eq_constantLine]
  exact (constantRankOne_eq_lineOrthogonalProjection N).symm

/-- The zero projection has the literal physical mean/covolume coefficient. -/
theorem actualZeroProjection_apply_mean (N : ℕ) [NeZero N] (f : QuotientL2 N) :
    actualZeroProjection N f =
      ((∫ q, f q ∂carrierPushforward N) / (actualVolume N : ℂ)) • constantL2 N := by
  rw [actualZeroProjection_eq_constantRankOne]
  exact constantRankOne_apply_mean N f

theorem actualZeroProjection_rank (N : ℕ) [NeZero N] :
    (actualZeroProjection N).rank = 1 := by
  rw [actualZeroProjection_eq_constantRankOne]
  exact constantRankOne_rank N

/-- Squared physical zero-sector norm with the unchanged finite-volume
normalization, obtained from the genuine orthogonal projection formula. -/
theorem actualZeroProjection_norm_sq_mean (N : ℕ) [NeZero N] (f : QuotientL2 N) :
    ‖actualZeroProjection N f‖ ^ 2 =
      ‖∫ q, f q ∂carrierPushforward N‖ ^ 2 / actualVolume N := by
  rw [actualZeroProjection_apply_mean, norm_smul, mul_pow, constantL2_norm_sq,
    norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (actualVolume_pos N)]
  field_simp [(actualVolume_pos N).ne'] <;> ring

/-- Exact zero atom of the ACTUAL unbounded scalar Laplace measure. -/
theorem actualLaplaceMeasure_zero_eq_mean_norm_sq (N : ℕ) [NeZero N]
    (f : QuotientL2 N) :
    actualLaplaceMeasure N f {0} =
      ENNReal.ofReal (‖∫ q, f q ∂carrierPushforward N‖ ^ 2 / actualVolume N) := by
  rw [actualLaplaceMeasure_zero_eq_projection_norm_sq, actualZeroProjection_norm_sq_mean]

/-- Absence of the actual zero atom is exactly the physical mean-zero
condition, ready for a genuine cusp/continuous-sector decomposition. -/
theorem actualLaplaceMeasure_zero_eq_zero_iff_mean_zero (N : ℕ) [NeZero N]
    (f : QuotientL2 N) :
    actualLaplaceMeasure N f {0} = 0 ↔ ∫ q, f q ∂carrierPushforward N = 0 := by
  rw [actualLaplaceMeasure_zero_eq_mean_norm_sq, ENNReal.ofReal_eq_zero]
  constructor
  · intro h
    have hle : ‖∫ q, f q ∂carrierPushforward N‖ ^ 2 ≤ 0 := by
      simpa only [zero_mul] using (div_le_iff₀ (actualVolume_pos N)).mp h
    have hsq : ‖∫ q, f q ∂carrierPushforward N‖ ^ 2 = 0 :=
      le_antisymm hle (sq_nonneg _)
    exact norm_eq_zero.mp (pow_eq_zero hsq)
  · intro h
    simp [h]

end
end ImbalancedChen.Part3.GammaZeroAtomConstantClosure20261026a
