import ImbalancedChen.Part3GammaZeroSpectralProjectionKernel
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The explicit rank-one projection onto the actual normalized constant
line of Gamma0(N). The scalar coefficient uses the ACTUAL quotient mass,
not a probability rescaling or an automorphic spectral normalization.
Its range lies in the actual native kernel by the proved cutoff closure.
Equality with the entire zero spectral projection is NOT asserted until
the independently owned kernel-subset-constants theorem is supplied.
-/
namespace ImbalancedChen.Part3.GammaConstantRankOneProjection20261026a

noncomputable section
open Set MeasureTheory
open Gamma0ActualSmoothQuotientCore20261025a
open Gamma0ActualConstantMode20261025a
open Gamma0ActualFriedrichsOperator20261025a
open GammaConstantFormClosure20261026a
open GammaNormalizedConstantVector20261026a
open GammaZeroSpectralProjectionKernel20261026a

/-- The literal original physical constant line. -/
def actualConstantLine (N : ℕ) [NeZero N] : Submodule ℂ (QuotientL2 N) :=
  Submodule.span ℂ {constantL2 N}

theorem unitConstant_span_eq (N : ℕ) [NeZero N] :
    Submodule.span ℂ {constantUnit N} = actualConstantLine N := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro f hf
    rw [Set.mem_singleton_iff.mp hf]
    exact (actualConstantLine N).smul_mem ((volumeRoot N)⁻¹ : ℂ)
      (Submodule.mem_span_singleton_self (constantL2 N))
  · apply Submodule.span_le.mpr
    intro f hf
    rw [Set.mem_singleton_iff.mp hf, ← volumeRoot_smul_constantUnit N]
    exact (Submodule.span ℂ {constantUnit N}).smul_mem (volumeRoot N : ℂ)
      (Submodule.mem_span_singleton_self (constantUnit N))

/-- Constructed continuous rank-one map, with the native complex inner
product convention (linear in the second slot). -/
def constantRankOne (N : ℕ) [NeZero N] : QuotientL2 N →L[ℂ] QuotientL2 N :=
  InnerProductSpace.rankOne ℂ (constantUnit N) (constantUnit N)

theorem constantRankOne_apply (N : ℕ) [NeZero N] (f : QuotientL2 N) :
    constantRankOne N f = inner ℂ (constantUnit N) f • constantUnit N := rfl

/-- This is an actual orthogonal projection, not merely an idempotent
algebraic formula. -/
theorem constantRankOne_eq_lineOrthogonalProjection (N : ℕ) [NeZero N] :
    constantRankOne N = (actualConstantLine N).starProjection := by
  ext f
  rw [← unitConstant_span_eq N, Submodule.starProjection_singleton]
  simp only [constantRankOne_apply, constantUnit_norm, one_pow, Complex.ofReal_one, div_one]

/-- Exact unnormalized mean/covolume formula in the original measure. -/
theorem constantRankOne_apply_mean (N : ℕ) [NeZero N] (f : QuotientL2 N) :
    constantRankOne N f =
      ((∫ q, f q ∂Gamma0QuotientCellPushforward20261025a.carrierPushforward N) /
        (actualVolume N : ℂ)) • constantL2 N := by
  rw [constantRankOne_eq_lineOrthogonalProjection]
  change (Submodule.span ℂ {constantL2 N}).starProjection f = _
  rw [Submodule.starProjection_singleton, constantL2_norm_sq, constantL2_inner]

theorem constantRankOne_isStarProjection (N : ℕ) [NeZero N] :
    IsStarProjection (constantRankOne N) :=
  InnerProductSpace.isStarProjection_rankOne_self (constantUnit_norm N)

theorem constantRankOne_rank (N : ℕ) [NeZero N] : (constantRankOne N).rank = 1 :=
  InnerProductSpace.rank_rankOne (constantUnit_ne_zero N) (constantUnit_ne_zero N)

theorem constantRankOne_norm (N : ℕ) [NeZero N] : ‖constantRankOne N‖ = 1 := by
  simp only [constantRankOne, InnerProductSpace.norm_rankOne, constantUnit_norm, mul_one]

theorem constantRankOne_range_le_kernel (N : ℕ) [NeZero N] (f : QuotientL2 N) :
    constantRankOne N f ∈ ambientFriedrichsKernel N := by
  change (constantRankOne N f, (0 : QuotientL2 N)) ∈ (actualGammaFriedrichs N).graph
  rw [constantRankOne_apply]
  simpa only [Prod.smul_mk, smul_zero] using (actualGammaFriedrichs N).graph.smul_mem
    (inner ℂ (constantUnit N) f) (constantUnit_mem_friedrichsGraph_zero N)

/-- The full zero spectral projection contains this proven constant
sector, without assuming that no other kernel vectors exist. -/
theorem zeroProjection_comp_constantRankOne (N : ℕ) [NeZero N] :
    (actualZeroProjection N).comp (constantRankOne N) = constantRankOne N := by
  ext f
  exact (actualZeroProjection_fixed_iff_kernel N _).mpr (constantRankOne_range_le_kernel N f)

end
end ImbalancedChen.Part3.GammaConstantRankOneProjection20261026a
