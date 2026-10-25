import ImbalancedChen.Part3Gamma0CompactCoreGradient
import Mathlib.Analysis.Normed.Operator.Extend

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-25.

The actual smooth-core weighted gradient extends uniquely from the SAME
actual shifted energy core into vector-valued L2 on each compact H set.
The domain is the existing genuine Gamma0 energy completion, not a new
completion or a claimed adjoint-defect form domain. Every actual energy
core approximation converges strongly in this local gradient L2 space.
This is a form-domain gradient supplier. No elliptic regularity, weak
derivative identification for arbitrary adjoint vectors, or scalar
quotient gradient is asserted.
-/

namespace ImbalancedChen.Part3.Gamma0EnergyCompactGradientExtension20261025a

noncomputable section
open Set Filter MeasureTheory
open UniformSpace
open scoped UpperHalfPlane
open ImbalancedChen.Part3.Gamma0ActualSmoothQuotientCore20261025a
open ImbalancedChen.Part3.Gamma0CompactGlobalOverlap20261025a
open ImbalancedChen.Part3.Gamma0ActualEnergyCompletion20261025a
open ImbalancedChen.Part3.Gamma0CompactCoreGradient20261025a

theorem coreGradient_bound_on_embedding (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) (u : EnergyCore N) :
    ‖coreGradientLinear N hK u‖ ≤
      Real.sqrt (compactOverlapBound N K : ℝ)*‖coreEmbedding N u‖ := by
  rw [coreEmbedding_norm]
  exact coreGradientLinear_bound N hK u

/-- Genuine local vector gradient on the already constructed actual
Gamma0 energy completion, obtained using the PROVED core bound. -/
def completedCompactGradient (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) :
    EnergyCompletion N →L[ℂ] CompactGradientL2 K :=
  (coreGradientLinear N hK).extendOfNorm (coreEmbedding N).toLinearMap

theorem completedCompactGradient_core (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) (u : EnergyCore N) :
    completedCompactGradient N hK (coreEmbedding N u) = coreGradientL2 N hK u :=
  LinearMap.extendOfNorm_eq (coreEmbedding_denseRange N)
    ⟨Real.sqrt (compactOverlapBound N K : ℝ),coreGradient_bound_on_embedding N hK⟩ u

theorem completedCompactGradient_norm_le (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) (e : EnergyCompletion N) :
    ‖completedCompactGradient N hK e‖ ≤
      Real.sqrt (compactOverlapBound N K : ℝ)*‖e‖ := by
  exact LinearMap.norm_extendOfNorm_apply_le (f := coreGradientLinear N hK)
    (e := (coreEmbedding N).toLinearMap) (coreEmbedding_denseRange N)
    (Real.sqrt (compactOverlapBound N K : ℝ)) (coreGradient_bound_on_embedding N hK) e

theorem completedCompactGradient_opNorm_le (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) :
    ‖completedCompactGradient N hK‖ ≤ Real.sqrt (compactOverlapBound N K : ℝ) := by
  apply (completedCompactGradient N hK).opNorm_le_bound (Real.sqrt_nonneg _)
  exact completedCompactGradient_norm_le N hK

theorem completedCompactGradient_norm_sq_le (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) (e : EnergyCompletion N) :
    ‖completedCompactGradient N hK e‖^2 ≤ (compactOverlapBound N K : ℝ)*‖e‖^2 := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (completedCompactGradient_norm_le N hK e) 2
  simpa only [mul_pow,Real.sq_sqrt (Nat.cast_nonneg _)] using h

/-- Equality on the actual dense energy-core embedding determines the
continuous local gradient uniquely. There is no choice of approximation. -/
theorem completedCompactGradient_unique (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K)
    (G : EnergyCompletion N →L[ℂ] CompactGradientL2 K)
    (hG : ∀ u : EnergyCore N, G (coreEmbedding N u) = coreGradientL2 N hK u) :
    G = completedCompactGradient N hK := by
  ext e
  refine Completion.induction_on e ?_ ?_
  · exact isClosed_eq G.continuous (completedCompactGradient N hK).continuous
  · intro u
    exact (hG u).trans (completedCompactGradient_core N hK u).symm

/-- Any actual core approximation in the genuine energy completion
converges strongly in the vector L2 gradient space on K. -/
theorem core_energy_approximation_gradient_tendsto (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) {ι : Type*} {l : Filter ι}
    (u : ι → EnergyCore N) (e : EnergyCompletion N)
    (hu : Tendsto (fun i => coreEmbedding N (u i)) l (𝓝 e)) :
    Tendsto (fun i => coreGradientL2 N hK (u i)) l
      (𝓝 (completedCompactGradient N hK e)) := by
  have h := ((completedCompactGradient N hK).continuous.tendsto e).comp hu
  simpa only [Function.comp_def,completedCompactGradient_core] using h

/-- The local limit cannot depend on the chosen core approximation. -/
theorem two_core_energy_approximations_same_gradient (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K)
    (u v : ℕ → EnergyCore N) (e : EnergyCompletion N)
    (hu : Tendsto (fun n => coreEmbedding N (u n)) atTop (𝓝 e))
    (hv : Tendsto (fun n => coreEmbedding N (v n)) atTop (𝓝 e)) :
    Tendsto (fun n => coreGradientL2 N hK (u n)-coreGradientL2 N hK (v n))
      atTop (𝓝 0) := by
  simpa only [sub_self] using
    (core_energy_approximation_gradient_tendsto N hK u e hu).sub
      (core_energy_approximation_gradient_tendsto N hK v e hv)

end
end ImbalancedChen.Part3.Gamma0EnergyCompactGradientExtension20261025a
