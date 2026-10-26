import ImbalancedChen.Part3GammaCoreGraphEnergyLimit

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

Quantitative form-norm and Dirichlet-error control for the legal core
diagonal. This is the ACTUAL completed form and original core Laplacian.
The zero-energy limit is supplied by the proved graph-zero construction,
not assumed to be an arbitrary constant in the form domain.
-/
namespace ImbalancedChen.Part3.GammaCoreDiagonalEnergyBudget20261026a

noncomputable section
open Gamma0ActualSmoothQuotientCore20261025a
open Gamma0ActualEnergyCompletion20261025a
open Gamma0ActualFriedrichsOperator20261025a
open Gamma0PhysicalClosedDirichletForm20261025a
open GammaCoreGraphEnergyLimit20261026a

theorem shifted_norm_identity (N : ℕ) [NeZero N] (w : EnergyCompletion N) :
    ‖w‖ ^ 2 = ‖physicalProjection N w‖ ^ 2 + (actualDirichletPair N w w).re := by
  unfold actualDirichletPair
  rw [Complex.sub_re, ← InnerProductSpace.norm_sq_eq_re_inner,
    ← InnerProductSpace.norm_sq_eq_re_inner]
  ring

/-- Exact disappearance of the zero-energy limit from the gradient part. -/
theorem energy_distance_sq_identity (N : ℕ) [NeZero N]
    (e : EnergyCompletion N) (he : actualDirichletPair N e e = 0)
    (u : EnergyCore N) :
    ‖coreEmbedding N u - e‖ ^ 2 =
      ‖physicalCore N u - physicalProjection N e‖ ^ 2 +
        (inner ℂ (physicalCore N u) (coreLaplacian N u)).re := by
  have hright := actualDirichletPair_right_zero_of_self_zero N e he (coreEmbedding N u)
  have hleft : actualDirichletPair N e (coreEmbedding N u) = 0 := by
    rw [← actualDirichletPair_star N (coreEmbedding N u) e, hright, star_zero]
  have hdiff : actualDirichletPair N (coreEmbedding N u - e) (coreEmbedding N u - e) =
      actualDirichletPair N (coreEmbedding N u) (coreEmbedding N u) := by
    unfold actualDirichletPair at hright hleft he ⊢
    simp only [map_sub, inner_sub_left, inner_sub_right]
    linear_combination -hright - hleft + he
  rw [shifted_norm_identity, hdiff, map_sub, physicalProjection_core,
    actualDirichletPair_core]

/-- An explicit bound on the genuine gradient/Dirichlet error. The actual
Delta L2 budget controls it by Green pairing and Cauchy--Schwarz. -/
theorem core_Dirichlet_error_le (N : ℕ) [NeZero N] (u : EnergyCore N) :
    (actualDirichletPair N (coreEmbedding N u) (coreEmbedding N u)).re ≤
      ‖physicalCore N u‖ * ‖coreLaplacian N u‖ := by
  rw [actualDirichletPair_core]
  exact re_inner_le_norm _ _

/-- If alpha bounds physical error and beta bounds native Delta output,
then alpha²+(‖f‖+alpha)beta bounds the true form-norm error squared. -/
theorem energy_distance_sq_le (N : ℕ) [NeZero N]
    (e : EnergyCompletion N) (he : actualDirichletPair N e e = 0)
    (u : EnergyCore N) {alpha beta : ℝ} (ha : 0 ≤ alpha)
    (hp : ‖physicalCore N u - physicalProjection N e‖ ≤ alpha)
    (hL : ‖coreLaplacian N u‖ ≤ beta) :
    ‖coreEmbedding N u - e‖ ^ 2 ≤
      alpha ^ 2 + (‖physicalProjection N e‖ + alpha) * beta := by
  have hphys : ‖physicalCore N u‖ ≤ ‖physicalProjection N e‖ + alpha := by
    calc
      _ = ‖physicalProjection N e + (physicalCore N u - physicalProjection N e)‖ := by
        congr 1
        abel
      _ ≤ ‖physicalProjection N e‖ + ‖physicalCore N u - physicalProjection N e‖ := norm_add_le _ _
      _ ≤ _ := add_le_add_left hp _
  rw [energy_distance_sq_identity N e he u]
  exact add_le_add (pow_le_pow_left₀ (norm_nonneg _) hp 2)
    ((re_inner_le_norm (𝕜 := ℂ) (physicalCore N u) (coreLaplacian N u)).trans
      (mul_le_mul hphys hL (norm_nonneg _) (add_nonneg (norm_nonneg _) ha)))

end
end ImbalancedChen.Part3.GammaCoreDiagonalEnergyBudget20261026a

