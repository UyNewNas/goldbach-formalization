import ImbalancedChen.Part3GenericGlobalBorelProjection
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Real.Sqrt

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.
Dominated strong convergence in the actual unrestricted spectral Hilbert
sum. The dominating function is summed over the Zorn family itself; no
countability assumption on that family is needed.
-/

namespace ImbalancedChen.Part3.GenericSpectralSumDominatedConvergence20261025a

noncomputable section
open Filter
open ImbalancedChen.Part3.GenericResolventGlobalSpectralAssembly20261025a

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R)

theorem spectralSum_norm_sq (ξ : SpectralSum R hSA) :
    ‖ξ‖ ^ 2 = ∑' i, ‖ξ i‖ ^ 2 := by
  convert lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) ξ using 1 <;> norm_cast

theorem spectralSum_summable_norm_sq (ξ : SpectralSum R hSA) :
    Summable (fun i => ‖ξ i‖ ^ 2) := by
  convert (lp.memℓp ξ).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal) using 1
  norm_cast

/-- A dominated coordinate limit is a strong limit, over arbitrary filters
and with no restriction on the cardinality of the spectral index set. -/
theorem spectralSum_tendsto_of_dominated {α : Type*} {l : Filter α}
    (F : α → SpectralSum R hSA) (ξ : SpectralSum R hSA)
    (bound : SpectralIndex R hSA → ℝ) (hbound : Summable bound)
    (hcoord : ∀ i, Tendsto (fun a => F a i) l (𝓝 (ξ i)))
    (hdom : ∀ᶠ a in l, ∀ i, ‖F a i - ξ i‖ ^ 2 ≤ bound i) :
    Tendsto F l (𝓝 ξ) := by
  have hscalar : Tendsto (fun a => ∑' i, ‖F a i - ξ i‖ ^ 2) l (𝓝 0) := by
    have h := tendsto_tsum_of_dominated_convergence
      (f := fun a i => ‖F a i - ξ i‖ ^ 2)
      (g := fun _ : SpectralIndex R hSA => (0 : ℝ)) hbound
      (fun i => by
        simpa using (((hcoord i).sub tendsto_const_nhds).norm.pow 2))
      (hdom.mono fun a ha i => by simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] using ha i)
    simpa only [tsum_zero] using h
  have hsq : Tendsto (fun a => ‖F a - ξ‖ ^ 2) l (𝓝 0) := by
    simpa only [spectralSum_norm_sq, lp.coeFn_sub, Pi.sub_apply] using hscalar
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hroot := (Real.continuous_sqrt.tendsto 0).comp hsq
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hroot

end
end ImbalancedChen.Part3.GenericSpectralSumDominatedConvergence20261025a
