import ImbalancedChen.ActualExtendedThirdCompactPolicySaving
import ImbalancedChen.ActualExtendedThirdInitialCutoff

/-!
# The actual signed third-policy correction has its proved integral limit

The first term is the literal reciprocal-totient sum of the original
upper policy's signed Mobius coefficient on its actual retained support.
The subtracted term is the same initial policy's ordinary plus density at
its exact floor-grid cutoff. The ambient cap remains N, with w=0 and
z=N^rho. Its old level is theta-2e; no cube test or arithmetic wall is
removed.

The finite same-policy identity and the original-cap residual limit
prove convergence. Choosing a positive cutoff, buffer, and fine mesh
before the target gives arbitrary accuracy against the unbuffered third
functional. This does not evaluate the initial baseline, attach a
positive presieve, pay progression errors, or identify the complete
fourth/fifth policy or its final numerical constant.
-/

namespace ImbalancedChen

noncomputable section

open Set Filter Topology
open scoped Classical BigOperators

/-- The original signed coefficient, with its exact initial-policy
baseline subtracted, has the actual retained-cell integral as its limit.
No arithmetic mean or signed-density estimate is a premise. -/
theorem tendsto_actualExtendedThirdCompactSignedDensityCorrection {e h : ℝ} {m : ℕ}
    (hh : 0 < h) (he0 : 0 < e) (he : e ≤ 1 / 384)
    (hmesh : actualExtendedThirdDyadicStep m ≤ e / 2) :
    Tendsto (fun N : ℕ =>
      (reciprocalTotientDensity
          (fixedRoughSupport (actualExtendedThirdCompactUpperPolicy e h m N false)
            N N 0 ((N : ℝ) ^ thirdPrefixRho))
          (fixedRoughCoefficient (actualExtendedThirdCompactUpperPolicy e h m N false)
            N N 0 ((N : ℝ) ^ thirdPrefixRho)) -
        actualSmallRosserPlusDensity N N
          ((N : ℝ) ^ actualExtendedThirdInitialStopExponent e m)
          ((N : ℝ) ^ (thirdPrefixTheta - 2 * e))) *
        Real.log (N : ℝ) / singularSeries N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (actualExtendedThirdCompactCellFunctional e h m)) := by
  have hlim := tendsto_actualExtendedThirdCompactResidualDensitySum hh he0.le he m
  apply hlim.congr'
  have hlarge : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}, 1 < N :=
    (eventually_gt_atTop 1).filter_mono inf_le_left
  filter_upwards [hlarge] with N hN
  rw [actualExtendedThirdCompactRoughDensity_eq_policy,
    ← actualExtendedThirdInitialPolicy_eq_actualPlus he0 he hN m]
  exact actualExtendedThirdCompactPolicySaving hN hh he0 he hmesh

/-- One legal finite policy is fixed before N. Its literal normalized
signed correction approximates the original unbuffered third functional
to arbitrary accuracy on all sufficiently large positive even targets. -/
theorem exists_actualExtendedThirdCompactSignedDensityCorrection_approx_ideal
    {ε : ℝ} (hε : 0 < ε) :
    ∃ h : ℝ, 0 < h ∧ ∃ e : ℝ, 0 < e ∧ e ≤ 1 / 384 ∧ ∃ m : ℕ,
      actualExtendedThirdDyadicStep m ≤ e / 2 ∧
        ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
          |(reciprocalTotientDensity
              (fixedRoughSupport (actualExtendedThirdCompactUpperPolicy e h m N false)
                N N 0 ((N : ℝ) ^ thirdPrefixRho))
              (fixedRoughCoefficient (actualExtendedThirdCompactUpperPolicy e h m N false)
                N N 0 ((N : ℝ) ^ thirdPrefixRho)) -
            actualSmallRosserPlusDensity N N
              ((N : ℝ) ^ actualExtendedThirdInitialStopExponent e m)
              ((N : ℝ) ^ (thirdPrefixTheta - 2 * e))) *
            Real.log (N : ℝ) / singularSeries N -
              actualExtendedThirdIdealFunctional| ≤ ε := by
  obtain ⟨h, hh, e₀, he₀, he₀cap, m₀, hb⟩ :=
    actualExtendedThirdCompactCellFunctional_uniform_approx (half_pos hε)
  have hepos : 0 < e₀ / 2 := half_pos he₀
  have hecap : e₀ / 2 ≤ 1 / 384 := (by linarith : e₀ / 2 ≤ e₀).trans he₀cap
  obtain ⟨m₁, hm₁⟩ := Filter.eventually_atTop.mp
    (tendsto_actualExtendedThirdDyadicStep.eventually (gt_mem_nhds (half_pos hepos)))
  let m : ℕ := max m₀ m₁
  have hmesh : actualExtendedThirdDyadicStep m ≤ (e₀ / 2) / 2 :=
    (hm₁ m (le_max_right m₀ m₁)).le
  have hcont : |actualExtendedThirdCompactCellFunctional (e₀ / 2) h m -
      actualExtendedThirdIdealFunctional| ≤ ε / 2 :=
    hb (e₀ / 2) hepos.le (by linarith) m (le_max_left m₀ m₁)
  have hArith : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      |(reciprocalTotientDensity
          (fixedRoughSupport (actualExtendedThirdCompactUpperPolicy (e₀ / 2) h m N false)
            N N 0 ((N : ℝ) ^ thirdPrefixRho))
          (fixedRoughCoefficient (actualExtendedThirdCompactUpperPolicy (e₀ / 2) h m N false)
            N N 0 ((N : ℝ) ^ thirdPrefixRho)) -
        actualSmallRosserPlusDensity N N
          ((N : ℝ) ^ actualExtendedThirdInitialStopExponent (e₀ / 2) m)
          ((N : ℝ) ^ (thirdPrefixTheta - 2 * (e₀ / 2)))) *
        Real.log (N : ℝ) / singularSeries N -
          actualExtendedThirdCompactCellFunctional (e₀ / 2) h m| < ε / 2 := by
    simpa only [Real.dist_eq] using Metric.tendsto_nhds.mp
      (tendsto_actualExtendedThirdCompactSignedDensityCorrection hh hepos hecap hmesh)
        (ε / 2) (half_pos hε)
  refine ⟨h, hh, e₀ / 2, hepos, hecap, m, hmesh, ?_⟩
  filter_upwards [hArith] with N hN
  apply (abs_sub_le _ (actualExtendedThirdCompactCellFunctional (e₀ / 2) h m) _).trans
  exact (add_le_add hN.le hcont).trans (by linarith)

end

end ImbalancedChen
