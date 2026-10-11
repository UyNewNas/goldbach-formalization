import ImbalancedChen.ActualRosserAtThreeLimit
import ImbalancedChen.ActualRosserCubeReduction

/-!
# Actual upper Rosser density at every fixed residual in `(0, 3]`

The literal cube-carrier identity reduces the level `N^beta` to the cutoff
`N^(beta/3)`. At that cutoff the proved residual-three limit applies. The
target-prime-deleted Euler ratio supplies the remaining factor, giving the
same raw coefficient density at the original cutoff `N^u`. All scales are
linked to the same target, and the covering cap can be arbitrary eventually.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology

private theorem eventually_cube_cap
    (u beta : ℝ) (hbetaU : beta ≤ 3 * u) (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ u ≤ (cap N : ℝ)) :
    ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (beta / 3) ≤ (cap N : ℝ) := by
  have hlarge : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      2 ≤ N := (eventually_ge_atTop 2).filter_mono inf_le_left
  filter_upwards [hcap, hlarge] with N hcapN hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  exact (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)).trans hcapN

/-- The exact raw upper coefficient ratio converges at every fixed pair
of positive exponents with `beta ≤ 3*u`. -/
theorem tendsto_actualSmallRosserPlusDensity_cube_ratio
    (u : ℝ) (hu : 0 < u) (beta : ℝ) (hbeta : 0 < beta)
    (hbetaU : beta ≤ 3 * u) (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ u ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ =>
      actualSmallRosserPlusDensity N (cap N) ((N : ℝ) ^ u) ((N : ℝ) ^ beta) /
        actualSmallEulerProduct N (cap N) ((N : ℝ) ^ u))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (2 * Real.exp Real.eulerMascheroniConstant * u / beta)) := by
  have hthird : 0 < beta / 3 := by positivity
  have hsmallcap := eventually_cube_cap u beta hbetaU cap hcap
  have hred : Tendsto (fun N : ℕ =>
      actualSmallRosserPlusDensity N (cap N) ((N : ℝ) ^ (beta / 3)) ((N : ℝ) ^ beta) /
        actualSmallEulerProduct N (cap N) ((N : ℝ) ^ (beta / 3)))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (2 * Real.exp Real.eulerMascheroniConstant / 3)) := by
    simpa only [show 3 * (beta / 3) = beta by ring] using
      tendsto_actualSmallRosserPlusDensity_at_three_ratio (beta / 3) hthird cap hsmallcap
  have heuler : Tendsto (fun N : ℕ =>
      actualSmallEulerProduct N (cap N) ((N : ℝ) ^ (beta / 3)) /
        actualSmallEulerProduct N (cap N) ((N : ℝ) ^ u))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (u / (beta / 3))) := by
    apply (tendsto_finiteSieveDensity_power_ratio hthird hu).congr'
    filter_upwards [hsmallcap, hcap] with N hsmall hbig
    rw [actualSmallEulerProduct_eq_finiteSieveDensity N (cap N) _ hsmall,
      actualSmallEulerProduct_eq_finiteSieveDensity N (cap N) _ hbig]
  have hlim := hred.mul heuler
  have hconstant : (2 * Real.exp Real.eulerMascheroniConstant / 3) * (u / (beta / 3)) =
      2 * Real.exp Real.eulerMascheroniConstant * u / beta := by
    field_simp
  rw [hconstant] at hlim
  apply hlim.congr'
  simp only [Filter.EventuallyEq, Filter.eventually_inf_principal]
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  intro hEven
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  exact (actualSmallRosserPlusDensity_power_cube_ratio N (cap N) hEven.2 hN1 hbetaU).symm

/-- With full singular-series normalization, the cutoff exponent cancels
and the same actual density has constant `4/beta`. -/
theorem tendsto_actualSmallRosserPlusDensity_cube_normalized
    (u : ℝ) (_hu : 0 < u) (beta : ℝ) (hbeta : 0 < beta)
    (hbetaU : beta ≤ 3 * u) (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ u ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ =>
      actualSmallRosserPlusDensity N (cap N) ((N : ℝ) ^ u) ((N : ℝ) ^ beta) *
        Real.log (N : ℝ) / singularSeries N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) (𝓝 (4 / beta)) := by
  have hthird : 0 < beta / 3 := by positivity
  have hsmallcap := eventually_cube_cap u beta hbetaU cap hcap
  have hlim :=
    tendsto_actualSmallRosserPlusDensity_at_three_normalized (beta / 3) hthird cap hsmallcap
  simp only [show 3 * (beta / 3) = beta by ring] at hlim
  apply hlim.congr'
  simp only [Filter.EventuallyEq, Filter.eventually_inf_principal]
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  intro _hEven
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  rw [actualSmallRosserPlusDensity_power_eq_cubeCutoff N (cap N) hN1 hbetaU]

/-- The fixed residual form has the exact ratio constant `2 exp(γ)/s`.
For `s ≤ 1` this follows from the literal cube identity as well; no definition
of a classical sieve factor below its usual domain is invoked. -/
theorem tendsto_actualSmallRosserPlusDensity_fixedResidual_ratio
    (u : ℝ) (hu : 0 < u) (s : ℝ) (hs : 0 < s) (hs3 : s ≤ 3)
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ u ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ =>
      actualSmallRosserPlusDensity N (cap N) ((N : ℝ) ^ u) ((N : ℝ) ^ (s * u)) /
        actualSmallEulerProduct N (cap N) ((N : ℝ) ^ u))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (2 * Real.exp Real.eulerMascheroniConstant / s)) := by
  have hlim := tendsto_actualSmallRosserPlusDensity_cube_ratio u hu (s * u) (mul_pos hs hu)
    (mul_le_mul_of_nonneg_right hs3 hu.le) cap hcap
  have hconstant : 2 * Real.exp Real.eulerMascheroniConstant * u / (s * u) =
      2 * Real.exp Real.eulerMascheroniConstant / s := by
    field_simp [hu.ne']
  simpa only [hconstant] using hlim

/-- Singular-series normalization at an arbitrary fixed residual in `(0,3]`. -/
theorem tendsto_actualSmallRosserPlusDensity_fixedResidual_normalized
    (u : ℝ) (hu : 0 < u) (s : ℝ) (hs : 0 < s) (hs3 : s ≤ 3)
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ u ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ =>
      actualSmallRosserPlusDensity N (cap N) ((N : ℝ) ^ u) ((N : ℝ) ^ (s * u)) *
        Real.log (N : ℝ) / singularSeries N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) (𝓝 (4 / (s * u))) :=
  tendsto_actualSmallRosserPlusDensity_cube_normalized u hu (s * u) (mul_pos hs hu)
    (mul_le_mul_of_nonneg_right hs3 hu.le) cap hcap

end

end ImbalancedChen
