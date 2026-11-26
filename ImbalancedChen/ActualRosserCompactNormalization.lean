import ImbalancedChen.ActualRosserCompactLimits
import ImbalancedChen.ActualCompactEulerNormalization
import Mathlib.Topology.MetricSpace.Algebra

/-!
# Uniform singular-series normalization of the actual Rosser densities

The two factors are proved uniformly for the same actual prime carrier:
the Rosser density divided by its Euler product, and that Euler product
times `log N / C_N`. Their continuous limits can be multiplied locally
uniformly. Positivity of the actual Euler product cancels the denominator,
and compactness restores uniform convergence on the full parameter set.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology
open MathlibNt.SieveTheory

/-- On every compact subset of `u > 0, s > 1`, the actual upper density
has its singular-series-normalized limit uniformly in both parameters.
The covering cap may depend on the target and the parameter. -/
theorem tendstoUniformlyOn_actualSmallRosserPlusDensity_normalized
    (S : Set (ℝ × ℝ)) (hS : IsCompact S)
    (hparam : ∀ p ∈ S, 0 < p.1 ∧ 1 < p.2)
    (cap : ℕ → ℝ × ℝ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      ∀ p ∈ S, (N : ℝ) ^ p.1 ≤ (cap N p : ℝ)) :
    TendstoUniformlyOn
      (fun N p => actualSmallRosserPlusDensity N (cap N p) ((N : ℝ) ^ p.1)
        ((N : ℝ) ^ (p.2 * p.1)) * Real.log (N : ℝ) / singularSeries N)
      (fun p => (2 * Real.exp (-Real.eulerMascheroniConstant) / p.1) *
        suzukiContinuousUpperFactor p.2)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) S := by
  have heuler := tendstoLocallyUniformlyOn_actualSmallEulerProduct_parameter_normalized
    S (fun p hp => (hparam p hp).1) cap hcap
  have hratio := (tendstoUniformlyOn_actualSmallRosserPlusDensity_ratio
    S hS hparam cap hcap).tendstoLocallyUniformlyOn
  have hce : ContinuousOn (fun p : ℝ × ℝ =>
      2 * Real.exp (-Real.eulerMascheroniConstant) / p.1) S :=
    continuousOn_const.div continuous_fst.continuousOn (fun p hp => (hparam p hp).1.ne')
  have hcf : ContinuousOn (fun p : ℝ × ℝ => suzukiContinuousUpperFactor p.2) S :=
    continuousOn_suzukiContinuousUpperFactor.comp continuous_snd.continuousOn
      (fun p hp => (hparam p hp).2)
  have hlim := heuler.mul₀ hratio hce hcf
  apply (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hS).mp
  apply hlim.congr_inseparable
  simp only [Filter.eventually_inf_principal]
  apply Filter.Eventually.of_forall
  intro N hN p _hp
  apply Inseparable.of_eq
  simp only [Pi.mul_apply]
  field_simp [(actualSmallEulerProduct_pos N (cap N p) ((N : ℝ) ^ p.1) hN.2).ne']

/-- The lower density has the analogous uniform normalization, including
compact-set boundary points with `s = 2`. -/
theorem tendstoUniformlyOn_actualSmallRosserMinusDensity_normalized
    (S : Set (ℝ × ℝ)) (hS : IsCompact S)
    (hparam : ∀ p ∈ S, 0 < p.1 ∧ 2 ≤ p.2)
    (cap : ℕ → ℝ × ℝ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      ∀ p ∈ S, (N : ℝ) ^ p.1 ≤ (cap N p : ℝ)) :
    TendstoUniformlyOn
      (fun N p => actualSmallRosserMinusDensity N (cap N p) ((N : ℝ) ^ p.1)
        ((N : ℝ) ^ (p.2 * p.1)) * Real.log (N : ℝ) / singularSeries N)
      (fun p => (2 * Real.exp (-Real.eulerMascheroniConstant) / p.1) *
        suzukiContinuousLowerFactor p.2)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) S := by
  have heuler := tendstoLocallyUniformlyOn_actualSmallEulerProduct_parameter_normalized
    S (fun p hp => (hparam p hp).1) cap hcap
  have hratio := (tendstoUniformlyOn_actualSmallRosserMinusDensity_ratio
    S hS hparam cap hcap).tendstoLocallyUniformlyOn
  have hce : ContinuousOn (fun p : ℝ × ℝ =>
      2 * Real.exp (-Real.eulerMascheroniConstant) / p.1) S :=
    continuousOn_const.div continuous_fst.continuousOn (fun p hp => (hparam p hp).1.ne')
  have hcf : ContinuousOn (fun p : ℝ × ℝ => suzukiContinuousLowerFactor p.2) S :=
    continuousOn_suzukiContinuousLowerFactor.comp continuous_snd.continuousOn
      (fun p hp => (hparam p hp).2)
  have hlim := heuler.mul₀ hratio hce hcf
  apply (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hS).mp
  apply hlim.congr_inseparable
  simp only [Filter.eventually_inf_principal]
  apply Filter.Eventually.of_forall
  intro N hN p _hp
  apply Inseparable.of_eq
  simp only [Pi.mul_apply]
  field_simp [(actualSmallEulerProduct_pos N (cap N p) ((N : ℝ) ^ p.1) hN.2).ne']

end

end ImbalancedChen
