import ImbalancedChen.UniformPowerEulerNormalization
import ImbalancedChen.RosserCompactParameterBounds

/-!
# The actual Euler normalizer on compact parameter sets

The first coordinate is the positive prime-cutoff exponent. The second
coordinate is unrestricted here. Caps can vary with both the target and the
parameter, and need only eventually cover all cutoffs simultaneously. The
finite Euler products need not be continuous in the parameter.
-/

namespace ImbalancedChen

noncomputable section

open Set Filter Topology

/-- An arbitrary compact positive-exponent parameter set has one Euler
normalization threshold, valid for every covering cap after that threshold. -/
theorem exists_actualSmallEulerProduct_compact_uniform_threshold
    (S : Set (ℝ × ℝ)) (hS : IsCompact S) (hpos : ∀ p ∈ S, 0 < p.1)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ p ∈ S, ∀ cap : ℕ, (N : ℝ) ^ p.1 ≤ (cap : ℝ) →
        |actualSmallEulerProduct N cap ((N : ℝ) ^ p.1) * Real.log (N : ℝ) /
          singularSeries N - 2 * Real.exp (-Real.eulerMascheroniConstant) / p.1| < eta := by
  obtain ⟨a, b, ha, hab⟩ := exists_compact_positive_first_coordinate_bounds S hS hpos
  obtain ⟨N0, hN0, hbound⟩ := exists_actualSmallEulerProduct_power_uniform_threshold
    a b eta ha heta
  refine ⟨N0, hN0, ?_⟩
  intro N hN hEven p hp cap hcap
  exact hbound N hN hEven p.1 (hab p hp) cap hcap

/-- Local uniformity survives the first-coordinate substitution and the
eventually uniform replacement by the actual finite prime carrier. -/
theorem tendstoLocallyUniformlyOn_actualSmallEulerProduct_parameter_normalized
    (S : Set (ℝ × ℝ)) (hpos : ∀ p ∈ S, 0 < p.1)
    (cap : ℕ → ℝ × ℝ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      ∀ p ∈ S, (N : ℝ) ^ p.1 ≤ (cap N p : ℝ)) :
    TendstoLocallyUniformlyOn
      (fun N p => actualSmallEulerProduct N (cap N p) ((N : ℝ) ^ p.1) *
        Real.log (N : ℝ) / singularSeries N)
      (fun p => 2 * Real.exp (-Real.eulerMascheroniConstant) / p.1)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) S := by
  have hbase := tendstoLocallyUniformlyOn_finiteSieveDensity_power_normalized.comp
    Prod.fst (fun p hp => hpos p hp) continuous_fst.continuousOn
  apply hbase.congr_inseparable
  filter_upwards [hcap] with N hN
  intro p hp
  apply Inseparable.of_eq
  simp only [Function.comp_apply]
  rw [actualSmallEulerProduct_eq_finiteSieveDensity N (cap N p)
    ((N : ℝ) ^ p.1) (hN p hp)]

/-- Uniform convergence on every compact positive-exponent parameter set,
with an arbitrary cap depending on both the target and the parameter. -/
theorem tendstoUniformlyOn_actualSmallEulerProduct_compact_normalized
    (S : Set (ℝ × ℝ)) (hS : IsCompact S) (hpos : ∀ p ∈ S, 0 < p.1)
    (cap : ℕ → ℝ × ℝ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      ∀ p ∈ S, (N : ℝ) ^ p.1 ≤ (cap N p : ℝ)) :
    TendstoUniformlyOn
      (fun N p => actualSmallEulerProduct N (cap N p) ((N : ℝ) ^ p.1) *
        Real.log (N : ℝ) / singularSeries N)
      (fun p => 2 * Real.exp (-Real.eulerMascheroniConstant) / p.1)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) S :=
  (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hS).mp
    (tendstoLocallyUniformlyOn_actualSmallEulerProduct_parameter_normalized S hpos cap hcap)

end

end ImbalancedChen
