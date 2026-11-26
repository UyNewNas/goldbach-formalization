import ImbalancedChen.SmallRosserErrorLimit

/-!
# Scalar absorption at the singular-series density scale

The absolute rough mass costs a reciprocal square of the small parameter.
Passing from the small Euler product to the singular-series-over-log scale
costs a second reciprocal square. The resulting fourth-power loss is still
absorbed by the actual exponential small-Rosser error. The chosen parameter
can satisfy any additional fixed positive upper bound before the large
scale grows. These are scalar statements, with no assumed sieve estimate.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology

/-- The exponential floor absorbs the full fourth-power parameter cost.
The constants B and C may be arbitrary real numbers. An extra upper bound
on epsilon permits later fixed support and policy constraints. -/
theorem exists_normalizedSmallRosser_epsilon_absorbing
    (B C r eta epsilonMax : ℝ) (hr : 0 < r) (heta : 0 < eta)
    (hepsilonMax : 0 < epsilonMax) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 / 8 ∧ epsilon < epsilonMax ∧
      epsilon ^ 2 ≤ r ∧
      (B / epsilon ^ 2) * (C * Real.exp (-(1 / epsilon))) *
        (r / epsilon ^ 2) < eta := by
  have hlimit : Tendsto
      (fun t : ℝ => (B * C * r) * (t ^ 4 * Real.exp (-t)))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 4).const_mul (B * C * r)
  have hsmall : ∀ᶠ t : ℝ in atTop,
      (B * C * r) * (t ^ 4 * Real.exp (-t)) < eta :=
    (tendsto_order.1 hlimit).2 eta heta
  obtain ⟨t, htSmall, htEight, htR, htMax⟩ :=
    (hsmall.and ((eventually_gt_atTop (8 : ℝ)).and
      ((eventually_ge_atTop (1 / r)).and
        (eventually_gt_atTop (1 / epsilonMax))))).exists
  have ht : 0 < t := by linarith
  have hepsilon : 0 < 1 / t := one_div_pos.mpr ht
  have hepsilonEight : 1 / t < (1 / 8 : ℝ) :=
    one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 8) htEight
  have hepsilonMax' : 1 / t < epsilonMax := by
    simpa only [one_div_one_div] using
      one_div_lt_one_div_of_lt (one_div_pos.mpr hepsilonMax) htMax
  have hepsilonR : 1 / t ≤ r := by
    apply (div_le_iff₀ ht).mpr
    have hrt : 1 ≤ t * r := (div_le_iff₀ hr).mp htR
    nlinarith
  refine ⟨1 / t, hepsilon, hepsilonEight, hepsilonMax', ?_, ?_⟩
  · nlinarith
  · have heq : (B / (1 / t) ^ 2) * (C * Real.exp (-(1 / (1 / t)))) *
          (r / (1 / t) ^ 2) = (B * C * r) * (t ^ 4 * Real.exp (-t)) := by
      rw [one_div_one_div]
      field_simp
    rw [heq]
    exact htSmall

/-- For fixed positive epsilon the normalized actual density error tends
to its fourth-power exponential floor. The rough-product constant remains
independent of the small-Rosser constant K. -/
theorem tendsto_normalizedSmallRosserDensityError_mul_roughMassEnvelope
    (B C K Krough r epsilon : ℝ) (hepsilon : 0 < epsilon) :
    Tendsto
      (fun D : ℝ => (B / epsilon ^ 2) *
        actualSmallRosserDensityError C K D epsilon * (r / epsilon ^ 2) *
        (1 + Krough / (epsilon ^ 2 * Real.log D)))
      atTop (𝓝 ((B / epsilon ^ 2) * (C * Real.exp (-(1 / epsilon))) *
        (r / epsilon ^ 2))) := by
  simpa only [mul_assoc] using
    (tendsto_actualSmallRosserDensityError_mul_roughMassEnvelope
      C K Krough r epsilon hepsilon).const_mul (B / epsilon ^ 2)

/-- The literal small cutoff eventually passes the finite Euler-product
threshold, after epsilon has been fixed. -/
theorem eventually_four_le_smallRosserPower
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ D : ℝ in atTop, 4 ≤ D ^ (epsilon ^ 2) :=
  (tendsto_rpow_atTop (sq_pos_of_pos hepsilon)).eventually
    (eventually_ge_atTop (4 : ℝ))

end

end ImbalancedChen
