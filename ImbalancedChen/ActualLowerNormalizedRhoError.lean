import ImbalancedChen.ActualLowerSmallRoughAttachment
import ImbalancedChen.ActualSmallEulerNormalization
import ImbalancedChen.EvenRoughAbsoluteDensity
import ImbalancedChen.NormalizedSmallRosserError

/-!
# The actual lower physical-weight attachment loss at the manuscript scale

For the same even-first-exit lower coefficient, the small Euler product and absolute rough mass are both bounded by proved
estimates. The resulting fourth-power epsilon loss is absorbed by a direct
choice of epsilon before the large threshold. The threshold is uniform in
the nonzero even target, covering cap and retained rough policy.

This controls the nonnegative loss from the small-weight attachment for the same actual rho
constructed from a fixed even-first-exit retention policy and the small Rosser weights.
It does not instantiate the manuscript's boxed compiler, bound the signed
rough main term, or supply the distribution theorem or the final sharp K.
The real-D theorem allows a truncated rough cap, whereas the target-scale
theorem requires the cap to cover the entire rough cutoff.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology

/-- The actual attachment error is arbitrarily small on the `C_N/log D`
scale. The caller can require epsilon to be below any earlier positive
bound, before any target, cap or rough retention policy is supplied. -/
theorem exists_actualLowerSmallRoughRho_density_error_le_normalized_reserve
    (r eta epsilonMax : ℝ) (hr : 0 < r) (heta : 0 < eta)
    (hepsilonMax : 0 < epsilonMax) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 / 8 ∧
      epsilon < epsilonMax ∧ epsilon ^ 2 ≤ r ∧
      ∃ D₀ : ℝ, 2 ≤ D₀ ∧ ∀ D : ℝ, D₀ ≤ D →
        ∀ N cap : ℕ, 0 < N → Even N →
          D ^ (epsilon ^ 2) ≤ (cap : ℝ) → ∀ retainEven : List ℕ → Bool,
            let w := D ^ (epsilon ^ 2)
            let z := D ^ r
            let L := D ^ epsilon
            let V := actualSmallEulerProduct N cap w
            let S := fixedEvenRoughSupport retainEven N cap w z
            let c := fixedEvenRoughCoefficient retainEven N cap w z
            let density := physicalDensitySum
              (actualLowerSmallRoughModuli retainEven N cap w z)
              (actualLowerSmallRoughRho retainEven N cap w z L)
            0 ≤ V * reciprocalTotientDensity S c - density ∧
              V * reciprocalTotientDensity S c - density ≤
                eta * singularSeries N / Real.log D := by
  obtain ⟨B, _hB, hEuler⟩ := exists_actualSmallEulerProduct_le_singularSeries_log
  obtain ⟨C, K, hC, _hK, hsupply⟩ := exists_actualLowerSmallRoughRho_density_error
  obtain ⟨Krough, hKrough, hrough⟩ :=
    exists_fixedEvenRoughAbsoluteDensity_le_powerParameters
  obtain ⟨epsilon, hepsilon, hepsilon8, hepsilonMax', hepsilonr, hfloor⟩ :=
    exists_normalizedSmallRosser_epsilon_absorbing B C r eta epsilonMax
      hr heta hepsilonMax
  have hlimit := tendsto_normalizedSmallRosserDensityError_mul_roughMassEnvelope
    B C K Krough r epsilon hepsilon
  have hsmall : ∀ᶠ D : ℝ in atTop,
      (B / epsilon ^ 2) * actualSmallRosserDensityError C K D epsilon *
        (r / epsilon ^ 2) * (1 + Krough / (epsilon ^ 2 * Real.log D)) < eta :=
    (tendsto_order.1 hlimit).2 eta hfloor
  obtain ⟨Dscalar, hDscalar⟩ := eventually_atTop.mp
    (hsmall.and (eventually_four_le_smallRosserPower epsilon hepsilon))
  obtain ⟨Dsieve, hDsieve, hsieve⟩ := hsupply epsilon hepsilon hepsilon8
  refine ⟨epsilon, hepsilon, hepsilon8, hepsilonMax', hepsilonr,
    max Dsieve Dscalar, hDsieve.trans (le_max_left _ _), ?_⟩
  intro D hD N cap hNpos hN hcap retainEven
  have hDs : Dsieve ≤ D := (le_max_left _ _).trans hD
  have hDt : Dscalar ≤ D := (le_max_right _ _).trans hD
  have hD1 : 1 < D := by linarith
  have hDpos : 0 < D := by linarith
  have hlogD : 0 < Real.log D := Real.log_pos hD1
  have hV := actualSmallEulerProduct_pos N cap (D ^ (epsilon ^ 2)) hN
  have hVbound := hEuler N cap hNpos hN (D ^ (epsilon ^ 2))
    (hDscalar D hDt).2 hcap
  rw [Real.log_rpow hDpos] at hVbound
  have hE : 0 ≤ actualSmallRosserDensityError C K D epsilon := by
    unfold actualSmallRosserDensityError
    positivity
  have hQ : 0 ≤ (r / epsilon ^ 2) *
      (1 + Krough / (epsilon ^ 2 * Real.log D)) := by
    have : 0 < Krough := by linarith
    positivity
  have herror := hsieve D hDs N cap hN retainEven (D ^ r)
  have hmass := hrough retainEven N cap hN D epsilon r hD1 hepsilon hepsilonr
    (by have hwfour := (hDscalar D hDt).2; linarith)
  have hscalar := (hDscalar D hDt).1
  have hnorm : 0 ≤ singularSeries N / Real.log D :=
    div_nonneg (singularSeries_pos N).le hlogD.le
  dsimp only at herror ⊢
  refine ⟨herror.1, herror.2.trans ?_⟩
  calc
    (actualSmallEulerProduct N cap (D ^ (epsilon ^ 2)) *
        actualSmallRosserDensityError C K D epsilon) *
        reciprocalTotientDensity
          (fixedEvenRoughSupport retainEven N cap (D ^ (epsilon ^ 2)) (D ^ r))
          (fun d => |fixedEvenRoughCoefficient retainEven N cap
            (D ^ (epsilon ^ 2)) (D ^ r) d|) ≤
      (actualSmallEulerProduct N cap (D ^ (epsilon ^ 2)) *
        actualSmallRosserDensityError C K D epsilon) *
          ((r / epsilon ^ 2) * (1 + Krough / (epsilon ^ 2 * Real.log D))) :=
      mul_le_mul_of_nonneg_left hmass (mul_nonneg hV.le hE)
    _ = actualSmallEulerProduct N cap (D ^ (epsilon ^ 2)) *
        (actualSmallRosserDensityError C K D epsilon *
          ((r / epsilon ^ 2) * (1 + Krough / (epsilon ^ 2 * Real.log D)))) := by ring
    _ ≤ (B * singularSeries N / (epsilon ^ 2 * Real.log D)) *
        (actualSmallRosserDensityError C K D epsilon *
          ((r / epsilon ^ 2) * (1 + Krough / (epsilon ^ 2 * Real.log D)))) :=
      mul_le_mul_of_nonneg_right hVbound (mul_nonneg hE hQ)
    _ = (singularSeries N / Real.log D) *
        ((B / epsilon ^ 2) * actualSmallRosserDensityError C K D epsilon *
          (r / epsilon ^ 2) * (1 + Krough / (epsilon ^ 2 * Real.log D))) := by
      field_simp
    _ ≤ (singularSeries N / Real.log D) * eta :=
      mul_le_mul_of_nonneg_left hscalar.le hnorm
    _ = eta * singularSeries N / Real.log D := by ring

/-- At `D=N^nu`, the same error has an arbitrary reserve on the actual
manuscript scale `C_N/log N`. The cap covers the full rough cutoff, so it
also covers the small cutoff required by the proved normalization bound.
The same epsilon and natural threshold work for all later even targets,
covering caps and retention policies. -/
theorem exists_actualLowerSmallRoughRho_density_error_le_target_reserve
    (nu r eta epsilonMax : ℝ) (hnu : 0 < nu) (hr : 0 < r)
    (heta : 0 < eta) (hepsilonMax : 0 < epsilonMax) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 / 8 ∧
      epsilon < epsilonMax ∧ epsilon ^ 2 ≤ r ∧
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
        ∀ cap : ℕ, (N : ℝ) ^ (nu * r) ≤ (cap : ℝ) →
          ∀ retainEven : List ℕ → Bool,
            let w := (N : ℝ) ^ (nu * epsilon ^ 2)
            let z := (N : ℝ) ^ (nu * r)
            let L := (N : ℝ) ^ (nu * epsilon)
            let V := actualSmallEulerProduct N cap w
            let S := fixedEvenRoughSupport retainEven N cap w z
            let c := fixedEvenRoughCoefficient retainEven N cap w z
            let density := physicalDensitySum
              (actualLowerSmallRoughModuli retainEven N cap w z)
              (actualLowerSmallRoughRho retainEven N cap w z L)
            0 ≤ V * reciprocalTotientDensity S c - density ∧
              V * reciprocalTotientDensity S c - density ≤
                eta * singularSeries N / Real.log (N : ℝ) := by
  obtain ⟨epsilon, hepsilon, hepsilon8, hepsilonMax', hepsilonr,
      D₀, _hD₀, hbound⟩ :=
    exists_actualLowerSmallRoughRho_density_error_le_normalized_reserve
      r (eta * nu) epsilonMax hr (mul_pos heta hnu) hepsilonMax
  have hpower : Tendsto (fun N : ℕ => (N : ℝ) ^ nu) atTop atTop :=
    (tendsto_rpow_atTop hnu).comp tendsto_natCast_atTop_atTop
  obtain ⟨Nlarge, hNlarge⟩ := eventually_atTop.mp
    (hpower.eventually (eventually_ge_atTop D₀))
  refine ⟨epsilon, hepsilon, hepsilon8, hepsilonMax', hepsilonr,
    max Nlarge 2, le_max_right _ _, ?_⟩
  intro N hN hEven cap hcap retainEven
  have hNlarge' : Nlarge ≤ N := (le_max_left _ _).trans hN
  have hN2 : 2 ≤ N := (le_max_right _ _).trans hN
  have hNpos : 0 < N := by omega
  have hNposR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hNnonneg : (0 : ℝ) ≤ N := hNposR.le
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hwcap : ((N : ℝ) ^ nu) ^ (epsilon ^ 2) ≤ (cap : ℝ) := by
    rw [← Real.rpow_mul hNnonneg]
    exact (Real.rpow_le_rpow_of_exponent_le hN1
      (mul_le_mul_of_nonneg_left hepsilonr hnu.le)).trans hcap
  have h := hbound ((N : ℝ) ^ nu) (hNlarge N hNlarge')
    N cap hNpos hEven hwcap retainEven
  dsimp only at h ⊢
  simp only [← Real.rpow_mul hNnonneg, Real.log_rpow hNposR] at h
  have hcancel : (eta * nu) * singularSeries N / (nu * Real.log (N : ℝ)) =
      eta * singularSeries N / Real.log (N : ℝ) := by
    field_simp [ne_of_gt hnu]
  rw [hcancel] at h
  exact h

end

end ImbalancedChen
