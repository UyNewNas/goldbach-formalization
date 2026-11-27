import ImbalancedChen.P2LowerFiniteCellBetaCompiler
import ImbalancedChen.P2ActualResidualUniverseMass
import ImbalancedChen.ActualSmallEulerNormalization
import ImbalancedChen.NormalizedSmallRosserError

/-! A sign-sensitive lower small Rosser attachment for any real rough
coefficient bounded by one on the actual residual divisor carrier. The
target threshold is uniform in the coefficient, including jointly rounded
coefficients that depend on the marked pair and all its neighbours. -/

namespace ImbalancedChen.P3OriginalU5JointBetaReserve

noncomputable section
open scoped Classical BigOperators Topology
open Filter
open P2LowerFiniteCellRounding P2LowerFiniteCellBetaCompiler

private theorem exists_absolute_density_le_powerParameters :
    ∃ Krough : ℝ, 1 < Krough ∧
      ∀ (N cap : ℕ), Even N →
        ∀ D epsilon r : ℝ, 1 < D → 0 < epsilon → epsilon ^ 2 ≤ r →
          2 ≤ D ^ (epsilon ^ 2) → ∀ c : ℕ → ℝ, (∀ d ∈ «universe» N cap (D ^ (epsilon ^ 2)) (D ^ r), |c d| ≤ 1) →
          reciprocalTotientDensity («universe» N cap (D ^ (epsilon ^ 2)) (D ^ r))
              (fun d => |c d|) ≤
            (r / epsilon ^ 2) * (1 + Krough / (epsilon ^ 2 * Real.log D)) := by
  obtain ⟨Krough, hKrough, hsupply⟩ :=
    P2ActualResidualUniverseMass.exists_mass_logRatio_bound
  refine ⟨Krough, hKrough, ?_⟩
  intro N cap hEven D epsilon r hD hepsilon hepsilonr hw c hc
  have hmass := hsupply N cap hEven (D ^ (epsilon ^ 2)) (D ^ r) hw
    (roughPower_cutoffs hD hepsilon hepsilonr).2
  have hfinite :
      reciprocalTotientDensity («universe» N cap (D ^ (epsilon ^ 2)) (D ^ r))
          (fun d => |c d|) ≤
        P2ActualResidualUniverseMass.mass N cap (D ^ (epsilon ^ 2)) (D ^ r) := by
    unfold reciprocalTotientDensity P2ActualResidualUniverseMass.mass
    apply Finset.sum_le_sum
    intro d hd
    exact div_le_div_of_nonneg_right (hc d hd) (Nat.cast_nonneg _)
  have h := hfinite.trans hmass
  have hDpos : 0 < D := zero_lt_one.trans hD
  rw [roughPower_log_ratio hDpos (ne_of_gt (Real.log_pos hD)) (ne_of_gt hepsilon),
    Real.log_rpow hDpos] at h
  exact h

private theorem exists_beta_error_le_normalized_reserve
    (r eta epsilonMax : ℝ) (hr : 0 < r) (heta : 0 < eta)
    (hepsilonMax : 0 < epsilonMax) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 / 8 ∧
      epsilon < epsilonMax ∧ epsilon ^ 2 ≤ r ∧
      ∃ D0 : ℝ, 2 ≤ D0 ∧ ∀ D : ℝ, D0 ≤ D →
        ∀ N cap : ℕ, 0 < N → Even N →
          D ^ (epsilon ^ 2) ≤ (cap : ℝ) →
          ∀ c : ℕ → ℝ, (∀ d ∈ «universe» N cap (D ^ (epsilon ^ 2)) (D ^ r), |c d| ≤ 1) →
            let w := D ^ (epsilon ^ 2)
            let z := D ^ r
            let L := D ^ epsilon
            let V := actualSmallEulerProduct N cap w
            let roughDensity := reciprocalTotientDensity («universe» N cap w z) c
            let density := physicalDensitySum (support N cap w z)
              (smallRoughRho (actualSmallRosserSupport N cap w) («universe» N cap w z)
                c (actualSmallRosserPlus N cap w L) (actualSmallRosserMinus N cap w L))
            0 ≤ V * roughDensity - density ∧
              V * roughDensity - density ≤ eta * singularSeries N / Real.log D := by
  obtain ⟨B, _hB, hEuler⟩ := exists_actualSmallEulerProduct_le_singularSeries_log
  obtain ⟨C, K, hC, _hK, hsupply⟩ := exists_actualSmallRosser_density_sandwich
  obtain ⟨Krough, hKrough, hrough⟩ := exists_absolute_density_le_powerParameters
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
  intro D hD N cap hNpos hEven hcap c hc
  have hDs : Dsieve ≤ D := (le_max_left _ _).trans hD
  have hDt : Dscalar ≤ D := (le_max_right _ _).trans hD
  have hD1 : 1 < D := by linarith
  have hDpos : 0 < D := zero_lt_one.trans hD1
  have hlogD : 0 < Real.log D := Real.log_pos hD1
  have hV := actualSmallEulerProduct_pos N cap (D ^ (epsilon ^ 2)) hEven
  have hVbound := hEuler N cap hNpos hEven (D ^ (epsilon ^ 2))
    (hDscalar D hDt).2 hcap
  rw [Real.log_rpow hDpos] at hVbound
  have hE : 0 ≤ actualSmallRosserDensityError C K D epsilon := by
    unfold actualSmallRosserDensityError
    positivity
  have hQ : 0 ≤ (r / epsilon ^ 2) *
      (1 + Krough / (epsilon ^ 2 * Real.log D)) := by
    have : 0 < Krough := zero_lt_one.trans hKrough
    positivity
  have hs := hsieve D hDs N cap hEven
  have herror := physicalDensitySum_smallRoughRho_lower_error
    (fun _ hd => actualSmallRosserSupport_smallPrimeSupportedAt N cap _ hd)
    (fun _ hd => universe_rough N cap (D ^ (epsilon ^ 2)) (D ^ r) hd)
    c
    (actualSmallRosserMinus N cap (D ^ (epsilon ^ 2)) (D ^ epsilon))
    (actualSmallRosserPlus N cap (D ^ (epsilon ^ 2)) (D ^ epsilon))
    (V := actualSmallEulerProduct N cap (D ^ (epsilon ^ 2)))
    (delta := actualSmallEulerProduct N cap (D ^ (epsilon ^ 2)) *
      actualSmallRosserDensityError C K D epsilon)
    (by simpa only [mul_sub, mul_one, actualSmallRosserMinusDensity] using hs.1)
    hs.2.1 hs.2.2.1
    (by simpa only [mul_add, mul_one, actualSmallRosserPlusDensity] using hs.2.2.2.1)
  have hmass := hrough N cap hEven D epsilon r hD1 hepsilon hepsilonr
    (by have hwfour := (hDscalar D hDt).2; linarith) c hc
  have hscalar := (hDscalar D hDt).1
  have hnorm : 0 ≤ singularSeries N / Real.log D :=
    div_nonneg (singularSeries_pos N).le hlogD.le
  dsimp only
  refine ⟨herror.1, herror.2.trans ?_⟩
  calc
    (actualSmallEulerProduct N cap (D ^ (epsilon ^ 2)) *
        actualSmallRosserDensityError C K D epsilon) *
        reciprocalTotientDensity («universe» N cap (D ^ (epsilon ^ 2)) (D ^ r))
          (fun d => |c d|) ≤
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
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ (singularSeries N / Real.log D) * eta :=
      mul_le_mul_of_nonneg_left hscalar.le hnorm
    _ = eta * singularSeries N / Real.log D := by ring

/-- At target scale the chosen epsilon and threshold work simultaneously
for every later covering cap and every signed one-bounded coefficient. -/
theorem exists_beta_error_le_target_reserve
    (nu r eta epsilonMax : ℝ) (hnu : 0 < nu) (hr : 0 < r)
    (heta : 0 < eta) (hepsilonMax : 0 < epsilonMax) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 / 8 ∧
      epsilon < epsilonMax ∧ epsilon ^ 2 ≤ r ∧
      ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
        ∀ cap : ℕ, (N : ℝ) ^ (nu * r) ≤ (cap : ℝ) →
          ∀ c : ℕ → ℝ, (∀ d ∈ «universe» N cap ((N : ℝ) ^ (nu * epsilon ^ 2)) ((N : ℝ) ^ (nu * r)), |c d| ≤ 1) →
            let w := (N : ℝ) ^ (nu * epsilon ^ 2)
            let z := (N : ℝ) ^ (nu * r)
            let L := (N : ℝ) ^ (nu * epsilon)
            let V := actualSmallEulerProduct N cap w
            let roughDensity := reciprocalTotientDensity («universe» N cap w z) c
            let density := physicalDensitySum (support N cap w z)
              (smallRoughRho (actualSmallRosserSupport N cap w) («universe» N cap w z)
                c (actualSmallRosserPlus N cap w L) (actualSmallRosserMinus N cap w L))
            0 ≤ V * roughDensity - density ∧
              V * roughDensity - density ≤ eta * singularSeries N / Real.log (N : ℝ) := by
  obtain ⟨epsilon, hepsilon, hepsilon8, hepsilonMax', hepsilonr,
      D0, _hD0, hbound⟩ :=
    exists_beta_error_le_normalized_reserve r (eta * nu) epsilonMax hr
      (mul_pos heta hnu) hepsilonMax
  have hpower : Tendsto (fun N : ℕ => (N : ℝ) ^ nu) atTop atTop :=
    (tendsto_rpow_atTop hnu).comp tendsto_natCast_atTop_atTop
  obtain ⟨Nlarge, hNlarge⟩ := eventually_atTop.mp
    (hpower.eventually (eventually_ge_atTop D0))
  refine ⟨epsilon, hepsilon, hepsilon8, hepsilonMax', hepsilonr,
    max Nlarge 2, le_max_right _ _, ?_⟩
  intro N hN hEven cap hcap c hc
  have hNlarge' : Nlarge ≤ N := (le_max_left _ _).trans hN
  have hN2 : 2 ≤ N := (le_max_right _ _).trans hN
  have hNpos : 0 < N := by omega
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNposR : (0 : ℝ) < N := zero_lt_one.trans hN1
  have hNnonneg : (0 : ℝ) ≤ N := hNposR.le
  have hwcap : ((N : ℝ) ^ nu) ^ (epsilon ^ 2) ≤ (cap : ℝ) := by
    rw [← Real.rpow_mul hNnonneg]
    exact (Real.rpow_le_rpow_of_exponent_le hN1.le
      (mul_le_mul_of_nonneg_left hepsilonr hnu.le)).trans hcap
  have h := hbound ((N : ℝ) ^ nu) (hNlarge N hNlarge')
    N cap hNpos hEven hwcap c (by simpa only [← Real.rpow_mul hNnonneg] using hc)
  dsimp only at h ⊢
  simp only [← Real.rpow_mul hNnonneg, Real.log_rpow hNposR] at h
  have hcancel : (eta * nu) * singularSeries N / (nu * Real.log (N : ℝ)) =
      eta * singularSeries N / Real.log (N : ℝ) := by
    field_simp [ne_of_gt hnu, ne_of_gt (Real.log_pos hN1)]
  rw [hcancel] at h
  exact h

end
end ImbalancedChen.P3OriginalU5JointBetaReserve
