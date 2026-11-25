import ImbalancedChen.P2LowerFiniteCellBetaCompiler
import ImbalancedChen.P2ActualResidualUniverseMass
import ImbalancedChen.ActualSmallEulerNormalization
import ImbalancedChen.NormalizedSmallRosserError

/-!
# Absolute mass and beta reserve for the actual rounded lower output

SOURCE ONLY / UNCOMPILED / NO KERNEL ACCEPTANCE.

The full residual Euler mass and its Mertens bound are already supplied by
P2ActualResidualUniverseMass. The only new mass comparison is the finite
sum consequence of the existing rounded coefficient's absolute one-bound.
The existing actual beta sandwich, Euler normalization and scalar absorption
then pay the attachment error of this SAME rounded output.

The small parameter is chosen before the threshold, target, cap, policy and
fine mesh. The fine mesh need not be positive for these density statements.
No small roundingLoss, raw/rounded identity, raw density evaluation, support
cap, whole-word tensor, admission or PP conclusion is assumed or obtained.
-/

namespace ImbalancedChen.P3OriginalU5RoundedBetaReserve

noncomputable section
open scoped Classical BigOperators Topology
open Filter
open P2LowerFiniteCellRounding P2LowerFiniteCellBetaCompiler

/-- The actual rounded absolute mass is bounded by the already-proved
complete residual mass. No retained-policy representation is required. -/
theorem exists_absolute_density_le_powerParameters :
    ∃ Krough : ℝ, 1 < Krough ∧
      ∀ (keep : List ℕ → Bool) (N cap : ℕ), Even N →
        ∀ D epsilon r : ℝ, 1 < D → 0 < epsilon → epsilon ^ 2 ≤ r →
          2 ≤ D ^ (epsilon ^ 2) → ∀ tau : ℝ,
          reciprocalTotientDensity («universe» N cap (D ^ (epsilon ^ 2)) (D ^ r))
              (fun d => |coefficient keep N cap (D ^ (epsilon ^ 2)) (D ^ r) tau d|) ≤
            (r / epsilon ^ 2) * (1 + Krough / (epsilon ^ 2 * Real.log D)) := by
  obtain ⟨Krough, hKrough, hsupply⟩ :=
    P2ActualResidualUniverseMass.exists_mass_logRatio_bound
  refine ⟨Krough, hKrough, ?_⟩
  intro keep N cap hEven D epsilon r hD hepsilon hepsilonr hw tau
  have hmass := hsupply N cap hEven (D ^ (epsilon ^ 2)) (D ^ r) hw
    (roughPower_cutoffs hD hepsilon hepsilonr).2
  have hfinite :
      reciprocalTotientDensity («universe» N cap (D ^ (epsilon ^ 2)) (D ^ r))
          (fun d => |coefficient keep N cap (D ^ (epsilon ^ 2)) (D ^ r) tau d|) ≤
        P2ActualResidualUniverseMass.mass N cap (D ^ (epsilon ^ 2)) (D ^ r) := by
    unfold reciprocalTotientDensity P2ActualResidualUniverseMass.mass
    apply Finset.sum_le_sum
    intro d _
    exact div_le_div_of_nonneg_right
      (coefficient_abs_le_one keep N cap (D ^ (epsilon ^ 2)) (D ^ r) tau d)
      (Nat.cast_nonneg _)
  have h := hfinite.trans hmass
  have hDpos : 0 < D := zero_lt_one.trans hD
  rw [roughPower_log_ratio hDpos (ne_of_gt (Real.log_pos hD)) (ne_of_gt hepsilon),
    Real.log_rpow hDpos] at h
  exact h

/-- The beta attachment loss of the actual rounded coefficient fits any
positive reserve on the singular-series/log D scale. All analytic suppliers
are reused; no output error bound is a premise. -/
theorem exists_beta_error_le_normalized_reserve
    (r eta epsilonMax : ℝ) (hr : 0 < r) (heta : 0 < eta)
    (hepsilonMax : 0 < epsilonMax) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 / 8 ∧
      epsilon < epsilonMax ∧ epsilon ^ 2 ≤ r ∧
      ∃ D0 : ℝ, 2 ≤ D0 ∧ ∀ D : ℝ, D0 ≤ D →
        ∀ N cap : ℕ, 0 < N → Even N →
          D ^ (epsilon ^ 2) ≤ (cap : ℝ) →
          ∀ (keep : List ℕ → Bool) (tau : ℝ),
            let w := D ^ (epsilon ^ 2)
            let z := D ^ r
            let L := D ^ epsilon
            let V := actualSmallEulerProduct N cap w
            let roughDensity := reciprocalTotientDensity («universe» N cap w z)
              (coefficient keep N cap w z tau)
            let density := physicalDensitySum (support N cap w z)
              (rho keep N cap w z tau L)
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
  intro D hD N cap hNpos hEven hcap keep tau
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
    (coefficient keep N cap (D ^ (epsilon ^ 2)) (D ^ r) tau)
    (actualSmallRosserMinus N cap (D ^ (epsilon ^ 2)) (D ^ epsilon))
    (actualSmallRosserPlus N cap (D ^ (epsilon ^ 2)) (D ^ epsilon))
    (V := actualSmallEulerProduct N cap (D ^ (epsilon ^ 2)))
    (delta := actualSmallEulerProduct N cap (D ^ (epsilon ^ 2)) *
      actualSmallRosserDensityError C K D epsilon)
    (by simpa only [mul_sub, mul_one, actualSmallRosserMinusDensity] using hs.1)
    hs.2.1 hs.2.2.1
    (by simpa only [mul_add, mul_one, actualSmallRosserPlusDensity] using hs.2.2.2.1)
  have hmass := hrough keep N cap hEven D epsilon r hD1 hepsilon hepsilonr
    (by have hwfour := (hDscalar D hDt).2; linarith) tau
  have hscalar := (hDscalar D hDt).1
  have hnorm : 0 ≤ singularSeries N / Real.log D :=
    div_nonneg (singularSeries_pos N).le hlogD.le
  dsimp only
  refine ⟨herror.1, herror.2.trans ?_⟩
  calc
    (actualSmallEulerProduct N cap (D ^ (epsilon ^ 2)) *
        actualSmallRosserDensityError C K D epsilon) *
        reciprocalTotientDensity («universe» N cap (D ^ (epsilon ^ 2)) (D ^ r))
          (fun d => |coefficient keep N cap (D ^ (epsilon ^ 2)) (D ^ r) tau d|) ≤
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

/-- At D=N^nu, the same output error is paid on the target scale, with
epsilon chosen before every later N, covering cap, policy and fine mesh.
For original U5, nu=34/125 and r=417/1360 give its unchanged cutoff. -/
theorem exists_beta_error_le_target_reserve
    (nu r eta epsilonMax : ℝ) (hnu : 0 < nu) (hr : 0 < r)
    (heta : 0 < eta) (hepsilonMax : 0 < epsilonMax) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 / 8 ∧
      epsilon < epsilonMax ∧ epsilon ^ 2 ≤ r ∧
      ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
        ∀ cap : ℕ, (N : ℝ) ^ (nu * r) ≤ (cap : ℝ) →
          ∀ (keep : List ℕ → Bool) (tau : ℝ),
            let w := (N : ℝ) ^ (nu * epsilon ^ 2)
            let z := (N : ℝ) ^ (nu * r)
            let L := (N : ℝ) ^ (nu * epsilon)
            let V := actualSmallEulerProduct N cap w
            let roughDensity := reciprocalTotientDensity («universe» N cap w z)
              (coefficient keep N cap w z tau)
            let density := physicalDensitySum (support N cap w z)
              (rho keep N cap w z tau L)
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
  intro N hN hEven cap hcap keep tau
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
    N cap hNpos hEven hwcap keep tau
  dsimp only at h ⊢
  simp only [← Real.rpow_mul hNnonneg, Real.log_rpow hNposR] at h
  have hcancel : (eta * nu) * singularSeries N / (nu * Real.log (N : ℝ)) =
      eta * singularSeries N / Real.log (N : ℝ) := by
    field_simp [ne_of_gt hnu, ne_of_gt (Real.log_pos hN1)]
  rw [hcancel] at h
  exact h

end
end ImbalancedChen.P3OriginalU5RoundedBetaReserve
