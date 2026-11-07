import ImbalancedChen.ActualUpperDensityAssembly
import ImbalancedChen.RealPhysicalUpperWeightBridge
import ImbalancedChen.RealHalfProductMassSuppliers
import ImbalancedChen.PowerErrorBudget

/-!
# Conditional same-weight assembly of the real bad-semiprime upper count

The ordered source mass is supplied by the proved PNT/Mertens limit and
has coefficient `log (1 / b)`. The natural ceiling of the sieve cutoff and
the manuscript's literal lower cutoff have proved negligible costs on the
same `singularNormalization` scale.

The remaining hypotheses concern one precision-indexed family
`Q delta N, rho delta N`: its pointwise majorant, its normalized density,
its exact coprime correction and its signed distribution error. One common
precision is chosen for all four uses before the target grows; the weight
may change when another precision is requested. These analytic hypotheses
are not proved by this module. In particular a distribution theorem for a smooth
outer source is not silently identified with the displayed exact source
error. The complete legal smoothing transfer remains a separate task.

The real imbalance exponent is fixed before every tolerance and target
threshold. It is distinct from `sieveExponent`, which only determines the
strict small-prime cap. No lower Chen-count premise occurs.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology

/-- Exact conditional `hUpper` for one actual coefficient at each chosen
precision. The
source-mass limit and both endpoint absorptions are proved suppliers;
the four displayed same-weight hypotheses must still be instantiated by
the current manuscript's legal upper construction. -/
theorem eventually_RealB_le_currentK_log_of_same_rho_inputs
    {b kappa sieveExponent : ℝ}
    (hb : 0 < b) (hb1 : b < 1) (hkappa : 0 < kappa)
    (hsieve : sieveExponent < 1)
    (Q : ℝ → ℕ → Finset ℕ) (rho : ℝ → ℕ → ℕ → ℝ)
    (hmajor : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N → ∀ n : ℕ,
      (if Nat.Coprime n (sieveProduct N (Nat.ceil ((N : ℝ) ^ sieveExponent)))
        then (1 : ℝ) else 0) ≤ physicalDivisorSum (Q delta N) (rho delta N) n)
    (hdensity : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      physicalDensitySum (Q delta N) (rho delta N) ≤
        (currentK + delta) * (singularSeries N / Real.log (N : ℝ)))
    (hcoprime : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      |realPhysicalCoprimeCorrection b N (manuscriptHalfProductCutoff kappa N)
        (Q delta N) (rho delta N)| ≤ delta * singularNormalization N)
    (hdistribution : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      |realPhysicalDistributionError b N (manuscriptHalfProductCutoff kappa N)
        (Q delta N) (rho delta N)| ≤ delta * singularNormalization N) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ N : ℕ in atTop, Even N →
      (RealB b N : ℝ) ≤
        (currentK * Real.log (1 / b) + epsilon) * singularNormalization N := by
  intro epsilon hepsilon
  let J : ℝ := Real.log (1 / b)
  have hJ : 0 < J := by
    apply Real.log_pos
    exact (one_lt_div hb).mpr hb1
  have hK : 0 < currentK := by norm_num [currentK]
  let budgetDenominator : ℝ := currentK + J + 5
  have hdenominator : 0 < budgetDenominator := by
    dsimp [budgetDenominator]
    linarith
  let delta : ℝ := min 1 (epsilon / budgetDenominator)
  have hdelta : 0 < delta := lt_min zero_lt_one (div_pos hepsilon hdenominator)
  have hdeltaOne : delta ≤ 1 := min_le_left _ _
  have hdeltaBudget : delta * budgetDenominator ≤ epsilon :=
    (le_div_iff₀ hdenominator).mp (min_le_right _ _)
  have hcoefficient : (J + delta) * (currentK + delta) + 4 * delta ≤
      currentK * J + epsilon := by
    have hsquare : delta * delta ≤ delta := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hdeltaOne hdelta.le
    dsimp only [budgetDenominator] at hdeltaBudget
    nlinarith only [hsquare, hdeltaBudget]
  have hmass : ∀ᶠ N : ℕ in atTop,
      ((realHalfProductSource b N (manuscriptHalfProductCutoff kappa N)).card : ℝ) /
        ((N : ℝ) / Real.log (N : ℝ)) < J + delta :=
    (tendsto_realHalfProductSource_manuscriptCutoff_mass_of_suppliers hb hb1 hkappa).eventually
      (gt_mem_nhds (lt_add_of_pos_right J hdelta))
  have hcap : ∀ᶠ N : ℕ in atTop,
      (Nat.ceil ((N : ℝ) ^ sieveExponent) : ℝ) ≤ delta * singularNormalization N := by
    simpa only [one_mul, pow_zero, mul_one] using
      eventually_ceil_powerLog_le_singularNormalization 1 sieveExponent 0
        (by norm_num) hsieve delta hdelta
  have hcutoff : ∀ᶠ N : ℕ in atTop,
      manuscriptHalfProductCutoff kappa N + 1 ≤ delta * singularNormalization N := by
    simpa only [manuscriptHalfProductCutoff, pow_zero, mul_one] using
      eventually_powerLog_add_one_le_singularNormalization 2 (1 - kappa) 0
        (by linarith) delta hdelta
  filter_upwards [hmajor delta hdelta, hdensity delta hdelta, hcoprime delta hdelta,
    hdistribution delta hdelta, hmass, hcap, hcutoff, eventually_ge_atTop (2 : ℕ)]
    with N hmajorN hdensityN hcoprimeN hdistributionN hmassN hcapN hcutoffN hN
  intro hEven
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hmassScale : 0 < (N : ℝ) / Real.log (N : ℝ) :=
    div_pos (lt_trans zero_lt_one hN1) (Real.log_pos hN1)
  have hdensityScale := densityScale_pos hN
  have hnormalization : 0 ≤ singularNormalization N := by
    rw [← sourceMassScale_mul_densityScale N]
    exact (mul_pos hmassScale hdensityScale).le
  have hsource :
      ((realHalfProductSource b N (manuscriptHalfProductCutoff kappa N)).card : ℝ) ≤
        (J + delta) * ((N : ℝ) / Real.log (N : ℝ)) :=
    (div_le_iff₀ hmassScale).mp hmassN.le
  have hmain :
      ((realHalfProductSource b N (manuscriptHalfProductCutoff kappa N)).card : ℝ) *
        physicalDensitySum (Q delta N) (rho delta N) ≤
        ((J + delta) * (currentK + delta)) * singularNormalization N := by
    calc
      ((realHalfProductSource b N (manuscriptHalfProductCutoff kappa N)).card : ℝ) *
          physicalDensitySum (Q delta N) (rho delta N) ≤
          ((realHalfProductSource b N (manuscriptHalfProductCutoff kappa N)).card : ℝ) *
            ((currentK + delta) * (singularSeries N / Real.log (N : ℝ))) :=
        mul_le_mul_of_nonneg_left (hdensityN hEven) (Nat.cast_nonneg _)
      _ ≤ ((J + delta) * ((N : ℝ) / Real.log (N : ℝ))) *
          ((currentK + delta) * (singularSeries N / Real.log (N : ℝ))) :=
        mul_le_mul_of_nonneg_right hsource
          (mul_nonneg (add_nonneg hK.le hdelta.le) hdensityScale.le)
      _ = ((J + delta) * (currentK + delta)) * singularNormalization N := by
        rw [← sourceMassScale_mul_densityScale N]
        ring
  have hcoprimeUpper := (le_abs_self
    (realPhysicalCoprimeCorrection b N (manuscriptHalfProductCutoff kappa N)
      (Q delta N) (rho delta N))).trans (hcoprimeN hEven)
  have hdistributionUpper := (le_abs_self
    (realPhysicalDistributionError b N (manuscriptHalfProductCutoff kappa N)
      (Q delta N) (rho delta N))).trans (hdistributionN hEven)
  have hfinite := RealB_cast_le_same_rho_main_add_errors N
    (Nat.ceil ((N : ℝ) ^ sieveExponent)) (Q delta N) (rho delta N) hb1
    (manuscriptHalfProductCutoff_nonneg kappa N) (hmajorN hEven)
  calc
    (RealB b N : ℝ) ≤
        ((J + delta) * (currentK + delta)) * singularNormalization N +
          delta * singularNormalization N + delta * singularNormalization N +
          delta * singularNormalization N + delta * singularNormalization N :=
      hfinite.trans (add_le_add (add_le_add (add_le_add (add_le_add hmain
        hcoprimeUpper) hdistributionUpper) hcapN) hcutoffN)
    _ = ((J + delta) * (currentK + delta) + 4 * delta) * singularNormalization N := by ring
    _ ≤ (currentK * J + epsilon) * singularNormalization N :=
      mul_le_mul_of_nonneg_right hcoefficient hnormalization

end

end ImbalancedChen
