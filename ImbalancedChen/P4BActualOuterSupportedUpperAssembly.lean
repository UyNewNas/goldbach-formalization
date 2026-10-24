import ImbalancedChen.ActualUpperCountingInputs
import ImbalancedChen.P4BZeroExtendOuterCarrier

/-!
# Actual outer upper assembly with a supported-carrier geometry gate

SOURCE ONLY / YELLOW / UNCOMPILED.
This is the complete actual same-coefficient asymptotic assembly for an outer
weight whose nonzero points lie below N. The enumeration carrier itself may
contain zero-weight points above N. The supported-carrier finite theorem
first truncates to m <= N and transports every finite mass and signed sum
back to this original carrier by exact zero-extension identities.

The original real-source mass, outer surplus, physical density, coprime
correction and primitive signed estimate all retain the same arguments and
the same attachedUpperCoefficient. The majorant and localization losses are
proved suppliers. The outer analytic estimates and the identical coefficient's
P4A density bound remain explicit conditional inputs, not proved conclusions.
-/

namespace ImbalancedChen
namespace P4B

noncomputable section
open Filter Topology
open scoped BigOperators

/-- Positive outer approximation is used before taking a signed modulus
sum. All hypotheses concern actual source geometry or the same physical
coefficient; the conclusion is conditional, not `current_realBad_upper`. -/
theorem eventually_RealB_le_of_actual_outer_supported_primitive_inputs
    {b kappa nu r : ℝ}
    (hb : 0 < b) (hb1 : b < 1) (hkappa : 0 < kappa)
    (hnu : 0 < nu) (hr : 0 < r) (hsieve : nu * r < 1)
    (epsilon : ℝ → ℝ) (retain : ℝ → ℕ → List ℕ → Bool)
    (cap : ℝ → ℕ → ℕ)
    (S : ℝ → ℕ → Finset ℕ) (weight : ℝ → ℕ → ℕ → ℝ)
    (hepsilon : ∀ delta : ℝ, 0 < delta →
      0 < epsilon delta ∧ epsilon delta ≤ 1 ∧ (epsilon delta) ^ 2 ≤ r)
    (hcover : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (nu * r) ≤ (cap delta N : ℝ))
    (hgeometry : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      (∀ m ∈ S delta N, weight delta N m ≠ 0 → m ≤ N) ∧
      realHalfProductSource b N (manuscriptHalfProductCutoff kappa N) ⊆ S delta N ∧
      (∀ m ∈ S delta N,
        (if m ∈ realHalfProductSource b N (manuscriptHalfProductCutoff kappa N)
          then (1 : ℝ) else 0) ≤ weight delta N m))
    (hsurplus : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      finiteSourceMass (S delta N) (weight delta N) ≤
        ((realHalfProductSource b N (manuscriptHalfProductCutoff kappa N)).card : ℝ) +
          delta * ((N : ℝ) / Real.log (N : ℝ)))
    (hdensity : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      physicalDensitySum
        (attachedUpperModuli nu r (epsilon delta) (retain delta) (cap delta) N)
        (attachedUpperCoefficient nu r (epsilon delta) (retain delta) (cap delta) N) ≤
          (currentK + delta) * (singularSeries N / Real.log (N : ℝ)))
    (hcoprime : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      |∑ d ∈ attachedUpperModuli nu r (epsilon delta) (retain delta) (cap delta) N,
        attachedUpperCoefficient nu r (epsilon delta) (retain delta) (cap delta) N d *
          ((finiteCoprimeMass (S delta N) (weight delta N) d -
              finiteSourceMass (S delta N) (weight delta N)) / (Nat.totient d : ℝ))| ≤
        delta * singularNormalization N)
    (hprimitive : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      |∑ d ∈ attachedUpperModuli nu r (epsilon delta) (retain delta) (cap delta) N,
        attachedUpperCoefficient nu r (epsilon delta) (retain delta) (cap delta) N d *
          finitePrimitiveDiscrepancy (S delta N) (weight delta N) N d| ≤
        delta * singularNormalization N) :
    ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ N : ℕ in atTop, Even N →
      (RealB b N : ℝ) ≤
        (currentK * Real.log (1 / b) + tolerance) * singularNormalization N := by
  intro tolerance htolerance
  let J : ℝ := Real.log (1 / b)
  have hJ : 0 < J := Real.log_pos ((one_lt_div hb).mpr hb1)
  have hK : 0 < currentK := by norm_num [currentK]
  let denominator : ℝ := 2 * currentK + J + 7
  have hdenominator : 0 < denominator := by dsimp [denominator]; linarith
  let delta : ℝ := min 1 (tolerance / denominator)
  have hdelta : 0 < delta := lt_min zero_lt_one (div_pos htolerance hdenominator)
  have hdeltaOne : delta ≤ 1 := min_le_left _ _
  have hdeltaBudget : delta * denominator ≤ tolerance :=
    (le_div_iff₀ hdenominator).mp (min_le_right _ _)
  have hcoefficient : (J + 2 * delta) * (currentK + delta) + 4 * delta ≤
      currentK * J + tolerance := by
    have hsquare : delta * delta ≤ delta := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hdeltaOne hdelta.le
    dsimp only [denominator] at hdeltaBudget
    nlinarith only [hsquare, hdeltaBudget, hdelta.le]
  have hmass : ∀ᶠ N : ℕ in atTop,
      ((realHalfProductSource b N (manuscriptHalfProductCutoff kappa N)).card : ℝ) /
        ((N : ℝ) / Real.log (N : ℝ)) < J + delta :=
    (tendsto_realHalfProductSource_manuscriptCutoff_mass_of_suppliers hb hb1 hkappa).eventually
      (gt_mem_nhds (lt_add_of_pos_right J hdelta))
  have hceil : ∀ᶠ N : ℕ in atTop,
      (Nat.ceil ((N : ℝ) ^ (nu * r)) : ℝ) ≤ delta * singularNormalization N := by
    simpa only [one_mul, pow_zero, mul_one] using
      eventually_ceil_powerLog_le_singularNormalization 1 (nu * r) 0
        (by norm_num) hsieve delta hdelta
  have hcutoff : ∀ᶠ N : ℕ in atTop,
      manuscriptHalfProductCutoff kappa N + 1 ≤ delta * singularNormalization N := by
    simpa only [manuscriptHalfProductCutoff, pow_zero, mul_one] using
      eventually_powerLog_add_one_le_singularNormalization 2 (1 - kappa) 0
        (by linarith) delta hdelta
  filter_upwards [hcover delta hdelta, hgeometry delta hdelta, hsurplus delta hdelta,
    hdensity delta hdelta, hcoprime delta hdelta, hprimitive delta hdelta,
    hmass, hceil, hcutoff, eventually_ge_atTop (2 : ℕ)]
    with N hcoverN hgeometryN hsurplusN hdensityN hcoprimeN hprimitiveN
      hmassN hceilN hcutoffN hN
  intro hEven
  obtain ⟨hsupported, hsource, houter⟩ := hgeometryN hEven
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hmassScale : 0 < (N : ℝ) / Real.log (N : ℝ) :=
    div_pos (lt_trans zero_lt_one hN1) (Real.log_pos hN1)
  have hdensityScale := densityScale_pos hN
  have hnormalization : 0 ≤ singularNormalization N := by
    rw [← sourceMassScale_mul_densityScale N]
    exact (mul_pos hmassScale hdensityScale).le
  have hsourceMass :
      ((realHalfProductSource b N (manuscriptHalfProductCutoff kappa N)).card : ℝ) ≤
        (J + delta) * ((N : ℝ) / Real.log (N : ℝ)) :=
    (div_le_iff₀ hmassScale).mp hmassN.le
  have houterMass : finiteSourceMass (S delta N) (weight delta N) ≤
      (J + 2 * delta) * ((N : ℝ) / Real.log (N : ℝ)) := by
    have hs := hsurplusN hEven
    nlinarith only [hs, hsourceMass]
  have hmassNonneg : 0 ≤ finiteSourceMass (S delta N) (weight delta N) := by
    apply Finset.sum_nonneg
    intro m hm
    have ho := houter m hm
    split_ifs at ho <;> linarith
  have hmain : finiteSourceMass (S delta N) (weight delta N) *
      physicalDensitySum
        (attachedUpperModuli nu r (epsilon delta) (retain delta) (cap delta) N)
        (attachedUpperCoefficient nu r (epsilon delta) (retain delta) (cap delta) N) ≤
      ((J + 2 * delta) * (currentK + delta)) * singularNormalization N := by
    calc
      _ ≤ finiteSourceMass (S delta N) (weight delta N) *
          ((currentK + delta) * (singularSeries N / Real.log (N : ℝ))) :=
        mul_le_mul_of_nonneg_left (hdensityN hEven) hmassNonneg
      _ ≤ ((J + 2 * delta) * ((N : ℝ) / Real.log (N : ℝ))) *
          ((currentK + delta) * (singularSeries N / Real.log (N : ℝ))) :=
        mul_le_mul_of_nonneg_right houterMass
          (mul_nonneg (add_nonneg hK.le hdelta.le) hdensityScale.le)
      _ = _ := by rw [← sourceMassScale_mul_densityScale N]; ring
  have hmajor := attachedUpperCoefficient_majorant hnu
    (hepsilon delta hdelta).1 (hepsilon delta hdelta).2.1
    (hepsilon delta hdelta).2.2 (retain delta) (cap delta) hN hcoverN
  have hfinite := RealB_cast_le_same_rho_outer_main_add_errors_of_supported_carrier N
    (Nat.ceil ((N : ℝ) ^ (nu * r))) (S delta N)
    (attachedUpperModuli nu r (epsilon delta) (retain delta) (cap delta) N)
    (weight delta N)
    (attachedUpperCoefficient nu r (epsilon delta) (retain delta) (cap delta) N)
    hb1 (manuscriptHalfProductCutoff_nonneg kappa N) hsupported hsource houter hmajor
  have hc := (le_abs_self _).trans (hcoprimeN hEven)
  have hp := (le_abs_self _).trans (hprimitiveN hEven)
  have hpaid := hfinite.trans
    (add_le_add (add_le_add (add_le_add (add_le_add hmain hc) hp) hceilN) hcutoffN)
  calc
    (RealB b N : ℝ) ≤
        (((J + 2 * delta) * (currentK + delta)) + 4 * delta) *
          singularNormalization N := by nlinarith only [hpaid]
    _ ≤ (currentK * J + tolerance) * singularNormalization N :=
      mul_le_mul_of_nonneg_right hcoefficient hnormalization

end
end P4B
end ImbalancedChen
