import ImbalancedChen.ActualHistoricalFifthSavingIntegral
import ImbalancedChen.ActualUpperPolicyFiniteBridge

/-!
# P4A: the same historical rho and its exact sign-sensitive ledger

The three stages select the literal policies from HistoricalPrefixCapData.
Even retention, coefficient identification, and physical attachment need no
level check.  The finite level check enters only the causal density identity.
The physical density difference keeps the negative rough mass correction:
attaching beta-plus to every raw coefficient would give a false identity.

All small weights, cutoffs, target deletions and enumeration caps are shared
between the two stages of each difference.  The causal actual-density supplier
uses the full rough carrier w=0, so only that specialization is identified
with the historical fourth/fifth savings.  The physical sign decomposition
itself holds at every presieve cutoff w.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators

inductive P4AHistoricalStage where
  | third
  | fourth
  | fifth
  deriving DecidableEq

/-- Magnitude of the negative coefficients' reciprocal-totient mass. -/
def p4aNegativeRoughMass (S : Finset ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ d ∈ S, if 0 ≤ c d then 0 else -(c d) / (Nat.totient d : ℝ)

def p4aPositiveRoughMass (S : Finset ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ d ∈ S, if 0 ≤ c d then c d / (Nat.totient d : ℝ) else 0

theorem p4aNegativeRoughMass_nonneg (S : Finset ℕ) (c : ℕ → ℝ) :
    0 ≤ p4aNegativeRoughMass S c := by
  unfold p4aNegativeRoughMass
  apply Finset.sum_nonneg
  intro d _hd
  by_cases hc : 0 ≤ c d
  · simp only [if_pos hc, le_refl]
  · rw [if_neg hc]
    exact div_nonneg (neg_nonneg.mpr (le_of_not_ge hc)) (Nat.cast_nonneg _)

theorem p4aPositiveRoughMass_nonneg (S : Finset ℕ) (c : ℕ → ℝ) :
    0 ≤ p4aPositiveRoughMass S c := by
  unfold p4aPositiveRoughMass
  apply Finset.sum_nonneg
  intro d _hd
  by_cases hc : 0 ≤ c d
  · rw [if_pos hc]
    exact div_nonneg hc (Nat.cast_nonneg _)
  · simp only [if_neg hc, le_refl]

theorem p4a_reciprocalDensity_eq_positive_sub_negative
    (S : Finset ℕ) (c : ℕ → ℝ) :
    reciprocalTotientDensity S c =
      p4aPositiveRoughMass S c - p4aNegativeRoughMass S c := by
  unfold reciprocalTotientDensity p4aPositiveRoughMass p4aNegativeRoughMass
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d _hd
  by_cases hc : 0 ≤ c d <;> simp only [hc, if_true, if_false] <;> ring

/-- Exact attachment formula with the negative mass visible. -/
theorem p4a_signSensitiveDensity_eq_raw_add_negativeMass
    (S : Finset ℕ) (c : ℕ → ℝ) (lo hi : ℝ) :
    signSensitiveReciprocalTotientDensity S c lo hi =
      reciprocalTotientDensity S c * hi + p4aNegativeRoughMass S c * (hi - lo) := by
  unfold signSensitiveReciprocalTotientDensity reciprocalTotientDensity
    p4aNegativeRoughMass
  rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _hd
  by_cases hc : 0 ≤ c d <;> simp only [hc, if_true, if_false] <;> ring

namespace HistoricalPrefixCapData

def p4aHistoricalPolicy (D : HistoricalPrefixCapData) (N : ℝ) :
    P4AHistoricalStage → Bool → List ℕ → Bool
  | .third => D.upperThirdPolicy N
  | .fourth => D.upperFourthPolicy N
  | .fifth => D.upperFifthPolicy N

theorem p4a_historical_even_retained (D : HistoricalPrefixCapData)
    (N : ℝ) (stage : P4AHistoricalStage) (pre : List ℕ) :
    D.p4aHistoricalPolicy N stage true pre = true := by
  cases stage with
  | third => exact D.upperThirdPolicy_even N pre
  | fourth => exact D.upperFourthPolicy_even N pre
  | fifth => exact D.upperFifthPolicy_even N pre

/-- The literal rough coefficient used by the physical attachment is the
first-exit coefficient of the selected historical policy. -/
theorem p4a_historical_fixedCoefficient_eq (D : HistoricalPrefixCapData)
    (stage : P4AHistoricalStage) (N cap : ℕ) (w z : ℝ) (d : ℕ) :
    fixedRoughCoefficient (D.p4aHistoricalPolicy (N : ℝ) stage false) N cap w z d =
      (firstExitRetainedCoefficient (D.p4aHistoricalPolicy (N : ℝ) stage)
        (roughPrimeUniverse N cap w z) d : ℝ) := by
  exact UpperPolicyFiniteBridge.fixedRoughCoefficient_eq_firstExitRetainedCoefficient_of_even_retained
    _ (D.p4a_historical_even_retained (N : ℝ) stage) N cap w z d

/-- Function equality, before any integer or progression is tested. -/
theorem p4a_historical_rho_eq_firstExitAttachment (D : HistoricalPrefixCapData)
    (stage : P4AHistoricalStage) (N cap : ℕ) (w z L : ℝ) :
    actualSmallRoughRho (D.p4aHistoricalPolicy (N : ℝ) stage false) N cap w z L =
      smallRoughRho (actualSmallRosserSupport N cap w)
        (firstExitRetainedModuli (D.p4aHistoricalPolicy (N : ℝ) stage)
          (roughPrimeUniverse N cap w z))
        (fun d => (firstExitRetainedCoefficient (D.p4aHistoricalPolicy (N : ℝ) stage)
          (roughPrimeUniverse N cap w z) d : ℝ))
        (actualSmallRosserMinus N cap w L) (actualSmallRosserPlus N cap w L) := by
  exact UpperPolicyFiniteBridge.actualSmallRoughRho_eq_firstExitAttachment
    _ (D.p4a_historical_even_retained (N : ℝ) stage) N cap w z L

def p4aHistoricalRawDensity (D : HistoricalPrefixCapData)
    (stage : P4AHistoricalStage) (N cap : ℕ) (w z : ℝ) : ℝ :=
  reciprocalTotientDensity
    (fixedRoughSupport (D.p4aHistoricalPolicy (N : ℝ) stage false) N cap w z)
    (fixedRoughCoefficient (D.p4aHistoricalPolicy (N : ℝ) stage false) N cap w z)

def p4aHistoricalNegativeMass (D : HistoricalPrefixCapData)
    (stage : P4AHistoricalStage) (N cap : ℕ) (w z : ℝ) : ℝ :=
  p4aNegativeRoughMass
    (fixedRoughSupport (D.p4aHistoricalPolicy (N : ℝ) stage false) N cap w z)
    (fixedRoughCoefficient (D.p4aHistoricalPolicy (N : ℝ) stage false) N cap w z)

def p4aHistoricalPhysicalDensity (D : HistoricalPrefixCapData)
    (stage : P4AHistoricalStage) (N cap : ℕ) (w z L : ℝ) : ℝ :=
  physicalDensitySum
    (actualSmallRoughModuli (D.p4aHistoricalPolicy (N : ℝ) stage false) N cap w z)
    (actualSmallRoughRho (D.p4aHistoricalPolicy (N : ℝ) stage false) N cap w z L)

def p4aSmallPlusDensity (N cap : ℕ) (w L : ℝ) : ℝ :=
  reciprocalTotientDensity (actualSmallRosserSupport N cap w)
    (actualSmallRosserPlus N cap w L)

def p4aSmallMinusDensity (N cap : ℕ) (w L : ℝ) : ℝ :=
  reciprocalTotientDensity (actualSmallRosserSupport N cap w)
    (actualSmallRosserMinus N cap w L)

theorem p4a_historicalRawDensity_eq_polynomial (D : HistoricalPrefixCapData)
    (stage : P4AHistoricalStage) (N cap : ℕ) (w z : ℝ) :
    D.p4aHistoricalRawDensity stage N cap w z =
      firstExitRetainedPolynomial (D.p4aHistoricalPolicy (N : ℝ) stage)
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap w z) := by
  exact (UpperPolicyFiniteBridge.firstExitRetainedPolynomial_eq_fixedRoughDensity_of_even_retained
    _ (D.p4a_historical_even_retained (N : ℝ) stage) N cap w z).symm

theorem p4a_historicalPhysicalDensity_eq (D : HistoricalPrefixCapData)
    (stage : P4AHistoricalStage) (N cap : ℕ) (w z L : ℝ) :
    D.p4aHistoricalPhysicalDensity stage N cap w z L =
      D.p4aHistoricalRawDensity stage N cap w z * p4aSmallPlusDensity N cap w L +
        D.p4aHistoricalNegativeMass stage N cap w z *
          (p4aSmallPlusDensity N cap w L - p4aSmallMinusDensity N cap w L) := by
  unfold p4aHistoricalPhysicalDensity
  rw [actualSmallRoughRho_density_eq]
  exact p4a_signSensitiveDensity_eq_raw_add_negativeMass _ _ _ _

/-- Same small weights at both stages, with the exact sign-sensitive
correction.  The raw difference alone is insufficient when lo differs from hi. -/
theorem p4a_historicalPhysicalDifference_eq (D : HistoricalPrefixCapData)
    (oldStage newStage : P4AHistoricalStage) (N cap : ℕ) (w z L : ℝ) :
    D.p4aHistoricalPhysicalDensity oldStage N cap w z L -
        D.p4aHistoricalPhysicalDensity newStage N cap w z L =
      (D.p4aHistoricalRawDensity oldStage N cap w z -
        D.p4aHistoricalRawDensity newStage N cap w z) * p4aSmallPlusDensity N cap w L +
      (D.p4aHistoricalNegativeMass oldStage N cap w z -
        D.p4aHistoricalNegativeMass newStage N cap w z) *
          (p4aSmallPlusDensity N cap w L - p4aSmallMinusDensity N cap w L) := by
  rw [D.p4a_historicalPhysicalDensity_eq, D.p4a_historicalPhysicalDensity_eq]
  ring

/-- The fourth-to-fifth raw saving is now attached to the very coefficients
used in the physical density.  No absolute or sign-sensitive error is dropped. -/
theorem p4a_historicalPhysicalFourthToFifthLedger (D : HistoricalPrefixCapData)
    (hab : D.a ≤ D.b) (hcheck : D.levelCheck = true)
    (N cap : ℕ) (hN : 1 < (N : ℝ)) (L : ℝ) :
    (D.p4aHistoricalPhysicalDensity .fourth N cap 0 ((N : ℝ) ^ (D.b : ℝ)) L -
      D.p4aHistoricalPhysicalDensity .fifth N cap 0 ((N : ℝ) ^ (D.b : ℝ)) L) *
        Real.log (N : ℝ) / singularSeries N =
      D.fifthPrimeCorrection N cap * p4aSmallPlusDensity N cap 0 L +
      (D.p4aHistoricalNegativeMass .fourth N cap 0 ((N : ℝ) ^ (D.b : ℝ)) -
        D.p4aHistoricalNegativeMass .fifth N cap 0 ((N : ℝ) ^ (D.b : ℝ))) *
          (p4aSmallPlusDensity N cap 0 L - p4aSmallMinusDensity N cap 0 L) *
            Real.log (N : ℝ) / singularSeries N := by
  have hraw :
      (D.p4aHistoricalRawDensity .fourth N cap 0 ((N : ℝ) ^ (D.b : ℝ)) -
        D.p4aHistoricalRawDensity .fifth N cap 0 ((N : ℝ) ^ (D.b : ℝ))) *
          Real.log (N : ℝ) / singularSeries N = D.fifthPrimeCorrection N cap := by
    rw [D.p4a_historicalRawDensity_eq_polynomial, D.p4a_historicalRawDensity_eq_polynomial]
    exact D.upperFourthToFifthSaving_normalized_eq_fifthPrimeCorrection hab hcheck N cap hN
  rw [D.p4a_historicalPhysicalDifference_eq, ← hraw]
  ring

/-- The third-to-fifth physical difference subtracts the fourth and fifth
causal entries once each, and retains the same negative-mass correction. -/
theorem p4a_historicalPhysicalThirdToFifthLedger (D : HistoricalPrefixCapData)
    (hab : D.a ≤ D.b) (hcheck : D.levelCheck = true)
    (N cap : ℕ) (hN : 1 < (N : ℝ)) (L : ℝ) :
    (D.p4aHistoricalPhysicalDensity .third N cap 0 ((N : ℝ) ^ (D.b : ℝ)) L -
      D.p4aHistoricalPhysicalDensity .fifth N cap 0 ((N : ℝ) ^ (D.b : ℝ)) L) *
        Real.log (N : ℝ) / singularSeries N =
      (actualHistoricalFourthSaving
        (ordinaryParityRosserPolicy false ((N : ℝ) ^ (D.old : ℝ)))
        (D.level3 (N : ℝ)) (D.level4 (N : ℝ)) N cap ((N : ℝ) ^ (D.b : ℝ)) *
          Real.log (N : ℝ) / singularSeries N + D.fifthPrimeCorrection N cap) *
        p4aSmallPlusDensity N cap 0 L +
      (D.p4aHistoricalNegativeMass .third N cap 0 ((N : ℝ) ^ (D.b : ℝ)) -
        D.p4aHistoricalNegativeMass .fifth N cap 0 ((N : ℝ) ^ (D.b : ℝ))) *
          (p4aSmallPlusDensity N cap 0 L - p4aSmallMinusDensity N cap 0 L) *
            Real.log (N : ℝ) / singularSeries N := by
  have hraw := D.upperThirdToFifthSaving_eq hab hcheck N cap hN
    ((N : ℝ) ^ (D.b : ℝ))
  have hdict := D.actualHistoricalFifthSaving_eq_fifthPrimeCorrection N cap
  rw [D.p4a_historicalPhysicalDifference_eq,
    D.p4a_historicalRawDensity_eq_polynomial, D.p4a_historicalRawDensity_eq_polynomial]
  simp only [p4aHistoricalPolicy]
  rw [hraw, ← hdict]
  ring

end HistoricalPrefixCapData

end

end ImbalancedChen
