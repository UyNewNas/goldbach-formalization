import ImbalancedChen.ActualNormalizedRhoError
import ImbalancedChen.ActualFirstExitDensityProjection
import ImbalancedChen.ActualUpperPolicyFiniteBridge
import ImbalancedChen.HistoricalPrefixCertificate

/-!
# P4A: uniform two-policy physical savings reserve

One epsilon and threshold work for every pair of policies, on the same
actual small weights.  The full historical saving uses w=0; transferring
it to a positive presieve keeps the genuine small-carrier continuation
correction of each policy.  Only the proved attachment error is small here.
No presieve correction, full raw-density bound, or K estimate is assumed.
-/

namespace ImbalancedChen

noncomputable section

def p4aReserveRawDensity (retain : List ℕ → Bool)
    (N cap : ℕ) (w z : ℝ) : ℝ :=
  reciprocalTotientDensity (fixedRoughSupport retain N cap w z)
    (fixedRoughCoefficient retain N cap w z)

def p4aReservePhysicalDensity (retain : List ℕ → Bool)
    (N cap : ℕ) (w z L : ℝ) : ℝ :=
  physicalDensitySum (actualSmallRoughModuli retain N cap w z)
    (actualSmallRoughRho retain N cap w z L)

/-- The small-carrier continuation correction, with every rough leaf's
actual selected history, sign, and mass.  This is a literal finite sum,
not a name for the desired density difference. -/
def p4aActualPresieveCorrection (retain : List ℕ → Bool)
    (N cap : ℕ) (w z : ℝ) : ℝ :=
  ((firstExitRetainedLeaves (oddFirstExitPolicy retain)
    (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
    (roughPrimeUniverse N cap w z)).map (fun leaf =>
      firstExitCorrection (oddFirstExitPolicy retain)
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) leaf.selected leaf.positive leaf.mass
        (roughPrimeUniverse N cap 0 w))).sum

/-- Exact physical presieve accounting before any estimate. -/
theorem p4a_fullRaw_eq_euler_presieved_add_correction
    (retain : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) (hwz : w ≤ z) :
    p4aReserveRawDensity retain N cap 0 z =
      actualSmallEulerProduct N cap w * p4aReserveRawDensity retain N cap w z +
        p4aActualPresieveCorrection retain N cap w z := by
  have h := firstExitRetainedPolynomial_append_eq_mul_product_add_corrections
    (oddFirstExitPolicy retain) (fun p : ℕ => 1 / ((p : ℝ) - 1)) []
    (roughPrimeUniverse N cap w z) (roughPrimeUniverse N cap 0 w) true 1
  rw [roughPrimeUniverse_small_eulerProduct,
    ← roughPrimeUniverse_split N cap w z hwz] at h
  change oddFirstExitRetainedPolynomial retain
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) (roughPrimeUniverse N cap 0 z) =
    oddFirstExitRetainedPolynomial retain
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) (roughPrimeUniverse N cap w z) *
        actualSmallEulerProduct N cap w + p4aActualPresieveCorrection retain N cap w z at h
  rw [oddFirstExitRetainedPolynomial_eq_fixedRoughDensity,
    oddFirstExitRetainedPolynomial_eq_fixedRoughDensity] at h
  simpa only [p4aReserveRawDensity, mul_comm] using h

theorem p4aActualPresieveCorrection_nonneg
    (retain : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) (hwz : w ≤ z) :
    0 ≤ p4aActualPresieveCorrection retain N cap w z := by
  have h := fixedRoughDensity_presieveProjection retain N cap w z hwz
  have heq := p4a_fullRaw_eq_euler_presieved_add_correction retain N cap w z hwz
  change actualSmallEulerProduct N cap w * p4aReserveRawDensity retain N cap w z ≤
    p4aReserveRawDensity retain N cap 0 z at h
  linarith

/-- Precision and threshold precede both policies.  The two physical
weights use the same beta-minus/beta-plus, target, cap, and all cutoffs. -/
theorem exists_p4a_twoPolicy_physicalSavings_reserve
    (nu r eta epsilonMax : ℝ) (hnu : 0 < nu) (hr : 0 < r)
    (heta : 0 < eta) (hepsilonMax : 0 < epsilonMax) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 / 8 ∧
      epsilon < epsilonMax ∧ epsilon ^ 2 ≤ r ∧
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
        ∀ cap : ℕ, (N : ℝ) ^ (nu * r) ≤ (cap : ℝ) →
          ∀ old new : List ℕ → Bool,
            let w := (N : ℝ) ^ (nu * epsilon ^ 2)
            let z := (N : ℝ) ^ (nu * r)
            let L := (N : ℝ) ^ (nu * epsilon)
            let V := actualSmallEulerProduct N cap w
            |(p4aReservePhysicalDensity old N cap w z L -
                p4aReservePhysicalDensity new N cap w z L) -
              V * (p4aReserveRawDensity old N cap w z -
                p4aReserveRawDensity new N cap w z)| ≤
              2 * eta * singularSeries N / Real.log (N : ℝ) := by
  obtain ⟨epsilon, hepsilon, hepsilon8, hepsilonMax', hepsilonr,
      N₀, hN₀, hbound⟩ :=
    exists_actualSmallRoughRho_density_error_le_target_reserve
      nu r eta epsilonMax hnu hr heta hepsilonMax
  refine ⟨epsilon, hepsilon, hepsilon8, hepsilonMax', hepsilonr, N₀, hN₀, ?_⟩
  intro N hN hEven cap hcap old new
  have hold := hbound N hN hEven cap hcap old
  have hnew := hbound N hN hEven cap hcap new
  dsimp only at hold hnew ⊢
  change 0 ≤ p4aReservePhysicalDensity old N cap _ _ _ -
      actualSmallEulerProduct N cap _ * p4aReserveRawDensity old N cap _ _ ∧
    p4aReservePhysicalDensity old N cap _ _ _ -
      actualSmallEulerProduct N cap _ * p4aReserveRawDensity old N cap _ _ ≤
        eta * singularSeries N / Real.log (N : ℝ) at hold
  change 0 ≤ p4aReservePhysicalDensity new N cap _ _ _ -
      actualSmallEulerProduct N cap _ * p4aReserveRawDensity new N cap _ _ ∧
    p4aReservePhysicalDensity new N cap _ _ _ -
      actualSmallEulerProduct N cap _ * p4aReserveRawDensity new N cap _ _ ≤
        eta * singularSeries N / Real.log (N : ℝ) at hnew
  apply abs_le.mpr
  constructor <;> nlinarith [hold.1, hold.2, hnew.1, hnew.2]

/-- Same epsilon and threshold transfer the complete third-to-fifth
historical signed ledger.  The projection-correction difference is retained
explicitly; only the actual small-weight attachment has the small reserve. -/
theorem exists_p4a_historicalThirdToFifth_physicalSavings_reserve
    (nu r eta epsilonMax : ℝ) (hnu : 0 < nu) (hr : 0 < r)
    (heta : 0 < eta) (hepsilonMax : 0 < epsilonMax) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 / 8 ∧
      epsilon < epsilonMax ∧ epsilon ^ 2 ≤ r ∧
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
        ∀ cap : ℕ, (N : ℝ) ^ (nu * r) ≤ (cap : ℝ) →
          ∀ D : HistoricalPrefixCapData, D.a ≤ D.b → D.levelCheck = true →
            let w := (N : ℝ) ^ (nu * epsilon ^ 2)
            let z := (N : ℝ) ^ (nu * r)
            let L := (N : ℝ) ^ (nu * epsilon)
            |(p4aReservePhysicalDensity (D.upperThirdPolicy (N : ℝ) false) N cap w z L -
                p4aReservePhysicalDensity (D.upperFifthPolicy (N : ℝ) false) N cap w z L) -
              (actualHistoricalFourthSaving
                (ordinaryParityRosserPolicy false ((N : ℝ) ^ (D.old : ℝ)))
                (D.level3 (N : ℝ)) (D.level4 (N : ℝ)) N cap z +
                actualHistoricalFifthSaving
                  (ordinaryParityRosserPolicy false ((N : ℝ) ^ (D.old : ℝ)))
                  (D.level3 (N : ℝ)) (D.level4 (N : ℝ)) (D.level5 (N : ℝ)) N cap z -
                (p4aActualPresieveCorrection (D.upperThirdPolicy (N : ℝ) false) N cap w z -
                  p4aActualPresieveCorrection (D.upperFifthPolicy (N : ℝ) false) N cap w z))| ≤
              2 * eta * singularSeries N / Real.log (N : ℝ) := by
  obtain ⟨epsilon, hepsilon, hepsilon8, hepsilonMax', hepsilonr,
      N₀, hN₀, hbound⟩ := exists_p4a_twoPolicy_physicalSavings_reserve
    nu r eta epsilonMax hnu hr heta hepsilonMax
  refine ⟨epsilon, hepsilon, hepsilon8, hepsilonMax', hepsilonr, N₀, hN₀, ?_⟩
  intro N hN hEven cap hcap D hab hcheck
  let w := (N : ℝ) ^ (nu * epsilon ^ 2)
  let z := (N : ℝ) ^ (nu * r)
  let L := (N : ℝ) ^ (nu * epsilon)
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hwz : w ≤ z := Real.rpow_le_rpow_of_exponent_le hN1.le
    (mul_le_mul_of_nonneg_left hepsilonr hnu.le)
  have hold := p4a_fullRaw_eq_euler_presieved_add_correction
    (D.upperThirdPolicy (N : ℝ) false) N cap w z hwz
  have hnew := p4a_fullRaw_eq_euler_presieved_add_correction
    (D.upperFifthPolicy (N : ℝ) false) N cap w z hwz
  have hraw := D.upperThirdToFifthSaving_eq hab hcheck N cap hN1 z
  have hidentOld := UpperPolicyFiniteBridge.firstExitRetainedPolynomial_eq_fixedRoughDensity_of_even_retained
    (D.upperThirdPolicy (N : ℝ)) (D.upperThirdPolicy_even (N : ℝ)) N cap 0 z
  have hidentNew := UpperPolicyFiniteBridge.firstExitRetainedPolynomial_eq_fixedRoughDensity_of_even_retained
    (D.upperFifthPolicy (N : ℝ)) (D.upperFifthPolicy_even (N : ℝ)) N cap 0 z
  rw [hidentOld, hidentNew] at hraw
  change p4aReserveRawDensity (D.upperThirdPolicy (N : ℝ) false) N cap 0 z -
    p4aReserveRawDensity (D.upperFifthPolicy (N : ℝ) false) N cap 0 z = _ at hraw
  have hledger :
      actualSmallEulerProduct N cap w *
        (p4aReserveRawDensity (D.upperThirdPolicy (N : ℝ) false) N cap w z -
          p4aReserveRawDensity (D.upperFifthPolicy (N : ℝ) false) N cap w z) =
      actualHistoricalFourthSaving
          (ordinaryParityRosserPolicy false ((N : ℝ) ^ (D.old : ℝ)))
          (D.level3 (N : ℝ)) (D.level4 (N : ℝ)) N cap z +
        actualHistoricalFifthSaving
          (ordinaryParityRosserPolicy false ((N : ℝ) ^ (D.old : ℝ)))
          (D.level3 (N : ℝ)) (D.level4 (N : ℝ)) (D.level5 (N : ℝ)) N cap z -
        (p4aActualPresieveCorrection (D.upperThirdPolicy (N : ℝ) false) N cap w z -
          p4aActualPresieveCorrection (D.upperFifthPolicy (N : ℝ) false) N cap w z) := by
    nlinarith [hold, hnew, hraw]
  have h := hbound N hN hEven cap hcap
    (D.upperThirdPolicy (N : ℝ) false) (D.upperFifthPolicy (N : ℝ) false)
  dsimp only at h ⊢
  change |(p4aReservePhysicalDensity _ N cap w z L -
    p4aReservePhysicalDensity _ N cap w z L) -
    actualSmallEulerProduct N cap w *
      (p4aReserveRawDensity _ N cap w z - p4aReserveRawDensity _ N cap w z)| ≤ _ at h
  rw [hledger] at h
  exact h

end

end ImbalancedChen
