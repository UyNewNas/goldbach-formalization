import ImbalancedChen.P4AHistoricalPhysicalSavingsReserve

/-!
# P4A: one reserve for a difference of one-sided attachment errors

Both policies use the same small weights and the same precision/threshold.
Their attachment errors lie in the same interval [0,B], so their difference
has absolute value at most B.  Neither error is assumed zero or canceled.
The full-carrier historical transfer retains both presieve corrections.
-/

namespace ImbalancedChen

noncomputable section

/-- The diameter of the common one-sided interval is one reserve. -/
theorem p4a_oneSidedAttachmentDifference_abs_le
    (Aold Anew Rold Rnew V B : ℝ)
    (hold : 0 ≤ Aold - V * Rold ∧ Aold - V * Rold ≤ B)
    (hnew : 0 ≤ Anew - V * Rnew ∧ Anew - V * Rnew ≤ B) :
    |(Aold - Anew) - V * (Rold - Rnew)| ≤ B := by
  apply abs_le.mpr
  constructor <;> nlinarith [hold.1, hold.2, hnew.1, hnew.2]

/-- Exact projection transport for a difference, on the same prime split. -/
theorem p4a_presievedDifference_eq_full_sub_corrections
    (old new : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) (hwz : w ≤ z) :
    actualSmallEulerProduct N cap w *
        (p4aReserveRawDensity old N cap w z - p4aReserveRawDensity new N cap w z) =
      (p4aReserveRawDensity old N cap 0 z - p4aReserveRawDensity new N cap 0 z) -
        (p4aActualPresieveCorrection old N cap w z -
          p4aActualPresieveCorrection new N cap w z) := by
  have hold := p4a_fullRaw_eq_euler_presieved_add_correction old N cap w z hwz
  have hnew := p4a_fullRaw_eq_euler_presieved_add_correction new N cap w z hwz
  nlinarith [hold, hnew]

/-- One precision and one threshold precede both policies.  The saving
difference costs eta, using the proved common one-sided error interval. -/
theorem exists_p4a_twoPolicy_physicalSavings_oneReserve
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
              eta * singularSeries N / Real.log (N : ℝ) := by
  obtain ⟨epsilon, hepsilon, hepsilon8, hepsilonMax', hepsilonr,
      N₀, hN₀, hbound⟩ :=
    exists_actualSmallRoughRho_density_error_le_target_reserve
      nu r eta epsilonMax hnu hr heta hepsilonMax
  refine ⟨epsilon, hepsilon, hepsilon8, hepsilonMax', hepsilonr, N₀, hN₀, ?_⟩
  intro N hN hEven cap hcap old new
  have hold := hbound N hN hEven cap hcap old
  have hnew := hbound N hN hEven cap hcap new
  dsimp only at hold hnew ⊢
  exact p4a_oneSidedAttachmentDifference_abs_le _ _ _ _ _ _ hold hnew

/-- The original third-to-fifth signed ledger transfers with a single eta
reserve.  The same finite projection corrections as before remain explicit. -/
theorem exists_p4a_historicalThirdToFifth_physicalSavings_oneReserve
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
              eta * singularSeries N / Real.log (N : ℝ) := by
  obtain ⟨epsilon, hepsilon, hepsilon8, hepsilonMax', hepsilonr,
      N₀, hN₀, hbound⟩ := exists_p4a_twoPolicy_physicalSavings_oneReserve
    nu r eta epsilonMax hnu hr heta hepsilonMax
  refine ⟨epsilon, hepsilon, hepsilon8, hepsilonMax', hepsilonr, N₀, hN₀, ?_⟩
  intro N hN hEven cap hcap D hab hcheck
  let w := (N : ℝ) ^ (nu * epsilon ^ 2)
  let z := (N : ℝ) ^ (nu * r)
  let L := (N : ℝ) ^ (nu * epsilon)
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hwz : w ≤ z := Real.rpow_le_rpow_of_exponent_le hN1.le
    (mul_le_mul_of_nonneg_left hepsilonr hnu.le)
  have hraw := D.upperThirdToFifthSaving_eq hab hcheck N cap hN1 z
  have hidentOld := UpperPolicyFiniteBridge.firstExitRetainedPolynomial_eq_fixedRoughDensity_of_even_retained
    (D.upperThirdPolicy (N : ℝ)) (D.upperThirdPolicy_even (N : ℝ)) N cap 0 z
  have hidentNew := UpperPolicyFiniteBridge.firstExitRetainedPolynomial_eq_fixedRoughDensity_of_even_retained
    (D.upperFifthPolicy (N : ℝ)) (D.upperFifthPolicy_even (N : ℝ)) N cap 0 z
  rw [hidentOld, hidentNew] at hraw
  change p4aReserveRawDensity (D.upperThirdPolicy (N : ℝ) false) N cap 0 z -
    p4aReserveRawDensity (D.upperFifthPolicy (N : ℝ) false) N cap 0 z = _ at hraw
  have h := hbound N hN hEven cap hcap
    (D.upperThirdPolicy (N : ℝ) false) (D.upperFifthPolicy (N : ℝ) false)
  dsimp only at h ⊢
  change |(p4aReservePhysicalDensity _ N cap w z L -
    p4aReservePhysicalDensity _ N cap w z L) -
    actualSmallEulerProduct N cap w *
      (p4aReserveRawDensity _ N cap w z - p4aReserveRawDensity _ N cap w z)| ≤ _ at h
  rw [p4a_presievedDifference_eq_full_sub_corrections _ _ N cap w z hwz, hraw] at h
  exact h

end

end ImbalancedChen
