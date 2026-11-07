import ImbalancedChen.ActualFirstExitDensityProjection
import ImbalancedChen.P4AHistoricalSameRhoAttachment
import ImbalancedChen.P4AHistoricalCausalSavingsLedger

/-!
# P4A: direct one-sided physical fifth-policy ledger

The universal single-policy physical-to-full-raw supplier is applied to
the literal fifth historical policy. Its full signed raw density then
telescopes into the third full density minus the fourth and fifth savings,
each exactly once. No physical difference is factored, and no difference
of projection corrections is charged to the reserve.

The finite level check supplies inherited level admissibility; the mesh
order a <= b remains the geometric premise of the existing finite ledger.
No raw upper bound, whole-density limit, or sharp K premise is introduced.
At the original historical cutoff the exponent equality b = nu*r is
explicit. Epsilon and the threshold are uniform in all cap data.

SOURCE ONLY: this candidate and its draft imports have not been compiled.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators

namespace HistoricalPrefixCapData

/-- The exact full signed fifth density, on any common finite carrier. -/
theorem p4a_historicalFifth_fullRaw_eq_causalLedger
    (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b) (hcheck : D.levelCheck = true)
    (N cap : ℕ) (hN : 1 < (N : ℝ)) (z : ℝ) :
    D.p4aHistoricalRawDensity .fifth N cap 0 z =
      D.p4aHistoricalRawDensity .third N cap 0 z -
        actualHistoricalFourthSaving
          (ordinaryParityRosserPolicy false ((N : ℝ) ^ (D.old : ℝ)))
          (D.level3 (N : ℝ)) (D.level4 (N : ℝ)) N cap z -
        actualHistoricalFifthSaving
          (ordinaryParityRosserPolicy false ((N : ℝ) ^ (D.old : ℝ)))
          (D.level3 (N : ℝ)) (D.level4 (N : ℝ)) (D.level5 (N : ℝ)) N cap z := by
  have h := D.upperThirdToFifthSaving_eq hab hcheck N cap hN z
  have hthird := D.p4a_historicalRawDensity_eq_polynomial .third N cap 0 z
  have hfifth := D.p4a_historicalRawDensity_eq_polynomial .fifth N cap 0 z
  simp only [p4aHistoricalPolicy] at hthird hfifth
  rw [← hthird, ← hfifth] at h
  linarith

/-- Dictionary from the full reciprocal-totient density to the normalized
policy polynomial used in the finite causal ledger. -/
theorem p4a_historicalRawDensity_normalized_eq_policyDensity
    (D : HistoricalPrefixCapData) (stage : P4AHistoricalStage)
    (N cap : ℕ) (z : ℝ) :
    D.p4aHistoricalRawDensity stage N cap 0 z *
      Real.log (N : ℝ) / singularSeries N =
      D.p4aPolicyDensity (D.p4aHistoricalPolicy (N : ℝ) stage) N cap z := by
  rw [D.p4a_historicalRawDensity_eq_polynomial]
  rfl

end HistoricalPrefixCapData

/-- Direct application of the genuine universal single-policy supplier.
Even the cap data are chosen after epsilon and the natural threshold. -/
theorem exists_p4a_historicalFifth_physical_le_fullRaw_reserve
    (nu r eta epsilonMax : ℝ) (hnu : 0 < nu) (hr : 0 < r)
    (heta : 0 < eta) (hepsilonMax : 0 < epsilonMax) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 / 8 ∧
      epsilon < epsilonMax ∧ epsilon ^ 2 ≤ r ∧
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
        ∀ cap : ℕ, (N : ℝ) ^ (nu * r) ≤ (cap : ℝ) →
          ∀ D : HistoricalPrefixCapData,
            let w := (N : ℝ) ^ (nu * epsilon ^ 2)
            let z := (N : ℝ) ^ (nu * r)
            let L := (N : ℝ) ^ (nu * epsilon)
            D.p4aHistoricalPhysicalDensity .fifth N cap w z L ≤
              D.p4aHistoricalRawDensity .fifth N cap 0 z +
                eta * singularSeries N / Real.log (N : ℝ) := by
  obtain ⟨epsilon, hepsilon, hepsilon8, hepsilonMax', hepsilonr,
      N₀, hN₀, hsupply⟩ := exists_actualSmallRoughRho_density_le_full_reserve
    nu r eta epsilonMax hnu hr heta hepsilonMax
  refine ⟨epsilon, hepsilon, hepsilon8, hepsilonMax', hepsilonr, N₀, hN₀, ?_⟩
  intro N hN hEven cap hcap D
  exact hsupply N hN hEven cap hcap (D.upperFifthPolicy (N : ℝ) false)

/-- The fifth physical density is bounded by the full third density minus
the two genuine savings, each once, with one attachment reserve. -/
theorem exists_p4a_historicalFifth_physical_le_causalLedger_reserve
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
            D.p4aHistoricalPhysicalDensity .fifth N cap w z L ≤
              D.p4aHistoricalRawDensity .third N cap 0 z -
                actualHistoricalFourthSaving
                  (ordinaryParityRosserPolicy false ((N : ℝ) ^ (D.old : ℝ)))
                  (D.level3 (N : ℝ)) (D.level4 (N : ℝ)) N cap z -
                actualHistoricalFifthSaving
                  (ordinaryParityRosserPolicy false ((N : ℝ) ^ (D.old : ℝ)))
                  (D.level3 (N : ℝ)) (D.level4 (N : ℝ)) (D.level5 (N : ℝ)) N cap z +
                eta * singularSeries N / Real.log (N : ℝ) := by
  obtain ⟨epsilon, hepsilon, hepsilon8, hepsilonMax', hepsilonr,
      N₀, hN₀, hbound⟩ := exists_p4a_historicalFifth_physical_le_fullRaw_reserve
    nu r eta epsilonMax hnu hr heta hepsilonMax
  refine ⟨epsilon, hepsilon, hepsilon8, hepsilonMax', hepsilonr, N₀, hN₀, ?_⟩
  intro N hN hEven cap hcap D hab hcheck
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have h := hbound N hN hEven cap hcap D
  dsimp only at h ⊢
  rw [D.p4a_historicalFifth_fullRaw_eq_causalLedger hab hcheck N cap hN1] at h
  exact h

/-- The literal physical rho, not a difference of physical densities.
All target deletions, small weights, rough cutoffs and caps are unchanged. -/
theorem exists_p4a_historicalFifth_actualRho_density_le_causalLedger_reserve
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
            physicalDensitySum
                (actualSmallRoughModuli (D.upperFifthPolicy (N : ℝ) false) N cap w z)
                (actualSmallRoughRho (D.upperFifthPolicy (N : ℝ) false) N cap w z L) ≤
              D.p4aHistoricalRawDensity .third N cap 0 z -
                actualHistoricalFourthSaving
                  (ordinaryParityRosserPolicy false ((N : ℝ) ^ (D.old : ℝ)))
                  (D.level3 (N : ℝ)) (D.level4 (N : ℝ)) N cap z -
                actualHistoricalFifthSaving
                  (ordinaryParityRosserPolicy false ((N : ℝ) ^ (D.old : ℝ)))
                  (D.level3 (N : ℝ)) (D.level4 (N : ℝ)) (D.level5 (N : ℝ)) N cap z +
                eta * singularSeries N / Real.log (N : ℝ) := by
  exact exists_p4a_historicalFifth_physical_le_causalLedger_reserve
    nu r eta epsilonMax hnu hr heta hepsilonMax

/-- At the original historical cutoff, the same fifth physical rho has
the normalized causal ledger with fourth and fifth entries each once. -/
theorem exists_p4a_historicalFifth_physical_normalized_le_causalLedger
    (nu r eta epsilonMax : ℝ) (hnu : 0 < nu) (hr : 0 < r)
    (heta : 0 < eta) (hepsilonMax : 0 < epsilonMax) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 / 8 ∧
      epsilon < epsilonMax ∧ epsilon ^ 2 ≤ r ∧
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
        ∀ cap : ℕ, (N : ℝ) ^ (nu * r) ≤ (cap : ℝ) →
          ∀ D : HistoricalPrefixCapData, D.a ≤ D.b → D.levelCheck = true →
            (D.b : ℝ) = nu * r →
            let w := (N : ℝ) ^ (nu * epsilon ^ 2)
            let z := (N : ℝ) ^ (D.b : ℝ)
            let L := (N : ℝ) ^ (nu * epsilon)
            D.p4aHistoricalPhysicalDensity .fifth N cap w z L *
                Real.log (N : ℝ) / singularSeries N ≤
              D.p4aPolicyDensity (D.upperThirdPolicy (N : ℝ)) N cap z -
                D.p4aFourthEntry N cap z - D.fifthPrimeCorrection N cap + eta := by
  obtain ⟨epsilon, hepsilon, hepsilon8, hepsilonMax', hepsilonr,
      N₀, hN₀, hbound⟩ := exists_p4a_historicalFifth_physical_le_fullRaw_reserve
    nu r eta epsilonMax hnu hr heta hepsilonMax
  refine ⟨epsilon, hepsilon, hepsilon8, hepsilonMax', hepsilonr, N₀, hN₀, ?_⟩
  intro N hN hEven cap hcap D hab hcheck hb
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hS := singularSeries_pos N
  have h := hbound N hN hEven cap hcap D
  dsimp only at h ⊢
  rw [← hb] at h
  have hn := mul_le_mul_of_nonneg_right h (div_nonneg hlog.le hS.le)
  have hreserve : (eta * singularSeries N / Real.log (N : ℝ)) *
      (Real.log (N : ℝ) / singularSeries N) = eta := by
    field_simp [ne_of_gt hlog, ne_of_gt hS]
  rw [add_mul, hreserve] at hn
  have hraw := D.p4a_historicalRawDensity_normalized_eq_policyDensity
    .fifth N cap ((N : ℝ) ^ (D.b : ℝ))
  simp only [HistoricalPrefixCapData.p4aHistoricalPolicy] at hraw
  have hledger := D.p4a_fifth_density_eq_causal_ledger hab hcheck N cap hN1
  simp only [← mul_div_assoc] at hn
  rw [hraw, hledger] at hn
  exact hn

end

end ImbalancedChen
