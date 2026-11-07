import ImbalancedChen.P4ACompactPhysicalIntegralLedger
import ImbalancedChen.P4AOrdinaryRootFirstIntegral

/-!
SOURCE ONLY / UNCOMPILED.

This assembles the real attached physical density with the exact ordinary-root
dictionary and P2's actual full-domain positive-series enclosure. All compact
parameters and the support constraint epsilon <= 2*e are retained in the same
existential witness. There is no selected U1 endpoint, K premise, or numerical
replay; n is arbitrary.

Draft staging:
* ../P4ACompactPhysicalIntegralLedger.lean.txt ->
  ImbalancedChen/P4ACompactPhysicalIntegralLedger.lean
* P4AOrdinaryRootFirstIntegral.lean.txt ->
  ImbalancedChen/P4AOrdinaryRootFirstIntegral.lean
* this file -> ImbalancedChen/P4AOriginalRootPhysicalSeriesLedger.lean
-/

namespace ImbalancedChen.P4AOriginalRootPhysicalSeriesLedger20261024zSourceOnly

noncomputable section

open P4ASameRhoCompact OriginalThirdFiniteReserveSourceOnly
open P4AOrdinaryRootFirstIntegral20261024zSourceOnly
open P2FirstIntegralSeriesSourceOnly

/-- Actual U1 form of the physical ledger, for direct later all22 substitution.
The identity rewrites the entire existing existence theorem, retaining its one
common compact policy, attachment precision, and eventual target threshold. -/
theorem exists_actual_physical_density_le_actual_U1_integral_ledger
    (eta : ℝ) (heta : 0 < eta) :
    ∃ h : ℝ, 0 < h ∧ ∃ e : ℝ, 0 < e ∧ e ≤ 1 / 384 ∧ ∃ m : ℕ,
      actualExtendedThirdDyadicStep m ≤ e / 2 ∧
      ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 / 8 ∧ epsilon < 1 ∧
        epsilon ≤ 2 * e ∧ epsilon ^ 2 ≤ thirdPrefixRho ∧
        ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
          physicalDensitySum
              (attachedUpperModuli 1 thirdPrefixRho epsilon (retain e h m) (fun N => N) N)
              (attachedUpperCoefficient 1 thirdPrefixRho epsilon (retain e h m) (fun N => N) N) ≤
            (4 / thirdPrefixTheta + originalFirstIntegral + originalCompactThirdCorrection +
              (319683857488126290909150567 / 2 ^ 111 : ℝ) +
              originalDensityReserve / 4 + eta) *
              (singularSeries N / Real.log (N : ℝ)) := by
  simpa only [originalOrdinaryRoot_eq_constant_add_originalFirstIntegral] using
    P4ACompactPhysicalIntegralLedger.exists_actual_physical_density_le_original_integral_ledger
      eta heta

/-- Replacing actual U1 by its proved series enclosure costs precisely the
existing P2 integral tail. The compact correction and every reserve are literal. -/
theorem actual_U1_ledger_le_series_ledger (n : ℕ) (eta : ℝ) :
    4 / thirdPrefixTheta + originalFirstIntegral + originalCompactThirdCorrection +
        (319683857488126290909150567 / 2 ^ 111 : ℝ) +
        originalDensityReserve / 4 + eta ≤
      4 / thirdPrefixTheta + partialIntegral n + integralTail n +
        originalCompactThirdCorrection +
        (319683857488126290909150567 / 2 ^ 111 : ℝ) +
        originalDensityReserve / 4 + eta := by
  linarith only [(originalFirstIntegral_series_enclosure n).2]

/-- For every series order and positive surplus, one concrete compact policy
and one support-compatible attachment precision control every large even N. -/
theorem exists_actual_physical_density_le_original_root_series_ledger
    (n : ℕ) (eta : ℝ) (heta : 0 < eta) :
    ∃ h : ℝ, 0 < h ∧ ∃ e : ℝ, 0 < e ∧ e ≤ 1 / 384 ∧ ∃ m : ℕ,
      actualExtendedThirdDyadicStep m ≤ e / 2 ∧
      ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 / 8 ∧ epsilon < 1 ∧
        epsilon ≤ 2 * e ∧ epsilon ^ 2 ≤ thirdPrefixRho ∧
        ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
          physicalDensitySum
              (attachedUpperModuli 1 thirdPrefixRho epsilon (retain e h m) (fun N => N) N)
              (attachedUpperCoefficient 1 thirdPrefixRho epsilon (retain e h m) (fun N => N) N) ≤
            (4 / thirdPrefixTheta + partialIntegral n + integralTail n +
              originalCompactThirdCorrection +
              (319683857488126290909150567 / 2 ^ 111 : ℝ) +
              originalDensityReserve / 4 + eta) *
              (singularSeries N / Real.log (N : ℝ)) := by
  obtain ⟨h, hh, e, he, hecap, m, hmesh, epsilon, hepsilon, hepsilon8,
      hepsilon1, hepsilonSupport, hepsilonR, N₀, hN₀, hPhysical⟩ :=
    exists_actual_physical_density_le_actual_U1_integral_ledger eta heta
  refine ⟨h, hh, e, he, hecap, m, hmesh, epsilon, hepsilon, hepsilon8,
    hepsilon1, hepsilonSupport, hepsilonR, N₀, hN₀, ?_⟩
  intro N hN hEven
  have hScale : 0 ≤ singularSeries N / Real.log (N : ℝ) :=
    (densityScale_pos (hN₀.trans hN)).le
  exact (hPhysical N hN hEven).trans
    (mul_le_mul_of_nonneg_right (actual_U1_ledger_le_series_ledger n eta) hScale)

/-- The witnesses may be chosen before n: the same physical compact policy
satisfies all members of the P2 enclosure family simultaneously. -/
theorem exists_actual_physical_density_le_all_original_root_series_ledgers
    (eta : ℝ) (heta : 0 < eta) :
    ∃ h : ℝ, 0 < h ∧ ∃ e : ℝ, 0 < e ∧ e ≤ 1 / 384 ∧ ∃ m : ℕ,
      actualExtendedThirdDyadicStep m ≤ e / 2 ∧
      ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 / 8 ∧ epsilon < 1 ∧
        epsilon ≤ 2 * e ∧ epsilon ^ 2 ≤ thirdPrefixRho ∧
        ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ n N : ℕ, N₀ ≤ N → Even N →
          physicalDensitySum
              (attachedUpperModuli 1 thirdPrefixRho epsilon (retain e h m) (fun N => N) N)
              (attachedUpperCoefficient 1 thirdPrefixRho epsilon (retain e h m) (fun N => N) N) ≤
            (4 / thirdPrefixTheta + partialIntegral n + integralTail n +
              originalCompactThirdCorrection +
              (319683857488126290909150567 / 2 ^ 111 : ℝ) +
              originalDensityReserve / 4 + eta) *
              (singularSeries N / Real.log (N : ℝ)) := by
  obtain ⟨h, hh, e, he, hecap, m, hmesh, epsilon, hepsilon, hepsilon8,
      hepsilon1, hepsilonSupport, hepsilonR, N₀, hN₀, hPhysical⟩ :=
    exists_actual_physical_density_le_actual_U1_integral_ledger eta heta
  refine ⟨h, hh, e, he, hecap, m, hmesh, epsilon, hepsilon, hepsilon8,
    hepsilon1, hepsilonSupport, hepsilonR, N₀, hN₀, ?_⟩
  intro n N hN hEven
  have hScale : 0 ≤ singularSeries N / Real.log (N : ℝ) :=
    (densityScale_pos (hN₀.trans hN)).le
  exact (hPhysical N hN hEven).trans
    (mul_le_mul_of_nonneg_right (actual_U1_ledger_le_series_ledger n eta) hScale)

end

end ImbalancedChen.P4AOriginalRootPhysicalSeriesLedger20261024zSourceOnly
