import ImbalancedChen.P4ACompactConstrainedPrecisionEndpoint
import ImbalancedChen.P4ACompactBaselineLimit
import ImbalancedChen.Part4ActualThirdFiniteDensityReserve

/-!
SOURCEONLY / UNCOMPILED.
An actual physical density endpoint with one fixed compact policy. The
ordinary root and actual compact integral remain unevaluated. Every limit,
attachment and approximation premise is supplied by a proved-source API;
there is no K-bound or physical-density premise.
-/
namespace ImbalancedChen.P4ACompactPhysicalIntegralLedger

noncomputable section
open Filter Topology
open P4ASameRhoCompact OriginalThirdFiniteReserveSourceOnly

/-- The buffer/mesh used for the root approximation also meet the actual
compact approximation thresholds. One common attachment precision is
then selected before every even target. The two surplus halves are the
ordinary-root approximation and physical attachment, respectively. -/
theorem exists_actual_physical_density_le_original_integral_ledger
    (eta : ℝ) (heta : 0 < eta) :
    ∃ h : ℝ, 0 < h ∧ ∃ e : ℝ, 0 < e ∧ e ≤ 1 / 384 ∧ ∃ m : ℕ,
      actualExtendedThirdDyadicStep m ≤ e / 2 ∧
      ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 / 8 ∧ epsilon < 1 ∧
        epsilon ≤ 2 * e ∧ epsilon ^ 2 ≤ thirdPrefixRho ∧
        ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
          physicalDensitySum
              (attachedUpperModuli 1 thirdPrefixRho epsilon (retain e h m) (fun N => N) N)
              (attachedUpperCoefficient 1 thirdPrefixRho epsilon (retain e h m) (fun N => N) N) ≤
            (originalOrdinaryRoot + originalCompactThirdCorrection +
              (319683857488126290909150567 / 2^111 : ℝ) +
              originalDensityReserve / 4 + eta) *
              (singularSeries N / Real.log (N : ℝ)) := by
  have hu : 0 < originalDensityReserve / 4 := by
    norm_num [originalDensityReserve]
  obtain ⟨h, hh, E, hE, _hEcap, M, hApprox⟩ :=
    actualExtendedThirdCompactCellFunctional_uniform_approx hu
  obtain ⟨e, he0, hecap, heE, m, hMm, hmesh, hBase⟩ :=
    exists_legal_baseline_le_original_root_add (eta / 2) E (half_pos heta) hE M
  have hCell := hApprox e he0.le heE.le m hMm
  have hCellUpper : actualExtendedThirdCompactCellFunctional e h m ≤
      originalCompactThirdCorrection +
        (319683857488126290909150567 / 2^111 : ℝ) + originalDensityReserve / 4 := by
    have hdiff := (le_abs_self _).trans hCell
    linarith only [hdiff, idealFunctional_le_compact_add_Tnew]
  obtain ⟨epsilon, hepsilon, hepsilon8, hepsilon1, hepsilonSupport, hepsilonR,
      N₀, hN₀, hPhysical⟩ :=
    exists_attached_physical_density_endpoint_support_precision
      hh he0 hecap hmesh (eta / 2) (half_pos heta)
  refine ⟨h, hh, e, he0, hecap, m, hmesh, epsilon, hepsilon,
    hepsilon8, hepsilon1, hepsilonSupport, hepsilonR, N₀, hN₀, ?_⟩
  intro N hN hEven
  have hScale := (densityScale_pos (hN₀.trans hN)).le
  have hCoefficient : baselineLimit e m + actualExtendedThirdCompactCellFunctional e h m +
      eta / 2 ≤ originalOrdinaryRoot + originalCompactThirdCorrection +
        (319683857488126290909150567 / 2^111 : ℝ) + originalDensityReserve / 4 + eta := by
    linarith only [hBase, hCellUpper]
  exact (hPhysical N hN hEven).trans (mul_le_mul_of_nonneg_right hCoefficient hScale)

end
end ImbalancedChen.P4ACompactPhysicalIntegralLedger
