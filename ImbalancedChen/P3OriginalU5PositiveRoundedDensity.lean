import ImbalancedChen.P3OriginalU5SelectedDensityLower
import ImbalancedChen.P3OriginalU5PairNormalizedDensityReserve

/-! A positive signed rounded density on the complete original U5 pair carrier,
with the physical modulus bound for the same rounding parameters. -/

namespace ImbalancedChen.P3OriginalU5PositiveRoundedDensity

noncomputable section
open scoped Classical BigOperators
open P2OriginalPairSourceReceiver (PairRange)
open P2OriginalLowerWholeBoxBranchSelect (CandidateBank)
open P2OriginalSelectedPairNativeData (selectedPolicy)
open P3OriginalU5PairNormalizedDensityReserve (exists_rounded_U5_pair_normalized_density_reserve)
open P3OriginalU5RoundedCountInsertion (roundedRho roundedSupport)
open P3OriginalU5SelectedDensityLower (exists_original_U5_selected_pair_lower)
open P5OriginalU5CausalFinite (pairSupport)
open P5OriginalU5PlateauPrimeBV (fullModulus)

/-- The positive constant is uniform in the mesh. For each mesh and permitted
rounding cutoff, the same witnesses give the signed lower bound and a strict
cap on every nonzero complete physical modulus. -/
theorem exists_original_U5_positive_rounded_density (R : PairRange) :
    ∃ c : ℝ, 0 < c ∧ ∀ (mesh : ℕ) (epsilonMax : ℝ), 0 < epsilonMax →
      ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 / 8 ∧
        epsilon < epsilonMax ∧ epsilon < 1 / 272 ∧
        ∃ tau0 : ℝ, 0 < tau0 ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
          ∀ N ≥ N0, Even N → ∀ (bank : CandidateBank mesh) (tau : ℝ),
            0 < tau → tau ≤ tau0 →
            c * singularSeries N / Real.log (N : ℝ) ≤
              (∑ t ∈ pairSupport N, ∑ k ∈ roundedSupport N epsilon,
                roundedRho N epsilon tau (selectedPolicy R bank (1 / 1000) false N t) k /
                  (Nat.totient (fullModulus t k) : ℝ)) ∧
            ∀ t ∈ pairSupport N, ∀ k : ℕ, roundedRho N epsilon tau
                (selectedPolicy R bank (1 / 1000) false N t) k ≠ 0 →
              (fullModulus t k : ℝ) < (N : ℝ) ^ (599 / 1000 : ℝ) := by
  obtain ⟨c, hc, Ns, hNs, hselected⟩ := exists_original_U5_selected_pair_lower R
  refine ⟨c / 2, half_pos hc, ?_⟩
  intro mesh epsilonMax hmax
  obtain ⟨epsilon, he, he8, heMax, he272, tau0, htau0, Nr, _, hrounded⟩ :=
    exists_rounded_U5_pair_normalized_density_reserve mesh (c / 2) epsilonMax (half_pos hc) hmax
  refine ⟨epsilon, he, he8, heMax, he272, tau0, htau0, max Ns Nr, hNs.trans (le_max_left _ _), ?_⟩
  intro N hN hEven bank tau htau hsmall
  have hs := hselected N ((le_max_left _ _).trans hN) hEven bank (1 / 1000) (by norm_num) le_rfl
  obtain ⟨hr, hcap⟩ := hrounded N ((le_max_right _ _).trans hN) hEven R bank tau htau hsmall
  refine ⟨?_, hcap⟩
  calc
    c / 2 * singularSeries N / Real.log (N : ℝ) =
        c * singularSeries N / Real.log (N : ℝ) - c / 2 * singularSeries N / Real.log (N : ℝ) := by ring
    _ ≤ _ := (sub_le_sub_right hs _).trans hr

end
end ImbalancedChen.P3OriginalU5PositiveRoundedDensity
