import ImbalancedChen.CurrentChenPairHarmonicMean
import ImbalancedChen.P3OriginalU5NormalizedDensityReserve
import ImbalancedChen.P3OriginalU5RoundedPairDensity

/-!
# Normalized density reserve summed over the original U5 pairs

The constant-test harmonic limit bounds the total reciprocal-totient weight
of the original selector. Dividing the row budget by this fixed bound pays
the error once across all pairs, with the external pair in each full modulus.
-/

namespace ImbalancedChen.P3OriginalU5PairNormalizedDensityReserve

noncomputable section
open Filter
open scoped BigOperators
open P2OriginalPairSourceReceiver (PairRange)
open P2OriginalLowerWholeBoxBranchSelect (CandidateBank)
open P2OriginalSelectedPairNativeData (selectedPolicy)
open P3OriginalU5NormalizedDensityReserve (exists_rounded_U5_normalized_density_reserve)
open P3OriginalU5RoundedCountInsertion (roundedRho roundedSupport)
open P3OriginalU5RoundedPairDensity (roundedRho_fullModulus_density_eq)
open P5OriginalU5CausalFinite (fullDensity pairSupport)
open P5OriginalU5PlateauPrimeBV (fullModulus)

/-- The original pair selector has eventually bounded reciprocal-totient mass. -/
theorem exists_pairSupport_harmonic_mass_bound :
    ∃ H0 : ℝ, 0 < H0 ∧ ∃ N0 : ℕ, ∀ N ≥ N0,
      (∑ t ∈ pairSupport N, 1 / (Nat.totient (t.1 * t.2) : ℝ)) ≤ H0 := by
  have hlim := tendsto_currentChenUpsilon5_harmonic_test (fun _ => (1 : ℝ)) continuousOn_const
  obtain ⟨H, hH⟩ := hlim.isBoundedUnder_le
  change ∀ᶠ N : ℕ in atTop,
    (∑ t ∈ pairSupport N, 1 / (Nat.totient (t.1 * t.2) : ℝ)) ≤ H at hH
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp hH
  exact ⟨max 1 H, zero_lt_one.trans_le (le_max_left _ _), N0,
    fun N hN => (hN0 N hN).trans (le_max_right _ _)⟩

/-- Common parameters pay one normalized reserve over all original pairs.
The signed double sum and the support cap use the very same rounded rows. -/
theorem exists_rounded_U5_pair_normalized_density_reserve
    (mesh : ℕ) (kappa epsilonMax : ℝ) (hkappa : 0 < kappa) (hmax : 0 < epsilonMax) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 / 8 ∧
      epsilon < epsilonMax ∧ epsilon < 1 / 272 ∧
      ∃ tau0 : ℝ, 0 < tau0 ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
        ∀ N : ℕ, N0 ≤ N → Even N →
          ∀ (R : PairRange) (bank : CandidateBank mesh) (tau : ℝ), 0 < tau → tau ≤ tau0 →
            (∑ t ∈ pairSupport N,
              fullDensity N (selectedPolicy R bank (1 / 1000) false N t) /
                (Nat.totient (t.1 * t.2) : ℝ)) - kappa * singularSeries N / Real.log (N : ℝ) ≤
              (∑ t ∈ pairSupport N, ∑ k ∈ roundedSupport N epsilon,
                roundedRho N epsilon tau (selectedPolicy R bank (1 / 1000) false N t) k /
                  (Nat.totient (fullModulus t k) : ℝ)) ∧
            ∀ t ∈ pairSupport N, ∀ k : ℕ, roundedRho N epsilon tau
                (selectedPolicy R bank (1 / 1000) false N t) k ≠ 0 →
              (fullModulus t k : ℝ) < (N : ℝ) ^ (599 / 1000 : ℝ) := by
  obtain ⟨H0, hH0, Nmass, hmass⟩ := exists_pairSupport_harmonic_mass_bound
  obtain ⟨epsilon, hepsilon, hepsilon8, hepsilonMax, hepsilon272,
      tau0, htau0, Nrow, hNrow, hrow⟩ :=
    exists_rounded_U5_normalized_density_reserve mesh (kappa / H0) epsilonMax
      (div_pos hkappa hH0) hmax
  refine ⟨epsilon, hepsilon, hepsilon8, hepsilonMax, hepsilon272, tau0, htau0,
    max Nrow Nmass, hNrow.trans (le_max_left _ _), ?_⟩
  intro N hN hEven R bank tau htau hsmall
  have hNr : Nrow ≤ N := (le_max_left _ _).trans hN
  have hNm : Nmass ≤ N := (le_max_right _ _).trans hN
  have hN2 : 2 ≤ N := hNrow.trans hNr
  have hNreal : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlog := Real.log_pos hNreal
  let keep (t : ℕ × ℕ) := selectedPolicy R bank (1 / 1000) false N t
  let d (t : ℕ × ℕ) : ℝ := Nat.totient (t.1 * t.2)
  let loss := (kappa / H0) * singularSeries N / Real.log (N : ℝ)
  have hloss : 0 ≤ loss :=
    (div_pos (mul_pos (div_pos hkappa hH0) (singularSeries_pos N)) hlog).le
  have hpaid : (∑ t ∈ pairSupport N, loss / d t) ≤ kappa * singularSeries N / Real.log (N : ℝ) := by
    calc
      _ = loss * (∑ t ∈ pairSupport N, 1 / d t) := by
        simp only [Finset.mul_sum, div_eq_mul_inv, one_mul]
      _ ≤ loss * H0 := mul_le_mul_of_nonneg_left (hmass N hNm) hloss
      _ = _ := by
        dsimp only [loss]
        field_simp [hH0.ne', hlog.ne']
  refine ⟨?_, fun t ht => (hrow N hNr hEven R bank t ht tau htau hsmall).2⟩
  calc
    _ ≤ (∑ t ∈ pairSupport N, fullDensity N (keep t) / d t) -
        ∑ t ∈ pairSupport N, loss / d t := sub_le_sub_left hpaid _
    _ = ∑ t ∈ pairSupport N, (fullDensity N (keep t) / d t - loss / d t) := by
      rw [Finset.sum_sub_distrib]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro t ht
      rw [← sub_div, roundedRho_fullModulus_density_eq hN2 hepsilon hepsilon8 ht tau (keep t)]
      exact div_le_div_of_nonneg_right (hrow N hNr hEven R bank t ht tau htau hsmall).1
        (Nat.cast_nonneg _)

end
end ImbalancedChen.P3OriginalU5PairNormalizedDensityReserve
