import ImbalancedChen.P3OriginalU5RoundedPrimeCorrection

/-!
# Same-parameter density reserve in the actual rounded U5 count

The pair density reserve and the full-modulus cap choose one rounded output.
The elementary prime-divisor and centre corrections are paid at that cap,
uniformly in every later receiver and bank. The remaining primitive error
is the signed discrepancy of exactly this output.

This does not assert a positive selected-policy main term or a distribution
estimate for the displayed signed primitive sum. Those are separate P3.6
obligations; no admission or PP premise is hidden in the conclusion.
-/

namespace ImbalancedChen.P3OriginalU5RoundedCountReserve

noncomputable section
open Filter
open scoped BigOperators
open P2OriginalPairSourceReceiver (PairRange)
open P2OriginalLowerWholeBoxBranchSelect (CandidateBank)
open P2OriginalSelectedPairNativeData (selectedPolicy)
open P3OriginalU5RoundedCountInsertion (roundedRho rowSignedPrimitive)
open P3OriginalU5PairNormalizedDensityReserve
  (exists_rounded_U5_pair_normalized_density_reserve)
open P3OriginalU5RoundedPrimeCorrection
  (correctionCost eventually_uniform_correction_payment
    original_U5_rounded_main_sub_correction_lower)
open P5OriginalU5CausalFinite (fullDensity fullProjectedMainSum pairSupport)
open P5OriginalU5PlateauPrimeBV (Policy fullModulus)

/-- The raw pair main term plus the same rounded signed primitive error,
less the density and elementary correction budgets, lower-bounds the original
count. The cap and correction bound use exactly the same selected policy. -/
theorem exists_original_U5_rounded_count_reserve
    (mesh : ℕ) (kappa eta epsilonMax : ℝ)
    (hkappa : 0 < kappa) (heta : 0 < eta) (hmax : 0 < epsilonMax) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 / 8 ∧
      epsilon < epsilonMax ∧ epsilon < 1 / 272 ∧
      ∃ tau0 : ℝ, 0 < tau0 ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
        ∀ N : ℕ, N0 ≤ N → Even N →
          ∀ (R : PairRange) (bank : CandidateBank mesh) (tau : ℝ), 0 < tau → tau ≤ tau0 →
            (fullProjectedMainSum N (selectedPolicy R bank (1 / 1000) false N) -
                ((chenPrimePrefix N).card : ℝ) *
                  (kappa * singularSeries N / Real.log (N : ℝ)) +
                (∑ t ∈ pairSupport N, rowSignedPrimitive N epsilon tau
                  (selectedPolicy R bank (1 / 1000) false N t) t) -
                eta * singularNormalization N ≤ currentChenUpsilon5 N) ∧
            correctionCost N epsilon tau (selectedPolicy R bank (1 / 1000) false N) ≤
              eta * singularNormalization N ∧
            ∀ t ∈ pairSupport N, ∀ k : ℕ, roundedRho N epsilon tau
                (selectedPolicy R bank (1 / 1000) false N t) k ≠ 0 →
              (fullModulus t k : ℝ) < (N : ℝ) ^ (599 / 1000 : ℝ) := by
  obtain ⟨epsilon, hepsilon, hepsilon8, hepsilonMax, hepsilon272,
      tau0, htau0, Nden, hNden, hden⟩ :=
    exists_rounded_U5_pair_normalized_density_reserve mesh kappa epsilonMax hkappa hmax
  obtain ⟨Ncorr, hcorr⟩ := eventually_atTop.mp
    (eventually_uniform_correction_payment eta heta)
  refine ⟨epsilon, hepsilon, hepsilon8, hepsilonMax, hepsilon272,
    tau0, htau0, max Nden Ncorr, hNden.trans (le_max_left _ _), ?_⟩
  intro N hN hEven R bank tau htau hsmall
  have hNd : Nden ≤ N := (le_max_left _ _).trans hN
  have hNc : Ncorr ≤ N := (le_max_right _ _).trans hN
  have hN2 : 2 ≤ N := hNden.trans hNd
  let policy : Policy := selectedPolicy R bank (1 / 1000) false N
  have hreserve := hden N hNd hEven R bank tau htau hsmall
  have hpaid := hcorr N hNc epsilon tau policy hreserve.2
  have hcount := original_U5_rounded_main_sub_correction_lower
    hN2 hepsilon hepsilon8 tau policy
  have hmain := mul_le_mul_of_nonneg_left hreserve.1
    (Nat.cast_nonneg (chenPrimePrefix N).card : (0 : ℝ) ≤ (chenPrimePrefix N).card)
  have hmainId : fullProjectedMainSum N policy =
      ((chenPrimePrefix N).card : ℝ) *
        (∑ t ∈ pairSupport N, fullDensity N (policy t) /
          (Nat.totient (t.1 * t.2) : ℝ)) := by
    rw [fullProjectedMainSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    ring
  refine ⟨?_, hpaid, hreserve.2⟩
  change fullProjectedMainSum N policy -
      ((chenPrimePrefix N).card : ℝ) *
        (kappa * singularSeries N / Real.log (N : ℝ)) +
      (∑ t ∈ pairSupport N, rowSignedPrimitive N epsilon tau (policy t) t) -
      eta * singularNormalization N ≤ currentChenUpsilon5 N
  rw [hmainId]
  linarith only [hmain, hcount, hpaid]

end
end ImbalancedChen.P3OriginalU5RoundedCountReserve
