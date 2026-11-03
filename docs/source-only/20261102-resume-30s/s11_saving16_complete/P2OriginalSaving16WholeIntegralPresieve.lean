import ImbalancedChen.P4AOriginalArchiveFourteenPositivePresieve
import ImbalancedChen.P2OriginalSaving16Full87SourceBinding

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

An actual original-fourth/fifth archive schedule supplies the WHOLE
original fourteen-source integral in the positive-presieve envelope.
This uses the ordinary whole-family supplier (including its harmful
complement), rather than merely replacing that integral by its Q96 floor.
The actual beta supplier is applied to one complete new tree. The
ordinary comparison and beta error consume eta/2 each, once.

The tree here remains R06's literal fourteen splice on its concrete
policy6. Full-sixth/full87 chronology and the final signed compiler are
separate obligations; this file makes no equality claim for those trees.
-/

namespace ImbalancedChen.P2OriginalSaving16WholeIntegralPresieve

noncomputable section
open scoped Classical BigOperators
open MeasureTheory VariableEnvelope
open P4AOriginalArchiveFourteenPositivePresieve
open P5OriginalCommonRefinedConstructor P5OriginalCommonPositivePresieve
open P5OriginalFourthFifthSourceInputs
open P4AOriginalCommonArchiveSchedule P4AOriginalCausalHistory
open P5OriginalCommonFourthFallbackExcision P5OriginalCommonFourthSourceNavigation
open P2OriginalSaving16FourteenPhysicalAtlas P2OriginalFourteenWeightedTrim
open P2OriginalAscendingEighthCapDictionary P2OriginalSaving16TrimmedHistory

/-- Concrete whole-integral envelope, with ONE archive/history schedule
and the original full-q fourth/fifth signed sources on that schedule.
There is no source-integral, endpoint, bank, geometry, history, beta-error
or saving estimate among the hypotheses. The only parameters are the
original positive precision/support choices preceding N. -/
theorem exists_original_bank_whole_integral_schedule
    (nu eta betaMax : ℝ) (hnu : 0 < nu) (heta : 0 < eta) (hbetaMax : 0 < betaMax) :
    ∃ beta : ℝ, 0 < beta ∧ beta < 1 / 8 ∧ beta < betaMax ∧
      beta ^ 2 ≤ (19 / 96 : ℝ) / nu ∧
      ∃ n : ℕ, ∃ e0 : ℝ, 0 < e0 ∧ e0 ≤ 11 / 64000 ∧
        ∀ e : ℚ, 0 < e → (e : ℝ) < e0 → ∀ omega : ℝ, omega ≤ 1 / 100 →
          ∃ q N0 : ℕ, 0 < q ∧ 2 ≤ N0 ∧
            FourteenHistory (schedule e q omega) (width n) ∧
            (∀ N cap : ℕ, N0 ≤ N → Even N →
              (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ) →
              let w := (N : ℝ) ^ (nu * beta ^ 2)
              let z := (N : ℝ) ^ (19 / 96 : ℝ)
              let L := (N : ℝ) ^ (nu * beta)
              1 < w ∧ w ≤ z ∧
                |(∫ t in region, sourceDensity t) -
                  (∫ t in trimmedRegion (width n), sourceDensity t)| < eta / 8 ∧
                normalize N (physical (fourteenPolicy e q omega (N : ℝ)) N cap w z L) <
                  normalize N (raw (policy6 (data e q omega) (N : ℝ)) N cap 0 z) -
                    (∫ t in region, sourceDensity t) + eta) ∧
            (∀ N cap : ℕ, 1 ≤ (N : ℝ) → ∀ w z L : ℝ, ∀ G : ℕ → ℝ,
              let d := data e q omega
              let T := P1Pair12RetainedSignedSource.attachedLeafTest N cap 1 w L G
              let carrier := roughPrimeUniverse N cap w z
              P5OriginalCommonRefinedSource.sourceChange d .fourth N cap w z L G =
                P1Pair12RetainedSignedSource.signedTest
                  (P5OriginalCommonFourthSourceNavigation.original4 d (N : ℝ))
                  (fun _ => 1) T [] true 1 carrier -
                P1Pair12RetainedSignedSource.signedTest
                  (P5OriginalCommonRefinedConstructor.old3 d (N : ℝ))
                  (fun _ => 1) T [] true 1 carrier ∧
              P5OriginalCommonRefinedSource.sourceChange d .fifth N cap w z L G =
                P1Pair12RetainedSignedSource.signedTest
                  (P4AOriginalCausalHistory.original5 d (N : ℝ))
                  (fun _ => 1) T [] true 1 carrier -
                P1Pair12RetainedSignedSource.signedTest
                  (P5OriginalCommonFourthSourceNavigation.original4 d (N : ℝ))
                  (fun _ => 1) T [] true 1 carrier) := by
  have hr : 0 < (19 / 96 : ℝ) / nu := div_pos (by norm_num) hnu
  have hnr : nu * ((19 / 96 : ℝ) / nu) = (19 / 96 : ℝ) := by
    field_simp [hnu.ne'] <;> ring
  obtain ⟨beta, hb, hb8, hbMax, hbr, Nb, _hNb, hbeta⟩ :=
    exists_actualSmallRoughRho_density_le_full_reserve
      nu ((19 / 96 : ℝ) / nu) (eta / 2) betaMax hnu hr (half_pos heta) hbetaMax
  obtain ⟨n, e0, he0, he0bound, hschedule⟩ :=
    exists_fixed_archive_and_whole_fourteen_schedule
      originalRows4 originalAdmission4 (fun r _hr hr => originalAdmission4_geometry r hr)
      (eta / 2) (half_pos heta)
  refine ⟨beta, hb, hb8, hbMax, hbr, n, e0, he0, he0bound, ?_⟩
  intro e he hee omega homega
  obtain ⟨q, Ns, hq, hNs, hs⟩ := hschedule e he hee omega homega
  dsimp only at hs
  obtain ⟨hhistory, hordinary, _hfourth, _hfifth⟩ := hs
  refine ⟨q, max Ns Nb, hq, hNs.trans (le_max_left _ _), hhistory, ?_, ?_⟩
  · intro N cap hN hEven hcap
    have hN2 : 2 ≤ N := hNs.trans ((le_max_left _ _).trans hN)
    have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    have hz : (N : ℝ) ^ mu ≤ (N : ℝ) ^ (19 / 96 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hN1.le (by norm_num [mu])
    have hbs := hbeta N ((le_max_right _ _).trans hN) hEven cap
      (by simpa only [hnr] using hcap) (fourteenPolicy e q omega (N : ℝ) false)
    dsimp only at hbs
    simp only [hnr] at hbs
    change physical (fourteenPolicy e q omega (N : ℝ)) N cap
        ((N : ℝ) ^ (nu * beta ^ 2)) ((N : ℝ) ^ (19 / 96 : ℝ)) ((N : ℝ) ^ (nu * beta)) ≤
      raw (fourteenPolicy e q omega (N : ℝ)) N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ)) +
        (eta / 2) * singularSeries N / Real.log (N : ℝ) at hbs
    have hnorm := normalize_mono N hN2 hbs
    rw [normalize_add, normalize_reserve N hN2] at hnorm
    obtain ⟨htrim, hlower⟩ := hordinary N cap ((le_max_left _ _).trans hN) hEven
      ((N : ℝ) ^ (19 / 96 : ℝ)) hz hcap
    change (∫ t in region, sourceDensity t) - eta / 2 <
      normalize N (P2OriginalFourteenSignedParentLedger.charge N cap 0
        ((N : ℝ) ^ (19 / 96 : ℝ)) (lambda6 (data e q omega) (N : ℝ))
        P4AOriginalAscending14Literal42.literalPattern
        (policy5 (data e q omega) (N : ℝ))) at hlower
    rw [← raw_current_sub_fourteen_eq_original_charge, normalize_sub] at hlower
    dsimp only
    refine ⟨Real.one_lt_rpow hN1 (mul_pos hnu (sq_pos_of_pos hb)), ?_, ?_, ?_⟩
    · apply Real.rpow_le_rpow_of_exponent_le hN1.le
      simpa only [hnr] using mul_le_mul_of_nonneg_left hbr hnu.le
    · convert htrim using 1 <;> ring
    · linarith only [hnorm, hlower]
  · intro N cap hN w z L G
    exact original_fourth_fifth_attached_sources e q omega N cap hN w z L G

end
end ImbalancedChen.P2OriginalSaving16WholeIntegralPresieve
