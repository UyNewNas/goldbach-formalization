import ImbalancedChen.P4AActualSmallTailDensityCatalogue
import ImbalancedChen.P4ACatalogFiveSmallThirdPayment

/-!
SOURCE ONLY / UNCOMPILED / KERNEL UNVERIFIED / ZERO FORMAL CREDIT.

The actual R07 complete catalogue-five supplier pays its full original
small-third occurrence sum. It selects the cutoff bound before the old
schedule, widths and target; no physical-gap or tail-payment hypothesis
is required. This file consumes that supplier at eta/2 and R10's two
actual buffered fallback cap payments together at eta/2.

The result concerns the SAME catalogFiveCapError defined in the earlier
file, now with no unpaid tail. The earlier partial catalogues remain valid
but are alternatives: their costs must not be added to this payment.
R08's complete original fourth/fifth gains use these same m and buffer.

This is a complete payment of the displayed catalogue-five-plus-cap
quantity, not of the full finite policy or the remaining 3*u_d/4. The
full87 source dictionary, fifth old defect and independent compiler u_c
remain separate. No actual full-policy hdensity is assumed or concluded.
-/

namespace ImbalancedChen.P4AActualCompleteCatalogFiveCapPayment

noncomputable section
open scoped Classical BigOperators
open P5OriginalCommonRefinedConstructor P4AOriginalCausalHistory
open P1Pair12RetainedSignedSource P5OriginalCommonFourthSourceNavigation
open P4AOriginalBufferedFallbackCaps P4AOriginalBufferedArchiveContinuation
open P4AActualBufferedFallbackCapPayment P4AActualSmallTailDensityCatalogue
open P4ACatalogFiveSmallThirdPayment

/-- Requested error, then a positive small-cutoff bound, then any allowed
cutoff a, common original-data width, actual old schedule, one new finite
mesh/buffer, and finally N0. All actual losses are supplied, not assumed.

R07 receives eta/2 for the entire original catalogue-five saving error;
the second and third buffered cap defects each receive eta/4. Original
fourth/fifth signed gains are preserved for the very same witnesses.
The literal old-data conditions do not claim to satisfy every obligation
of the still-missing global full87 schedule. -/
theorem exists_original_archive_complete_catalog5_cap_payment
    (eta : ℝ) (heta : 0 < eta) :
    ∃ a0 : ℝ, 0 < a0 ∧ a0 < (19 / 96 : ℝ) ∧
      ∀ a : ℝ, 0 < a → a ≤ a0 →
      ∃ delta : ℝ, 0 < delta ∧
      ∀ (e : ℚ) (q : ℕ) (chi omega : ℝ),
      let s := originalSchedule e q chi omega
      let d := s.data
      d.omega = a → 0 < (d.e : ℝ) → (d.e : ℝ) < (3 / 256 : ℝ) / 100 →
      d.chi < (d.e : ℝ) / 10 →
      P4ACatalogFiveHistoricalCoverage.meshStep d.m ≤ d.chi →
      4 * (d.e : ℝ) + P4ACatalogFiveHistoricalCoverage.meshStep d.m ≤ delta →
      (3 / 2 : ℝ) * d.chi + 2 * (d.e : ℝ) ≤ delta →
      2 * P4ACatalogFiveHistoricalCoverage.meshStep d.m ≤ delta →
      ∃ m : ℕ, ∃ buffer : ℚ, 0 < (buffer : ℝ) ∧
        (buffer : ℝ) ≤ 2 * (d.e : ℝ) ∧
        (∀ N : ℝ, 1 ≤ N → ∀ (weight : ℕ → ℝ) (T : Bool → List ℕ → ℝ)
          (carrier : List ℕ),
          (signedTest (bufferedThirdPolicy d m buffer N) weight T [] true 1 carrier -
              signedTest (fourthPolicy d m buffer N) weight T [] true 1 carrier =
            signedTest (old3 d N) weight T [] true 1 carrier -
              signedTest (original4 d N) weight T [] true 1 carrier) ∧
          (signedTest (fourthPolicy d m buffer N) weight T [] true 1 carrier -
              signedTest (fifthPolicy s m buffer N) weight T [] true 1 carrier =
            signedTest (original4 d N) weight T [] true 1 carrier -
              signedTest (original5 d N) weight T [] true 1 carrier)) ∧
        ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
          catalogFiveCapError d m buffer a N < eta := by
  have heta2 : 0 < eta / 2 := half_pos heta
  obtain ⟨a0, ha0, ha0rho, hcutoff⟩ :=
    exists_complete_actual_catalog5_approx (eta / 2) heta2
  refine ⟨a0, ha0, ha0rho, ?_⟩
  intro a ha haa0
  have harho : a < (19 / 96 : ℝ) := haa0.trans_lt ha0rho
  obtain ⟨delta, hd, Ng, hNg, hglobal⟩ := hcutoff a ha haa0
  refine ⟨delta, hd, ?_⟩
  intro e q chi omega
  dsimp only
  intro homega he hesmall hchi hmesh hp hc ho
  let s := originalSchedule e q chi omega
  let d := s.data
  obtain ⟨m, buffer, hb, hbe, Nb, hNb, hbuffer⟩ :=
    exists_one_preN_buffered_fallback_cap_payment d he a (eta / 2) ha harho heta2
  refine ⟨m, buffer, hb, hbe, ?_, max Ng Nb, hNg.trans (le_max_left _ _), ?_⟩
  · intro N hN weight T carrier
    exact original_archives_two_signed_gains e q chi omega m buffer N hN weight T carrier
  · intro N hN hEven
    have hNG : Ng ≤ N := (le_max_left _ _).trans hN
    have hNB : Nb ≤ N := (le_max_right _ _).trans hN
    have hN2 : 2 ≤ N := hNb.trans hNB
    have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    have hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (N : ℝ) := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hNr
        (by norm_num : (19 / 96 : ℝ) ≤ 1)
    have hG := hglobal d homega he hesmall hchi hmesh hp hc ho N hNG hEven
    have hB := hbuffer N hNB hEven N hcap
    dsimp only [catalogFiveCapError]
    linarith only [hG, hB]

end
end ImbalancedChen.P4AActualCompleteCatalogFiveCapPayment
