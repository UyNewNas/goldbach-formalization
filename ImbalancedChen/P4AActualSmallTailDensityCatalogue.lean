import ImbalancedChen.P4AActualLocalDensityCatalogue
import ImbalancedChen.P4ACatalogFiveGlobalLossReduction

/-!
SOURCE ONLY / UNCOMPILED / KERNEL UNVERIFIED / ZERO FORMAL CREDIT.

R07's actual catalogue-five identity now pays the complete coarseRow,
historical endpoint replacement and compact order omission.  The remaining
small-third omittedRow sum is retained literally.  Its absolute value is
NOT assumed small.  This file combines the actual paid part with R10's
two finite fallback cap errors on one original archive data set, keeping
R08's two original archive gains for the same selected m and buffer.

This is a stronger PARTIAL catalogue, alternative to localDensityError.
The two catalogues are not added together: their coarse and endpoint costs
overlap.  No full-policy signed dictionary, full87 equality, fifth-debt
payment or compiler estimate is asserted by this construction.
-/

namespace ImbalancedChen.P4AActualSmallTailDensityCatalogue

noncomputable section
open scoped Classical BigOperators
open P5OriginalCommonRefinedConstructor P4AOriginalCausalHistory
open P1Pair12RetainedSignedSource P5OriginalCommonFourthSourceNavigation
open P4AOriginalBufferedFallbackCaps P4AOriginalBufferedArchiveContinuation
open P4AActualBufferedFallbackCapPayment P4ACatalogFiveGlobalLossReduction
open P4ACatalogFiveOmittedOrderPayment P4AOriginalSecondPhysicalIntegral

/-- Actual source-saving error together with the two separately defined
fallback cap errors. No complete-policy density is identified with this. -/
def catalogFiveCapError (d : OriginalData) (m : ℕ) (buffer a : ℝ) (N : ℕ) : ℝ :=
  |normalizedActualSaving d N - physicalSaving| +
    secondCapDefect d m buffer a N N + thirdCapDefect d m buffer a N N

/-- The explicitly paid part. The original signed small omission is
inside the source comparison, as in R07's exact decomposition. -/
def tailReducedDensityError (d : OriginalData) (m : ℕ) (buffer a : ℝ) (N : ℕ) : ℝ :=
  |normalizedActualSaving d N + smallOmittedSum d a N - physicalSaving| +
    secondCapDefect d m buffer a N N + thirdCapDefect d m buffer a N N

/-- The sole unestimated term in this catalogue is displayed with its
actual sign-independent absolute cost. It has not been discarded. -/
theorem catalogFiveCapError_le_paid_add_smallOmission
    (d : OriginalData) (m : ℕ) (buffer a : ℝ) (N : ℕ) :
    catalogFiveCapError d m buffer a N ≤
      tailReducedDensityError d m buffer a N + |smallOmittedSum d a N| := by
  have htri : |normalizedActualSaving d N - physicalSaving| ≤
      |normalizedActualSaving d N + smallOmittedSum d a N - physicalSaving| +
        |smallOmittedSum d a N| := by
    calc
      _ = |(normalizedActualSaving d N + smallOmittedSum d a N - physicalSaving) -
          smallOmittedSum d a N| := by congr 1 <;> ring
      _ ≤ _ := abs_sub _ _
  dsimp only [catalogFiveCapError, tailReducedDensityError]
  linarith only [htri]

/-- One original archive data set, one new fallback mesh/buffer, one N0.
The supplied R07 error gets eta/2, and both cap errors together get eta/2.
The latter's two actual carriers receive eta/4 each inside the supplier.
All remaining assumptions are literal parameter/mesh conditions; no
density estimate or small-tail estimate is a premise.

The final inequality retains the entire actual smallOmittedSum. The
geometric constraints are compatibility conditions on the old schedule,
not a construction satisfying every other upstream schedule obligation. -/
theorem exists_original_archive_small_tail_density_catalogue
    (a eta : ℝ) (ha : 0 < a) (harho : a < (19 / 96 : ℝ)) (heta : 0 < eta) :
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
          tailReducedDensityError d m buffer a N < eta ∧
          catalogFiveCapError d m buffer a N < eta + |smallOmittedSum d a N| := by
  have heta2 : 0 < eta / 2 := half_pos heta
  obtain ⟨delta, hd, Ng, hNg, hglobal⟩ :=
    exists_actual_saving_approx_with_small_omission a (eta / 2) ha harho heta2
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
    have hpaid : tailReducedDensityError d m buffer a N < eta := by
      dsimp only [tailReducedDensityError]
      linarith only [hG, hB]
    exact ⟨hpaid, (catalogFiveCapError_le_paid_add_smallOmission d m buffer a N).trans_lt
      (add_lt_add_right hpaid _)⟩

end
end ImbalancedChen.P4AActualSmallTailDensityCatalogue
