import ImbalancedChen.P4AActualBufferedFallbackCapPayment
import ImbalancedChen.P4ACatalogFiveCoarseWeightedPayment
import ImbalancedChen.P4ACatalogFiveHistoricalPairBoundaryPayment
import ImbalancedChen.P4AOriginalBufferedArchiveContinuation

/-!
SOURCE ONLY / UNCOMPILED / KERNEL UNVERIFIED / ZERO FORMAL CREDIT.

A concrete PARTIAL density-error catalogue on one original archive data set.
It consumes R07's actual coarseRow and untrimmed historical endpoint payments
and R08's preservation of both original archive gains.  The Q22 cap payment
uses the same data and one later mesh/buffer; all choices still precede N.

The three paid components are distinct: rawLevel versus v(first), historical
endpoint versus its full integral, and the buffered fallback caps versus
v(second)/v(second+third).  The endpoint comparison is not added twice.
Its omittedRow terms (especially disabled-small-third), full higher-cap
source conversion, actual complete density telescope, and the separate
compiler reserve remain outside this catalogue.  No hdensity, All22,
unproved total-error bound, or replacement of a fifth debt is an input.
-/

namespace ImbalancedChen.P4AActualLocalDensityCatalogue

noncomputable section
open scoped Classical BigOperators
open P5OriginalCommonRefinedConstructor P4AOriginalCausalHistory
open P1Pair12RetainedSignedSource P5OriginalCommonFourthSourceNavigation
open P4AOriginalBufferedFallbackCaps P4AOriginalBufferedArchiveContinuation
open P4AActualBufferedFallbackCapPayment
open P4ACatalogFiveCoarseWeightedPayment P4ACatalogFiveHistoricalPairBoundaryPayment

/-- All terms are in log(N)/C_N normalized density units. The cap terms
use the original enumeration cap N. No unspecified error is a field. -/
def localDensityError (d : OriginalData) (m : ℕ) (buffer a : ℝ) (N : ℕ) : ℝ :=
  coarseAbsoluteSum d N +
    |normalizedHistoricalEndpoint d N - P4AOriginalSecondPhysicalIntegral.physicalSaving| +
    secondCapDefect d m buffer a N N + thirdCapDefect d m buffer a N N

/-- The actual original fourth/fifth bank, complete coarse discrepancy,
untrimmed endpoint and Q22 cap errors share one data set and one N0.

The two positive widths are selected before the old archive parameters.
Their remaining conditions are literal buffer/mesh inequalities, not
error estimates.  Once old data meet them, the new m/buffer are selected;
R08's signed gain identities hold for those very witnesses and all full-q
terminal tests.  Three proved components each receive eta/3 exactly once.
This is not a bound for the complete original physical rho. -/
theorem exists_original_archive_local_density_catalogue
    (a eta : ℝ) (ha : 0 < a) (harho : a < (19 / 96 : ℝ)) (heta : 0 < eta) :
    ∃ coarseWidth : ℝ, 0 < coarseWidth ∧
      ∃ endpointWidth : ℝ, 0 < endpointWidth ∧
      ∀ (e : ℚ) (q : ℕ) (chi omega : ℝ),
      let s := originalSchedule e q chi omega
      let d := s.data
      a ≤ d.omega → 0 < (d.e : ℝ) → (d.e : ℝ) < (3 / 256 : ℝ) / 100 →
      d.chi < (d.e : ℝ) / 10 →
      (3 / 2 : ℝ) * d.chi + 2 * (d.e : ℝ) ≤ coarseWidth →
      4 * (d.e : ℝ) + P4ACatalogFiveHistoricalCoverage.meshStep d.m ≤ endpointWidth →
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
          localDensityError d m buffer a N < eta := by
  have heta3 : 0 < eta / 3 := by positivity
  obtain ⟨coarseWidth, hc, Nc, hNc, hcoarse⟩ :=
    exists_complete_coarseRow_payment a (eta / 3) ha harho heta3
  obtain ⟨endpointWidth, hew, Ne, hNe, hend⟩ :=
    exists_historical_endpoint_approx_integral (eta / 3) heta3
  refine ⟨coarseWidth, hc, endpointWidth, hew, ?_⟩
  intro e q chi omega
  dsimp only
  intro homega he hesmall hchi hcw hew'
  let s := originalSchedule e q chi omega
  let d := s.data
  obtain ⟨m, buffer, hb, hbe, Nb, hNb, hbuffer⟩ :=
    exists_one_preN_buffered_fallback_cap_payment d he a (eta / 3) ha harho heta3
  refine ⟨m, buffer, hb, hbe, ?_, max Nc (max Ne Nb),
    hNc.trans (le_max_left _ _), ?_⟩
  · intro N hN weight T carrier
    exact original_archives_two_signed_gains e q chi omega m buffer N hN weight T carrier
  · intro N hN hEven
    have hNC : Nc ≤ N := (le_max_left _ _).trans hN
    have hNE : Ne ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
    have hNB : Nb ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
    have hN2 : 2 ≤ N := hNb.trans hNB
    have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    have hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (N : ℝ) := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hNr
        (by norm_num : (19 / 96 : ℝ) ≤ 1)
    have hC := hcoarse d homega he hesmall hchi hcw N hNC hEven
    have hE := hend d he.le hew' N hNE hEven
    have hB := hbuffer N hNB hEven N hcap
    dsimp only [localDensityError]
    linarith only [hC, hE, hB]

end
end ImbalancedChen.P4AActualLocalDensityCatalogue
