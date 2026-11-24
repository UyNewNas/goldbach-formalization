import ImbalancedChen.P4AActualCompleteCatalogFiveCapPayment
import ImbalancedChen.P4AOriginalArchiveFourteenPositivePresieve
import ImbalancedChen.P4AOriginalSecondPhysicalIntegral

/-!
SOURCE ONLY / UNCOMPILED / KERNEL UNVERIFIED / ZERO FORMAL CREDIT.

R07 already pays the whole ordinary catalog-five loss; R10 already pays
that loss and the two Q22 cap defects together. Here their literal width
premises are discharged on the actual original byte-backed fourth/fifth
schedule used by R06. The refinement is every q above one threshold,
so later history thresholds can share the same q by taking a maximum.

The result supplies actual slot five, including its sign and occurrence
multiplicity, and preserves the original fourth/fifth signed differences
for the same buffered mesh. It is not a full87 equality or a payment of
either total reserve. Earlier tail-bearing alternatives are not charged.
-/

namespace ImbalancedChen.P4AOriginalCatalogFiveArchiveSchedule

noncomputable section
open Filter Topology
open scoped Classical BigOperators
open P5OriginalCommonRefinedConstructor P4AOriginalCausalHistory
open P1Pair12RetainedSignedSource P5OriginalCommonFourthSourceNavigation
open P4AOriginalBufferedFallbackCaps P4AOriginalBufferedArchiveContinuation
open P4AActualOwnCubeCapPayment P4AActualBufferedFallbackCapPayment
open P4AActualSmallTailDensityCatalogue P4ACatalogFiveGlobalLossReduction
open P4AOriginalSecondPhysicalIntegral
open P4AOriginalArchiveFourteenPositivePresieve

/-- R10 and R06 use exactly the same original archive data when chi=e/20.
This is definitional source identity, not equality of two final policies. -/
theorem original_schedule_eq_fourteen_schedule (e : ℚ) (q : ℕ) (a : ℝ) :
    originalSchedule e q ((e : ℝ) / 20) a = schedule e q a := rfl

theorem second_cap_defect_nonneg (d : OriginalData) (m : ℕ)
    (buffer a : ℝ) (N cap : ℕ) : 0 ≤ secondCapDefect d m buffer a N cap := by
  unfold secondCapDefect capDefect
  apply Finset.sum_nonneg
  intro p hp
  exact mul_nonneg
    (actualPrimeBoxWeight_nonneg (Finset.mem_filter.mp hp).1) (abs_nonneg _)

theorem third_cap_defect_nonneg (d : OriginalData) (m : ℕ)
    (buffer a : ℝ) (N cap : ℕ) : 0 ≤ thirdCapDefect d m buffer a N cap := by
  unfold thirdCapDefect capDefect
  apply Finset.sum_nonneg
  intro p hp
  exact mul_nonneg
    (actualPrimeBoxWeight_nonneg (Finset.mem_filter.mp hp).1) (abs_nonneg _)

/-- These are the actual nonnegative cap charges, so the same combined
payment also bounds the complete original occurrence-source error. -/
theorem catalog_five_source_error_le_cap_error (d : OriginalData)
    (m : ℕ) (buffer a : ℝ) (N : ℕ) :
    |normalizedActualSaving d N - physicalSaving| ≤
      catalogFiveCapError d m buffer a N := by
  dsimp only [catalogFiveCapError]
  linarith only [second_cap_defect_nonneg d m buffer a N N,
    third_cap_defect_nonneg d m buffer a N N]

/-- The original fifth-slot endpoint minus the actual signed source is
bounded by the already-defined combined payment. No error estimate is a
premise, and no second copy of the physical chart gain is introduced. -/
theorem original_slot_five_deficit_le_cap_error (d : OriginalData)
    (m : ℕ) (buffer a : ℝ) (N : ℕ) :
    (640339 / 15210735000 : ℝ) - normalizedActualSaving d N ≤
      catalogFiveCapError d m buffer a N := by
  have hsource := catalog_five_source_error_le_cap_error d m buffer a N
  have habs : physicalSaving - normalizedActualSaving d N ≤
      |normalizedActualSaving d N - physicalSaving| := by
    rw [abs_sub_comm]
    exact le_abs_self _
  linarith only [original_physical_saving_ge_catalog_five, habs, hsource]

/-- Requested eta; small original cutoff; positive old buffer bound; any
rational e below it; one q0; EVERY original grid400 q above q0; then the
same Q22 mesh/buffer and N0. All old-data width premises are proved here.
The two actual original archive differences retain arbitrary terminal test,
weight, incoming signs and list multiplicity through their signed source.

This supplies no equality between the buffered fifth continuation and a
later full87 tree. The last conjunct is the actual catalog-five source,
with the lower endpoint used once in its original slot. -/
theorem exists_actual_original_catalog_five_schedule
    (eta : ℝ) (heta : 0 < eta) :
    ∃ a0 : ℝ, 0 < a0 ∧ a0 < (19 / 96 : ℝ) ∧
      ∀ a : ℝ, 0 < a → a ≤ a0 →
      ∃ e0 : ℝ, 0 < e0 ∧
      ∀ e : ℚ, 0 < e → (e : ℝ) < e0 →
      ∃ q0 : ℕ, 0 < q0 ∧
      ∀ q : ℕ, q0 ≤ q →
      let s := schedule e q a
      let d := data e q a
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
          catalogFiveCapError d m buffer a N < eta ∧
          (640339 / 15210735000 : ℝ) - eta < normalizedActualSaving d N := by
  obtain ⟨a0, ha0, ha0rho, hcutoff⟩ :=
    P4AActualCompleteCatalogFiveCapPayment.exists_original_archive_complete_catalog5_cap_payment
      eta heta
  refine ⟨a0, ha0, ha0rho, ?_⟩
  intro a ha haa0
  obtain ⟨delta, hdelta, hpayment⟩ := hcutoff a ha haa0
  let e0 : ℝ := min ((3 / 256 : ℝ) / 100) (delta / 10)
  have he0 : 0 < e0 := lt_min (by norm_num) (by positivity)
  refine ⟨e0, he0, ?_⟩
  intro e he hee
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have hesmall : (e : ℝ) < (3 / 256 : ℝ) / 100 :=
    hee.trans_le (min_le_left _ _)
  have hedelta : (e : ℝ) < delta / 10 := hee.trans_le (min_le_right _ _)
  have hchi : (0 : ℝ) < (e : ℝ) / 20 := by positivity
  obtain ⟨m0, hm0⟩ := Filter.eventually_atTop.mp
    ((tendsto_logPrimeMeshStep 0 (19 / 96)).eventually (gt_mem_nhds hchi))
  refine ⟨m0 + 1, by omega, ?_⟩
  intro q hq
  let s := schedule e q a
  let d := data e q a
  have hdm : m0 ≤ d.m := by
    change m0 ≤ P1OriginalFifthGrid400RefinedFullBoxCover.refinedMesh q
    unfold P1OriginalFifthGrid400RefinedFullBoxCover.refinedMesh
    omega
  have hmesh : P4ACatalogFiveHistoricalCoverage.meshStep d.m ≤ d.chi := by
    change logPrimeMeshStep 0 (19 / 96) d.m ≤ (e : ℝ) / 20
    exact (hm0 d.m hdm).le
  have hwidth : P4ACatalogFiveHistoricalCoverage.meshStep d.m ≤ (e : ℝ) / 20 := hmesh
  have hp : 4 * (d.e : ℝ) + P4ACatalogFiveHistoricalCoverage.meshStep d.m ≤ delta := by
    change 4 * (e : ℝ) + P4ACatalogFiveHistoricalCoverage.meshStep d.m ≤ delta
    linarith only [hwidth, hedelta, heR]
  have hc : (3 / 2 : ℝ) * d.chi + 2 * (d.e : ℝ) ≤ delta := by
    change (3 / 2 : ℝ) * ((e : ℝ) / 20) + 2 * (e : ℝ) ≤ delta
    linarith only [hedelta, heR]
  have ho : 2 * P4ACatalogFiveHistoricalCoverage.meshStep d.m ≤ delta := by
    linarith only [hwidth, hedelta, heR]
  have hchie : d.chi < (d.e : ℝ) / 10 := by
    change (e : ℝ) / 20 < (e : ℝ) / 10
    linarith only [heR]
  obtain ⟨m, buffer, hb, hbe, hpreserve, N0, hN0, hpaid⟩ :=
    hpayment e q ((e : ℝ) / 20) a rfl heR hesmall hchie hmesh hp hc ho
  refine ⟨m, buffer, hb, hbe, hpreserve, N0, hN0, ?_⟩
  intro N hN hEven
  have htotal := hpaid N hN hEven
  have habs := (catalog_five_source_error_le_cap_error d m buffer a N).trans_lt htotal
  have hlower := (abs_lt.mp habs).1
  exact ⟨htotal, by linarith only [hlower, original_physical_saving_ge_catalog_five]⟩

end
end ImbalancedChen.P4AOriginalCatalogFiveArchiveSchedule
