import ImbalancedChen.P1OriginalSingletonSmoothLicence
import ImbalancedChen.P5OriginalPrimeAtlasReserveBranches
import ImbalancedChen.P5OriginalHBMediumChartReserves

/-!
SOURCE ONLY / NOT ELABORATED / NO LEAN OR KERNEL ACCEPTANCE.

The original singleton chart, including its extra complete-product eta,
supplies the eventual numerical reserves for the existing no-medium
alternative. The original physical target is N throughout. No desired
short/long inequality or discrepancy estimate is assumed.

The threshold precedes the profile parameter, collar order, rough-cutoff
order, chart, HB order, source integer and ordered block word. The final
row interface uses the literal unfolded body of the historical
remainingTypeIValue; it does not introduce another remaining carrier.

Frozen 1106 coefficient appendix, original HB / Type I selection,
lines 526--548 and 621--630. Source/statement review is recorded in
docs/p1/20261125/p15-singleton-remaining-typei-geometry/SOURCE_REVIEW.json.
-/

namespace ImbalancedChen.P1OriginalSingletonRemainingTypeIGeometry

noncomputable section

open Classical Filter
open scoped Topology BigOperators
open P5Z.HBRightClosedDyadicRoles (Block)
open P5Z.ActualHBDyadicProductWindow (lower)
open P5Z.ActualRoughHeathBrownWords (roles)
open P5Z.ActualHBDyadicOccurrenceFamily (blockCoefficient)
open P5Z.ExactOriginalSmoothDyadicPartition (R R_pos scales beforeHBCutoff)
open P5Z.ActualLabelledPrimeSmoothCharts
  (chartTerm trimmedWeight profile_nonzero_support)
open P5Z.PerGroupIntegerHBAtlasPushforward (Row hbCutoff typeIValue)
open P5Z.ActualHBMediumBranchPartition
  (firstMedium longBlocks originalLower originalUpper)
open P5Z.ActualHBMediumRoleSupports (original_noMedium_actual_alternative)
open P5Z.OriginalHBMediumChartReserves (original_chart_numeric_reserves)
open P5Z.OriginalPrimeAllGroupHBDiscrepancy
  (originalChart actual_chi_one actual_chi_zero original_cutoff_nonneg)
open P5Z.OriginalPrimeAtlasReserveBranches (originalMediumLow originalMediumHigh)
open P5Z.ActualEtaPsiOccurrenceBudget (eta eta_zero)
open P5CanonicalTentNarrowSingletonTransfer (actualLicence)

private theorem actual_chart_integer_support
    (kap kap0 : ℝ) (B N cj n : ℕ) (hN : 0 < N)
    (hactive : originalChart (actualLicence kap B N) N kap0 [cj] [n] ≠ 0) :
    (N : ℝ) ^ (1 - kap0) < (n : ℝ) ∧
      R cj / 2 ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * R cj := by
  have htuple := (mul_ne_zero_iff.mp
    (show P5Z.ExactOriginalSmoothDyadicPartition.tupleProfile
        P5Z.ActualEtaPsiOccurrenceBudget.chi [cj] [n] *
        trimmedWeight eta
          (fun u => (P5Z.LicensedOriginalIntegerProfile.listExtension
            (actualLicence kap B N) u : ℂ)) (N : ℝ) kap0 [n] ≠ 0 from hactive)).1
  have hwindow := profile_nonzero_support P5Z.ActualEtaPsiOccurrenceBudget.chi
    (fun t ht => actual_chi_one ht) (fun t ht => actual_chi_zero ht) [cj] [n] htuple
  have hbounds : R cj / 2 ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * R cj := by
    cases hwindow with
    | cons hhead _ => exact hhead.2
  have heta : eta ((n : ℝ) / (N : ℝ) ^ (1 - kap0)) ≠ 0 := by
    intro hz
    apply hactive
    simp only [originalChart, chartTerm, trimmedWeight, List.prod_cons,
      List.prod_nil, mul_one, hz, Complex.ofReal_zero, zero_mul, mul_zero]
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hden := Real.rpow_pos_of_pos hNp (1 - kap0)
  refine ⟨?_, hbounds⟩
  by_contra hnot
  exact heta (eta_zero ((div_le_one hden).mpr (le_of_not_gt hnot)))

/-- All five old numerical gates follow from an actual nonzero singleton
chart. One eventual physical-N threshold precedes every actual index. -/
theorem eventually_original_singleton_numeric_reserves
    {kap0 zeta : ℝ} (hkap0 : kap0 < 1)
    (hzeta : 0 < zeta) (hsmall : zeta ≤ 1 / 20000) :
    ∀ᶠ N : ℕ in atTop, ∀ (kap : ℝ) (B cj n : ℕ),
      originalChart (actualLicence kap B N) N kap0 [cj] [n] ≠ 0 →
      1 ≤ originalMediumLow zeta [cj] ∧
      1 ≤ originalMediumHigh zeta [cj] ∧
      64 * (originalMediumLow zeta [cj]) ^ 6 < (n : ℝ) ∧
      (n : ℝ) < (originalMediumHigh zeta [cj]) ^ 3 ∧
      hbCutoff cj ≤ originalMediumHigh zeta [cj] := by
  have hshortExp : 0 < 1 - 18 * zeta := by linarith
  have hlongExp : 0 < 3 * zeta / 4 := by positivity
  have hlarge : ∀ᶠ X : ℝ in atTop,
      1 ≤ X ∧ 8192 < X ^ (1 - 18 * zeta) ∧ 4 < X ^ (3 * zeta / 4) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ),
      (_root_.tendsto_rpow_atTop hshortExp).eventually (eventually_gt_atTop (8192 : ℝ)),
      (_root_.tendsto_rpow_atTop hlongExp).eventually (eventually_gt_atTop (4 : ℝ))]
      with X hX hshort hlong
    exact ⟨hX, hshort, hlong⟩
  obtain ⟨X0, hX0⟩ := eventually_atTop.mp hlarge
  have hgrowth : Tendsto (fun N : ℕ => (N : ℝ) ^ (1 - kap0)) atTop atTop :=
    (_root_.tendsto_rpow_atTop (by linarith : 0 < 1 - kap0)).comp
      tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    hgrowth.eventually (eventually_ge_atTop (2 * X0))] with N hN hsize
  intro kap B cj n hactive
  obtain ⟨htrim, hlo, hhi⟩ := actual_chart_integer_support kap kap0 B N cj n
    (by omega) hactive
  have hRX0 : X0 ≤ R cj := by linarith
  obtain ⟨hRone, hshort, hlong⟩ := hX0 (R cj) hRX0
  have hRp : 0 < R cj := R_pos cj
  have hy : 0 ≤ hbCutoff cj :=
    Real.rpow_nonneg (by linarith : 0 ≤ 2 * R cj) _
  have hcube : (hbCutoff cj) ^ 3 = 2 * R cj := by
    unfold hbCutoff
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0 ≤ 2 * R cj)]
    norm_num
  have hnumeric := original_chart_numeric_reserves
    (X := R cj) (zeta := zeta) (a := 1) (C := 2) (R := R cj)
    (y := hbCutoff cj) (n := n) hRone hzeta.le (by norm_num)
    (by simp) (by linarith) (by linarith) hhi hy hcube hshort
    (by simpa only [show (2 : ℝ) * 2 = 4 from by norm_num] using hlong)
  simpa only [originalMediumLow, originalMediumHigh, originalLower, originalUpper,
    scales, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    using hnumeric

/-- The two branch tests are exactly those retained by remainingTypeIValue:
no first medium position, and the long-occurrence count is not one.
Every nonzero original HB block satisfying them has exactly two long
occurrences, each carrying the original one or logarithm role. -/
theorem eventually_original_singleton_remaining_typeI_two_long
    {kap0 zeta : ℝ} (hkap0 : kap0 < 1)
    (hzeta : 0 < zeta) (hsmall : zeta ≤ 1 / 20000) :
    ∀ᶠ N : ℕ in atTop, ∀ (kap : ℝ) (B K cj j n : ℕ) (bs : List Block),
      originalChart (actualLicence kap B N) N kap0 [cj] [n] ≠ 0 →
      j ∈ Finset.range 3 →
      blockCoefficient (beforeHBCutoff K [cj]) (hbCutoff cj) j n bs ≠ 0 →
      firstMedium (originalMediumLow zeta [cj]) (originalMediumHigh zeta [cj]) bs = none →
      (longBlocks (originalMediumHigh zeta [cj]) bs).length ≠ 1 →
      (longBlocks (originalMediumHigh zeta [cj]) bs).length = 2 ∧
        (∀ rb ∈ (roles j).zip bs,
          originalMediumHigh zeta [cj] < (lower rb.2 : ℝ) →
          rb.1 = .one ∨ rb.1 = .logarithm) := by
  filter_upwards [eventually_original_singleton_numeric_reserves hkap0 hzeta hsmall]
    with N hN
  intro kap B K cj j n bs hactive hj hcoeff hbranch hremaining
  have hnumeric := hN kap B cj n hactive
  have hbounds : 1 ≤ originalLower (R cj) zeta ∧
      1 ≤ originalUpper (R cj) zeta ∧
      64 * (originalLower (R cj) zeta) ^ 6 < (n : ℝ) ∧
      (n : ℝ) < (originalUpper (R cj) zeta) ^ 3 ∧
      hbCutoff cj ≤ originalUpper (R cj) zeta := by
    simpa only [originalMediumLow, originalMediumHigh, originalLower, originalUpper,
      scales, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      using hnumeric
  have hbranch' : firstMedium (originalLower (R cj) zeta)
      (originalUpper (R cj) zeta) bs = none := by
    simpa only [originalMediumLow, originalMediumHigh, originalLower, originalUpper,
      scales, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      using hbranch
  have hremaining' : (longBlocks (originalUpper (R cj) zeta) bs).length ≠ 1 := by
    simpa only [originalMediumHigh, originalUpper, scales, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, mul_one] using hremaining
  obtain ⟨hcount, hroles⟩ := original_noMedium_actual_alternative
    (original_cutoff_nonneg K [cj]) hbounds.1 hbounds.2.1 hbounds.2.2.2.2
    hj hcoeff hbranch' hbounds.2.2.1 hbounds.2.2.2.1
  have htwo := hcount.resolve_left hremaining'
  constructor
  · simpa only [originalMediumHigh, originalUpper, scales, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, mul_one] using htwo
  · simpa only [originalMediumHigh, originalUpper, scales, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, mul_one] using hroles

/-- This expression is the exact unfolded body of historical
remainingTypeIValue on one literal Row. The arbitrary F is only the
unchanged row test; this is a finite predicate identity, not an estimate. -/
theorem singleton_remaining_predicate_iff
    (lo hi : ℝ) (F : List Row → ℂ) (row : Row) :
    ((if (longBlocks hi ([row].flatMap Row.blocks)).length = 1 then (0 : ℂ)
      else typeIValue lo hi F [row]) ≠ 0) ↔
      (longBlocks hi row.blocks).length ≠ 1 ∧
        firstMedium lo hi row.blocks = none ∧ F [row] ≠ 0 := by
  by_cases hlong : (longBlocks hi row.blocks).length = 1 <;>
    by_cases hbranch : firstMedium lo hi row.blocks = none <;>
    simp [typeIValue, hlong, hbranch]

/-- The historical remaining selector, with its original row and exact
complete integer, feeds the actual geometry without numerical premises.
The row test may be instantiated with the original signed sourceTest. -/
theorem eventually_original_singleton_remaining_row_two_long
    {kap0 zeta : ℝ} (hkap0 : kap0 < 1)
    (hzeta : 0 < zeta) (hsmall : zeta ≤ 1 / 20000) :
    ∀ᶠ N : ℕ in atTop, ∀ (kap : ℝ) (B K cj : ℕ) (row : Row) (F : List Row → ℂ),
      originalChart (actualLicence kap B N) N kap0 [cj] [row.factors.prod] ≠ 0 →
      row.order ∈ Finset.range 3 →
      blockCoefficient (beforeHBCutoff K [cj]) (hbCutoff cj)
        row.order row.factors.prod row.blocks ≠ 0 →
      (if (longBlocks (originalMediumHigh zeta [cj])
          ([row].flatMap Row.blocks)).length = 1 then (0 : ℂ)
        else typeIValue (originalMediumLow zeta [cj]) (originalMediumHigh zeta [cj])
          F [row]) ≠ 0 →
      (longBlocks (originalMediumHigh zeta [cj]) row.blocks).length = 2 ∧
        (∀ rb ∈ (roles row.order).zip row.blocks,
          originalMediumHigh zeta [cj] < (lower rb.2 : ℝ) →
          rb.1 = .one ∨ rb.1 = .logarithm) := by
  filter_upwards [eventually_original_singleton_remaining_typeI_two_long
    hkap0 hzeta hsmall] with N hN
  intro kap B K cj row F hactive hj hcoeff hremaining
  obtain ⟨hnotOne, hbranch, _⟩ :=
    (singleton_remaining_predicate_iff (originalMediumLow zeta [cj])
      (originalMediumHigh zeta [cj]) F row).mp hremaining
  exact hN kap B K cj row.order row.factors.prod row.blocks
    hactive hj hcoeff hbranch hnotOne

end
end ImbalancedChen.P1OriginalSingletonRemainingTypeIGeometry
