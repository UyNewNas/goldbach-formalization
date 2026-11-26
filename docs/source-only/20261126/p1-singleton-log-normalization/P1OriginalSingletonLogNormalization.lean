import ImbalancedChen.P1OriginalSingletonTwoLongDictionary
import ImbalancedChen.P1OriginalSingletonPhysicalLevel

/-!
SOURCE ONLY / NOT ELABORATED / NO LEAN OR KERNEL ACCEPTANCE.

The existing all-integer normalization and singleton-profile identity are
composed at the original complete group integer. The denominator is log n,
never the logarithm of each HB factor. The actual tuple and both copies of
the same Q/rho kernel remain unchanged. Unit HB factors are retained.

The second statement concerns one genuine ordered tuple. It does not infer
activity of an aggregate block coefficient or of every point of its rectangle.
No remaining/two-long selector, complementary block, Fourier representation,
roughness error or final discrepancy estimate is supplied by this bridge.
-/

namespace ImbalancedChen.P1OriginalSingletonLogNormalization
noncomputable section
open Classical Filter
open scoped BigOperators
open P5Z.HBRightClosedDyadicRoles (Block)
open P5Z.LiteralHeathBrownOccurrenceWords (factorTuples)
open P5Z.ActualRoughHeathBrownWords (roles)
open P5Z.ActualHBDyadicOccurrenceFamily (assignedWeight)
open P5Z.ExactOriginalSmoothDyadicPartition (beforeHBCutoff tupleProfile)
open P5Z.PerGroupIntegerHBAtlasPushforward (hbCutoff)
open P5Z.LicensedOriginalIntegerProfile (listExtension)
open P5Z.IndependentPrimeSourceWordDictionary (wordKernel)
open P5Z.OriginalPrimeAllGroupHBDiscrepancy (originalChart)
open P5Z.ActualLabelledPrimeSmoothCharts (chartTerm trimmedWeight)
open P5CanonicalTentNarrowSingletonTransfer (actualLicence)
open P5Z.AllGroupHBLogNormalization (normalized_listExtension)
open P5ActualUpperPairHBLogTransport (wordLog)
open P5Z.OrderedFactorTupleRectangleReindex (blockVector)
open Part3.OriginalProperPowerActualChart (wordVector)
open P5Z.ActualLowerNormalizedAtlasOccurrence
  (scalarProfile integerProfile rowRoles normalized_singleton_profile)
open P5Z.ActualLowerNormalizedBlockGeometry (rectangle)
open P5Z.ActualHBPostModulusLogCutoff (hbSlots completeProduct)
open P1OriginalSingletonRemainingTypeIGeometry
  (eventually_original_singleton_numeric_reserves)
open P1OriginalSingletonTwoLongDictionary (actual_tuple_to_rectangle)
open P1OriginalSingletonPhysicalLevel (scalarProfile_complete_support)

/-- Pointwise composition of the existing exact normalization suppliers.
This includes all natural n, with totalized division at n = 0 and n = 1.
The original complete-product eta and chart psi are both retained. -/
theorem scalarProfile_eq_originalChart_div_log
    (kap : ℝ) (B N cj : ℕ) (kap0 : ℝ) (n : ℕ) :
    (scalarProfile kap B N cj kap0 n : ℂ) =
      originalChart (actualLicence kap B N) N kap0 [cj] [n] /
        (Real.log (n : ℝ) : ℂ) := by
  rw [← normalized_singleton_profile, normalized_listExtension]
  simp only [wordLog, originalChart, chartTerm, tupleProfile, trimmedWeight,
    List.prod_cons, List.prod_nil, mul_one, Complex.ofReal_div, div_eq_mul_inv]
  ring

/-- The original nonzero chart supplies the complete log denominator on
one genuine assigned tuple. The existing pointwise support is then available
at precisely that tuple, with no new carrier or aggregate nonzero premise.

The physical-N threshold precedes kap, B, K, chart/order, tuple, Q and rho.
The final equality keeps the entire same-Q/rho count-minus-coprime-mean kernel.
It does not assert that the kernel, or every point of the rectangle, is nonzero. -/
theorem eventually_actual_tuple_normalized_profile
    {kap0 zeta : ℝ} (hkap0 : kap0 < 1)
    (hzeta : 0 < zeta) (hsmall : zeta ≤ 1 / 20000) :
    ∀ᶠ N : ℕ in atTop, ∀ (kap : ℝ), kap < 1 →
      ∀ (B K cj j n : ℕ) (bs : List Block) (fs : List ℕ)
        (Q : Finset ℕ) (rho : ℕ → ℂ),
      originalChart (actualLicence kap B N) N kap0 [cj] [n] ≠ 0 →
      fs ∈ factorTuples (2*(j+1)) n →
      assignedWeight (beforeHBCutoff K [cj]) (hbCutoff cj) (roles j) bs fs ≠ 0 →
      let r := 2*(j+1)
      let bv := blockVector r bs
      let ns := wordVector r fs
      ns ∈ rectangle bv ∧
      completeProduct ns = n ∧
      0 < Real.log (completeProduct ns : ℝ) ∧
      integerProfile kap B N cj kap0 ns ≠ 0 ∧
      (N : ℝ)^(1-kap0) < (completeProduct ns : ℝ) ∧
      (completeProduct ns : ℝ) ≤ 2*(N : ℝ) ∧
      hbSlots (beforeHBCutoff K [cj]) (fun _ => hbCutoff cj) (rowRoles j) ns *
          (integerProfile kap B N cj kap0 ns : ℂ) *
          wordKernel Q rho N [completeProduct ns] =
        assignedWeight (beforeHBCutoff K [cj]) (hbCutoff cj) (roles j) bs fs *
          (originalChart (actualLicence kap B N) N kap0 [cj] [n] /
            (Real.log (n : ℝ) : ℂ)) * wordKernel Q rho N [n] := by
  filter_upwards [eventually_original_singleton_numeric_reserves hkap0 hzeta hsmall,
    eventually_ge_atTop (1 : ℕ)] with N hnumeric hN
  intro kap hkap B K cj j n bs fs Q rho hactive hfs hassigned
  obtain ⟨hlo, _, hlarge, _, _⟩ := hnumeric kap B cj n hactive
  have hpower : (1 : ℝ) ≤
      (P5Z.OriginalPrimeAtlasReserveBranches.originalMediumLow zeta [cj])^6 := by
    simpa only [one_pow] using
      pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hlo 6
  have hn : (1 : ℝ) < n := by nlinarith only [hlarge, hpower]
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hn
  have hscalarC : (scalarProfile kap B N cj kap0 n : ℂ) ≠ 0 := by
    rw [scalarProfile_eq_originalChart_div_log]
    exact div_ne_zero hactive (by exact_mod_cast hlog.ne')
  have hscalar : scalarProfile kap B N cj kap0 n ≠ 0 := by
    intro hz
    apply hscalarC
    rw [hz, Complex.ofReal_zero]
  obtain ⟨htrim, hcap⟩ := scalarProfile_complete_support kap hkap B N cj kap0
    (by omega) hscalar
  obtain ⟨_, _, _, hrect, hproduct, hweight⟩ :=
    actual_tuple_to_rectangle (beforeHBCutoff K [cj]) (hbCutoff cj)
      j n bs fs hfs hassigned
  refine ⟨hrect, hproduct, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hproduct] using hlog
  · simpa only [integerProfile, hproduct] using hscalar
  · simpa only [hproduct] using htrim
  · simpa only [hproduct] using hcap
  · simp only [integerProfile, hproduct, hweight, scalarProfile_eq_originalChart_div_log]

end
end ImbalancedChen.P1OriginalSingletonLogNormalization
