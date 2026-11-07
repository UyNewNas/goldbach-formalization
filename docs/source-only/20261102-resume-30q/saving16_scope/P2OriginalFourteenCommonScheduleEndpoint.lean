import ImbalancedChen.P4AOriginalCommonArchiveSchedule
import ImbalancedChen.P2OriginalSaving16OwnedIntegral

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The original Q96 lower endpoint now applies to the literal ordinary
fourteen-cell signed charge on O's SAME pre-N archive/history schedule.
The source integral, common ancestors, fourth/fifth signed preservation,
weak-complement payment and 39741-simplex ownership are imported proofs,
not caller premises and not reproved here. No complete-cell, facet or
active-eight coverage is needed for this positive lower bound.

The primitive fourth rows/licence and their Geometry premise stay explicit.
This does not instantiate the complete fourth bank, identify the held
policy8 with all87, or pay the positive-presieve/compiler/reserve terms.
Every inherited finite body is UNEVALUATED. The endpoint import must use
P's same-module canonical-moment replacement; the full chain remains HOLD.
-/

namespace ImbalancedChen.P2OriginalFourteenCommonScheduleEndpoint

noncomputable section
open scoped Classical BigOperators
open MeasureTheory VariableEnvelope
open P4AOriginalCausalHistory
open P4AOriginalCommonArchiveSchedule
open P5OriginalCommonRefinedConstructor
open P5OriginalCommonFourthFallbackExcision
open P5OriginalCommonFourthSourceNavigation
open P1Pair12RetainedSignedSource
open P2OriginalFourthCapProducerInterface
open P2OriginalAscendingEighthCapDictionary
open P2OriginalSaving16FourteenPhysicalAtlas
open P2OriginalSaving16TrimmedHistory
open P2OriginalFourteenWeightedTrim

/-- One original grid400-aligned schedule realizes the retained histories,
preserves the original fourth/fifth signed gains, and gives the ORIGINAL
Q96 endpoint for the whole ordinary selected-family charge. The precision
and q precede N, cap, cutoff and every descendant history. The only new
deduction is the concrete source-endpoint comparison on this same schedule.
-/
theorem exists_fixed_archive_and_whole_fourteen_q96_schedule
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (hgeometry : ∀ r ∈ rows4, licensed4 r → r.Geometry)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ n : ℕ, ∃ e0 : ℝ, 0 < e0 ∧ e0 ≤ 11 / 64000 ∧
      ∀ e : ℚ, 0 < e → (e : ℝ) < e0 → ∀ omega : ℝ, omega ≤ 1 / 100 →
      ∃ q N0 : ℕ, 0 < q ∧ 2 ≤ N0 ∧
        let s := fixedSchedule rows4 licensed4 e q omega
        FourteenHistory s (width n) ∧
        (∀ N cap : ℕ, N0 ≤ N → Even N → ∀ z : ℝ,
          (N : ℝ) ^ mu ≤ z → z ≤ (cap : ℝ) →
          |(∫ t in region, sourceDensity t) -
            (∫ t in trimmedRegion (width n), sourceDensity t)| < epsilon / 4 ∧
          (1222997719565324892497827 : ℝ) / (2 : ℝ) ^ 96 - epsilon <
            P2OriginalFourteenSignedParentLedger.charge N cap 0 z
              (lambda6 s.data (N : ℝ)) P4AOriginalAscending14Literal42.literalPattern
              (policy5 s.data (N : ℝ)) * Real.log (N : ℝ) / singularSeries N) ∧
        (∀ N : ℝ, 1 ≤ N → ∀ h : ℕ → ℝ, ∀ T : Bool → List ℕ → ℝ,
          ∀ carrier : List ℕ,
          signedTest (common3 s.data N) h T [] true 1 carrier -
              signedTest (policy4 s.data N) h T [] true 1 carrier =
            signedTest (old3 s.data N) h T [] true 1 carrier -
              signedTest (original4 s.data N) h T [] true 1 carrier) ∧
        (∀ N : ℝ, 1 ≤ N → ∀ h : ℕ → ℝ, ∀ T : Bool → List ℕ → ℝ,
          ∀ carrier : List ℕ,
          signedTest (policy4 s.data N) h T [] true 1 carrier -
              signedTest (policy5 s.data N) h T [] true 1 carrier =
            signedTest (original4 s.data N) h T [] true 1 carrier -
              signedTest (original5 s.data N) h T [] true 1 carrier) := by
  obtain ⟨n, e0, he0, he0bound, hschedule⟩ :=
    exists_fixed_archive_and_whole_fourteen_schedule
      rows4 licensed4 hgeometry epsilon hepsilon
  refine ⟨n, e0, he0, he0bound, ?_⟩
  intro e he hee omega homega
  obtain ⟨q, N0, hq, hN0, hs⟩ := hschedule e he hee omega homega
  refine ⟨q, N0, hq, hN0, ?_⟩
  dsimp only at hs ⊢
  obtain ⟨hhistory, hwhole, hfourth, hfifth⟩ := hs
  refine ⟨hhistory, ?_, hfourth, hfifth⟩
  intro N cap hN hEven z hz hcap
  obtain ⟨htrim, hlower⟩ := hwhole N cap hN hEven z hz hcap
  refine ⟨htrim, ?_⟩
  exact (sub_le_sub_right
    P2OriginalSaving16OwnedIntegral.historical_endpoint_le_source_integral epsilon).trans_lt
      hlower

end
end ImbalancedChen.P2OriginalFourteenCommonScheduleEndpoint
