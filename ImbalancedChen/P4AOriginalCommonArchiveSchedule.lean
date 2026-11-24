import ImbalancedChen.P4AOriginalCausalHistory
import ImbalancedChen.P2OriginalFourteenWholeFamilyLower
import ImbalancedChen.P2OriginalSaving16CommonOldPolicy

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

One pre-N schedule is actually selected for the original archived fifth
bank and the whole original fourteen-cell selected charge.  The fifth
mesh is the original grid400-aligned m=475*q-1, with q fixed explicitly
above BOTH required third/history resolutions.  The archived fifth bank
is instantiated, rather than supplied as a preservation assumption.

This is a strict partial construction: the fourth records/licence remain
explicit primitive data. It does not instantiate their complete historical
bank, the finite strictly buffered second/third fallback box bank, or identify
the held eighth policy with all87. The held fallback formulas still use v.
Those missing branches cannot be supplied by the schedule theorem below.
-/

namespace ImbalancedChen.P4AOriginalCommonArchiveSchedule
noncomputable section
open scoped Classical BigOperators
open MeasureTheory VariableEnvelope
open P4AOriginalCausalHistory
open P5OriginalCommonRefinedConstructor
open P5OriginalCommonFourthFallbackExcision
open P5OriginalCommonFourthSourceNavigation
open P1Pair12RetainedSignedSource
open P2OriginalFourthCapProducerInterface
open P2OriginalAscendingEighthCapDictionary
open P2OriginalSaving16FourteenPhysicalAtlas
open P2OriginalSaving16TrimmedHistory
open P2OriginalFourteenWeightedTrim

/-- No N occurs in these finite fields. All third decisions read the
original first-three label; fourth and fifth rows stay at their own ranks. -/
def fixedSchedule (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (e : ℚ) (q : ℕ) (omega : ℝ) : ArchiveSchedule :=
  ⟨rows4, licensed4, e, q, (e : ℝ) / 20, omega⟩

/-- This record is a conclusion, never a common-history premise. -/
def FourteenHistory (s : ArchiveSchedule) (delta : ℝ) : Prop :=
  ∀ N : ℝ, 1 < N → ∀ pre : List ℕ, pre.length = 8 → (∀ p ∈ pre, 0 < p) →
    primeHistoryLogCoordinates N 8 pre ∈ trimmedRegion delta →
      HistoricalThirdCoarse.firstStop (s.data.e : ℝ) s.data.m N (rosserAncestor 1 pre) ∧
      P1ThirdFallbackSupport.supported (s.data.e : ℝ) s.data.chi s.data.m s.data.omega N
        (rosserAncestor 3 pre) ∧
      3 * primeHistoryLogCoordinates N 8 pre 0 < lambda3 s.data N (rosserAncestor 4 pre) ∧
      oddCube (primeHistoryLogCoordinates N 8 pre) 2 < lambda3 s.data N (rosserAncestor 4 pre) ∧
      oddCube (primeHistoryLogCoordinates N 8 pre) 4 < lambda3 s.data N (rosserAncestor 4 pre) ∧
      oddCube (primeHistoryLogCoordinates N 8 pre) 6 < lambda3 s.data N (rosserAncestor 4 pre) ∧
      lambda3 s.data N (rosserAncestor 4 pre) ≤ lambda6 s.data N (rosserAncestor 6 pre) ∧
      CurrentParentGuard (primeHistoryLogCoordinates N 8 pre)
        (lambda6 s.data N (rosserAncestor 6 pre)) ∧
      P5OriginalCommonRefinedFifthGainDefect.commonGain s.data N (rosserAncestor 5 pre) =
        P5OriginalCommonRefinedFifthGainDefect.oldGain s.data N (rosserAncestor 5 pre)

theorem refinedMesh_above_resolution (m : ℕ) :
    m ≤ P1OriginalFifthGrid400RefinedFullBoxCover.refinedMesh (m + 1) := by
  unfold P1OriginalFifthGrid400RefinedFullBoxCover.refinedMesh
  omega

/-- Epsilon first, one trim and common e0, then e/chi and omega, then ONE
grid400-aligned q and N0. No descendant or N chooses an ancestor's label.
The whole selected-family payment is consumed from O's implemented source.
There is no assertion that this fourteen-cell charge exhausts policy8. -/
theorem exists_fixed_archive_and_whole_fourteen_schedule
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
          (∫ t in region, sourceDensity t) - epsilon <
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
  obtain ⟨n, es, hes, hsource⟩ :=
    P2OriginalFourteenWholeFamilyLower.exists_actual_whole_family_lower_at_original_cutoff
      epsilon hepsilon
  obtain ⟨eh, heh, hhistory⟩ :=
    P2OriginalSaving16CommonOldPolicy.exists_common_actual_parent_on_trim (width n) (width_pos n)
  let e0 := min es (min eh (11 / 64000 : ℝ))
  have he0 : 0 < e0 := lt_min hes (lt_min heh (by norm_num))
  refine ⟨n, e0, he0, (min_le_right _ _).trans (min_le_right _ _), ?_⟩
  intro e he hee omega homega
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have hchie : (e : ℝ) / 20 ≤ (e : ℝ) / 10 := by linarith
  have hees : (e : ℝ) < es := hee.trans_le (min_le_left _ _)
  have heeh : (e : ℝ) < eh :=
    hee.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  obtain ⟨ms, N0, hN0, hwhole⟩ :=
    hsource e he hees ((e : ℝ) / 20) (by positivity) hchie
  obtain ⟨mh, hparent⟩ :=
    hhistory e he heeh ((e : ℝ) / 20) (by positivity) hchie
  let q : ℕ := max ms mh + 1
  let s := fixedSchedule rows4 licensed4 e q omega
  have hres := refinedMesh_above_resolution (max ms mh)
  have hms : ms ≤ s.data.m := (le_max_left ms mh).trans hres
  have hmh : mh ≤ s.data.m := (le_max_right ms mh).trans hres
  have hg : FourthGeometry s.data := hgeometry
  refine ⟨q, N0, by dsimp [q]; omega, hN0, ?_⟩
  change FourteenHistory s (width n) ∧ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hparent s.data rfl rfl hmh homega
  · exact hwhole s.data rfl rfl hms homega
  · intro N hN h T carrier
    exact fourth_signed_gain_preserved s.data hg N hN h T carrier
  · intro N hN h T carrier
    exact archive_fifth_signed_gain_preserved s hg N hN h T carrier

end
end ImbalancedChen.P4AOriginalCommonArchiveSchedule
