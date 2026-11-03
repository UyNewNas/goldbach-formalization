import ImbalancedChen.P1GuardFrozenFiniteCapAlgebra
import ImbalancedChen.P4AOriginalFull87ActualCommonHistory

/-!
SOURCE ONLY / UNCOMPILED / NO KERNEL CREDIT.

Finite scalar companions of the actual fourth, fifth and COMPLETE sixth
producers. The actual original seed has a finite rational alphabet because
its historical Gamma table is finite. No held-eleven substitution is made.

The original eligibility decisions are evaluated at their original current
values; the finite scalar image does NOT re-run those guards on a rounded
parent. This is a causal finite-VALUE construction, not yet a finite
whole-box action table or an archived-gain preservation theorem.
-/
namespace ImbalancedChen.P4AOriginalFull87FiniteParentCaps
noncomputable section
open scoped Classical BigOperators
open VariableEnvelope P1OriginalVariableFourthContinuation
open P5OriginalCommonRefinedConstructor P5OriginalCommonRefinedPreservation
open P4AOriginalCompleteSixthChronology
open P4AOriginalFull87SourceDictionary
open P4AOriginalFull87ActualCommonHistory
open P4AOriginalFull87HistoryCore (width oldHistory)
open P1GuardFrozenFiniteCapAlgebra

/-- The fallback and all original buffered Gamma entries, before N. -/
def thirdAlphabet (e : ℚ) (chi : ℝ) (m : ℕ) : Finset ℚ :=
  insert ((299 / 500 : ℚ) - 2 * e)
    ((HistoricalThirdCoarse.cells (e : ℝ) chi m).image fun j =>
      HistoricalThirdCoarse.gamma (e : ℝ) (HistoricalThirdCoarse.box m j) - 2 * e)

theorem originalSeed_mem (d : OriginalData) (N : ℝ) (pre : List ℕ) :
    originalSeed d N pre ∈ (thirdAlphabet d.e d.chi d.m).image (fun a => (a : ℝ)) := by
  unfold originalSeed P1OriginalVariableFourthContinuation.seedExponent
  by_cases hs : P1ThirdFallbackSupport.supported (d.e : ℝ) d.chi d.m d.omega N
      (rosserAncestor 3 pre)
  · rw [P1CoarseFirstCubeFallbackMargin.effectiveExponent, if_pos hs]
    obtain ⟨j, hj, ht⟩ := hs.2
    rw [HistoricalThirdCoarse.exponent_on_cell _ _ _ _ j hj ht]
    refine Finset.mem_image.mpr ⟨
      HistoricalThirdCoarse.gamma (d.e : ℝ) (HistoricalThirdCoarse.box d.m j) - 2 * d.e,
      Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j, hj, rfl⟩), ?_⟩
    simp [HistoricalThirdCoarse.levelExponent]
  · rw [P1CoarseFirstCubeFallbackMargin.effectiveExponent, if_neg hs]
    refine Finset.mem_image.mpr ⟨(299 / 500 : ℚ) - 2 * d.e,
      Finset.mem_insert_self _ _, ?_⟩
    simp [HistoricalThirdCoarse.initial, extendedDistributionCap]

theorem originalSeed_ancestor (d : OriginalData) (N : ℝ)
    (k : ℕ) (hk : 3 ≤ k) (pre : List ℕ) :
    originalSeed d N (rosserAncestor k pre) = originalSeed d N pre := by
  simp only [originalSeed, P1OriginalVariableFourthContinuation.seedExponent,
    rosserAncestor_nested 3 k hk]

/-- Explicit recursive finite scalar companions; the inherited finite
fourth and fifth values are present, not discarded during construction. -/
def cap4 (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ) (pre : List ℕ) : ℝ :=
  protect n (originalSeed (data e q om) N pre) (exponent4 (data e q om) N pre)

def cap5 (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ) (pre : List ℕ) : ℝ :=
  max (cap4 n e q om N (rosserAncestor 4 pre))
    (rounded n (exponent5 (data e q om) N pre) : ℝ)

def cap6 (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ) (pre : List ℕ) : ℝ :=
  max (cap5 n e q om N (rosserAncestor 5 pre))
    (rounded n (currentSixthExponent e q om N pre) : ℝ)

theorem cap5_eq_protect (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ) (pre : List ℕ) :
    cap5 n e q om N pre =
      protect n (originalSeed (data e q om) N pre) (exponent5 (data e q om) N pre) := by
  unfold cap5 cap4
  rw [originalSeed_ancestor _ _ 4 (by decide)]
  exact protect_nested n _ _ _ (inherited4_le_exponent5 (data e q om) N pre)

theorem cap6_eq_protect (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ) (pre : List ℕ) :
    cap6 n e q om N pre =
      protect n (originalSeed (data e q om) N pre) (currentSixthExponent e q om N pre) := by
  unfold cap6
  rw [cap5_eq_protect, originalSeed_ancestor _ _ 5 (by decide)]
  exact protect_nested n _ _ _ (fifth_le_current e q om N pre)

theorem cap4_le_cap5 (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ) (pre : List ℕ) :
    cap4 n e q om N (rosserAncestor 4 pre) ≤ cap5 n e q om N pre := le_max_left _ _

theorem cap5_le_cap6 (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ) (pre : List ℕ) :
    cap5 n e q om N (rosserAncestor 5 pre) ≤ cap6 n e q om N pre := le_max_left _ _

/-- One literal rational alphabet for all three levels. It contains no N,
omega, source owner, prime tuple, or caller-provided endpoint family. -/
def alphabet (n : ℕ) (e : ℚ) (q : ℕ) : Finset ℚ :=
  thirdAlphabet e ((e : ℝ) / 20)
    (P1OriginalFifthGrid400RefinedFullBoxCover.refinedMesh q) ∪ roundedAlphabet n

theorem caps_mem_alphabet (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ) (pre : List ℕ) :
    cap4 n e q om N pre ∈ (alphabet n e q).image (fun a => (a : ℝ)) ∧
    cap5 n e q om N pre ∈ (alphabet n e q).image (fun a => (a : ℝ)) ∧
    cap6 n e q om N pre ∈ (alphabet n e q).image (fun a => (a : ℝ)) := by
  have hs := originalSeed_mem (data e q om) N pre
  have hf (x : ℝ) : protect n (originalSeed (data e q om) N pre) x ∈
      (alphabet n e q).image (fun a => (a : ℝ)) :=
    protect_mem_union n _ _ x hs
  exact ⟨hf _, by rw [cap5_eq_protect]; exact hf _,
    by rw [cap6_eq_protect]; exact hf _⟩

/-- The actual fourth row formulas and eligibility are untouched. -/
theorem fourth_same_guard_image (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ)
    (history : List ℕ) (hlen : history.length = 4) :
    cap4 n e q om N history =
      let d := data e q om
      finiteMax d.rows4
        (fun r => producerEligible d.licensed4 r (primeHistoryLogCoordinates N 4 history))
        (fun r => protect n (originalSeed d N history)
          (r.bufferedCandidate (d.e : ℝ) (primeHistoryLogCoordinates N 4 history)))
        (protect n (originalSeed d N history) (lambda3 d N history)) := by
  unfold cap4 exponent4
  rw [if_pos hlen]
  exact protect_finiteMax n _ _ _ _ _

/-- The SAME fifth eligibility and pointwise candidates feed the finite
maximum, whose seed is precisely the finite fourth ancestor. -/
theorem fifth_same_guard_image (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ)
    (history : List ℕ) (hlen : history.length = 5) :
    cap5 n e q om N history =
      let d := data e q om
      finiteMax d.rows5
        (fun r => P1OriginalVariableFifthContinuation.eligible d.e d.chi d.m d.omega
          d.J5 r (primeHistoryLogCoordinates N 5 history))
        (fun r => protect n (originalSeed d N history)
          (P1OriginalVariableFifthContinuation.candidate (d.e : ℝ) r.selected
            (primeHistoryLogCoordinates N 5 history)))
        (cap4 n e q om N (rosserAncestor 4 history)) := by
  rw [cap5_eq_protect]
  unfold exponent5
  rw [if_pos hlen, protect_finiteMax]
  dsimp only
  rw [cap4, originalSeed_ancestor _ _ 4 (by decide)]

/-- Same original saved-row decisions, not savedEligible with a new parent. -/
theorem saved_same_guard_image (n : ℕ) (base : ℝ) (e : ℚ) (q : ℕ)
    (om N : ℝ) (pre : List ℕ) :
    protect n base (savedExponent e q om N pre) =
      finiteMax Finset.univ (fun i => savedEligible e q om N i pre)
        (fun i => protect n base
          (P4AOriginalSavedSixthArchive.endpoint i (primeHistoryLogCoordinates N 6 pre)))
        (protect n base (fifth e q om N pre)) :=
  protect_finiteMax n base _ _ _ _

/-- All eleven original actions remain in the SAME finite maximum. -/
theorem eleven_same_guard_image (n : ℕ) (base : ℝ) (e : ℚ) (q : ℕ)
    (om N : ℝ) (history : List ℕ) :
    protect n base (elevenExponent e q om N history) =
      finiteMax Certificates.P2OriginalSixthElevenLogSemantics.allCells.toFinset
        (fun c => eligibleSixth (data e q om) N c history)
        (fun c => protect n base
          (Certificates.P2OriginalSixthElevenLogSemantics.newCap c
            (primeHistoryLogCoordinates N 6 history)))
        (protect n base (savedExponent e q om N history)) :=
  protect_finiteMax n base _ _ _ _

/-- The raw current stays in the eligibility predicate on BOTH sides.
Rounded-current eligibility could admit new rows and is NOT proved equal. -/
theorem later_same_guard_image (n : ℕ) (base : ℝ) (stage : ℕ)
    (N current : ℝ) (pre : List ℕ) :
    protect n base (applyLater stage N current pre) =
      finiteMax Finset.univ (fun c => laterEligible stage current N c pre)
        (fun c => protect n base
          (P4AOriginalSixthLaterSemantics.endpoint c (primeHistoryLogCoordinates N 6 pre)))
        (protect n base current) :=
  protect_finiteMax n base _ _ _ _

/-- The original chronology's successor equation with all raw-current
guards preserved explicitly. This is not a newly chosen action order. -/
theorem afterLater_same_guard_image (n : ℕ) (base : ℝ) (e : ℚ) (q : ℕ)
    (om N : ℝ) (history : List ℕ) (k : ℕ) :
    protect n base (afterLater e q om N history (k + 1)) =
      finiteMax Finset.univ
        (fun c => laterEligible k (afterLater e q om N history k) N c history)
        (fun c => protect n base
          (P4AOriginalSixthLaterSemantics.endpoint c (primeHistoryLogCoordinates N 6 history)))
        (protect n base (afterLater e q om N history k)) :=
  later_same_guard_image n base k N (afterLater e q om N history k) history

/-- A conclusion predicate: all caps use their OWN ancestors. -/
def ParentBounds (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ) (pre : List ℕ) (c : Cell) : Prop :=
  let d := data e q om
  let L := lambda3 d N (rosserAncestor 4 pre)
  let a4 := rosserAncestor 4 pre
  let a5 := rosserAncestor 5 pre
  let a6 := rosserAncestor 6 pre
  0 < L ∧ L ≤ cap4 n e q om N a4 ∧
  cap4 n e q om N a4 ≤ cap5 n e q om N a5 ∧
  cap5 n e q om N a5 ≤ cap6 n e q om N a6 ∧
  cap6 n e q om N a6 ≤ comparison c (primeHistoryLogCoordinates N 8 pre) ∧
  (exponent4 d N a4 - 2 * width n < cap4 n e q om N a4 ∧
    cap4 n e q om N a4 ≤ exponent4 d N a4) ∧
  (exponent5 d N a5 - 2 * width n < cap5 n e q om N a5 ∧
    cap5 n e q om N a5 ≤ exponent5 d N a5) ∧
  (currentSixthExponent e q om N a6 - 2 * width n < cap6 n e q om N a6 ∧
    cap6 n e q om N a6 ≤ currentSixthExponent e q om N a6)

/-- The cap error is <2/(n+1) at EACH level, not three times that error.
All raw upper and history inputs here come from the actual common-history
supplier; the public schedule below discharges that intermediate input. -/
theorem parent_bounds_of_history (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ)
    (pre : List ℕ) (hlen : pre.length = 8) (c : Cell)
    (hs : Source c (primeHistoryLogCoordinates N 8 pre))
    (hr : RealizedHistory e q om N pre c) : ParentBounds n e q om N pre c := by
  let d := data e q om
  let L := lambda3 d N (rosserAncestor 4 pre)
  have hseed : L = originalSeed d N pre :=
    P4AOriginalFull87CompleteSixthBound.actual_third_eq_original d N pre hlen c hs
  have hL0 : 0 < L := by
    have hh := hr.2.2.1 (0 : Fin 4)
    have ht := (source_basic hs).2.2.1
    have ho : StrictAnti (primeHistoryLogCoordinates N 8 pre) :=
      Fin.strictAnti_iff_succ_lt.mpr (source_basic hs).2.2.2
    have h07 := ho.antitone (show (0 : Fin 8) ≤ 7 by decide)
    dsimp [oldHistory, P4AOriginalRemainingEighthSources.history] at hh
    change 0 < lambda3 d N (rosserAncestor 4 pre)
    linarith
  have h34 := lambda3_le_exponent4 d N (rosserAncestor 4 pre)
  have h45 := inherited4_le_exponent5 d N (rosserAncestor 5 pre)
  rw [rosserAncestor_nested 4 5 (by decide)] at h45
  have h56 := fifth_le_current e q om N (rosserAncestor 6 pre)
  change exponent5 d N (rosserAncestor 5 (rosserAncestor 6 pre)) ≤ _ at h56
  rw [rosserAncestor_nested 5 6 (by decide)] at h56
  have h6cap : currentSixthExponent e q om N (rosserAncestor 6 pre) ≤ cap :=
    hr.2.2.2.2.trans ((source_improvement_terminal hs).1.le.trans
      (source_physical_ceiling hs).le)
  have h4 := protect_error n L (exponent4 d N (rosserAncestor 4 pre))
    hL0.le h34 (h45.trans (h56.trans h6cap))
  have h5 := protect_error n L (exponent5 d N (rosserAncestor 5 pre))
    hL0.le (h34.trans h45) (h56.trans h6cap)
  have h6 := protect_error n L (currentSixthExponent e q om N (rosserAncestor 6 pre))
    hL0.le (h34.trans (h45.trans h56)) h6cap
  have he4 : cap4 n e q om N (rosserAncestor 4 pre) =
      protect n L (exponent4 d N (rosserAncestor 4 pre)) := by
    rw [cap4, originalSeed_ancestor _ _ 4 (by decide), ← hseed]
  have he5 : cap5 n e q om N (rosserAncestor 5 pre) =
      protect n L (exponent5 d N (rosserAncestor 5 pre)) := by
    rw [cap5_eq_protect, originalSeed_ancestor _ _ 5 (by decide), ← hseed]
  have he6 : cap6 n e q om N (rosserAncestor 6 pre) =
      protect n L (currentSixthExponent e q om N (rosserAncestor 6 pre)) := by
    rw [cap6_eq_protect, originalSeed_ancestor _ _ 6 (by decide), ← hseed]
  dsimp only [ParentBounds]
  rw [he4, he5, he6]
  exact ⟨hL0, h4.1, protect_mono n L h45, protect_mono n L h56,
    h6.2.2.trans hr.2.2.2.2, h4.2, h5.2, h6.2⟩

end
end ImbalancedChen.P4AOriginalFull87FiniteParentCaps
