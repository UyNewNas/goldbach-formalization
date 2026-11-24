import ImbalancedChen.P5OriginalCommonFourthActualAdmission
import ImbalancedChen.P5OriginalFifthArchiveFiniteIdentity

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The missing literal caller is derived for the actual E common policy.
Full inherited admissibility is supplied by actual recursive ancestor
tests, h45 by its own finite maximum, and the literal next-candidate sum
by the original exact prime-tuple dictionary. Both strict own-cube gates,
target, enumeration cap, current parent and signed small-beta correction
remain unchanged. No density/gain/PP/K conclusion is an input hypothesis.
-/
namespace ImbalancedChen.P5OriginalCommonFifthPhysicalCaller
noncomputable section
open scoped Classical BigOperators
open P5OriginalCommonRefinedConstructor P5OriginalCommonRefinedPreservation
open P5OriginalCommonFourthActualAdmission
open P1CorrectedFifthCausalTupleDictionary
open P4AOriginalVariableFifthPhysicalLedger

def actualCharge (d : OriginalData) (N cap : ℕ) (z : ℝ) : ℝ :=
  ((firstExitDepthFrontier 4 (common3 d (N : ℝ))
    (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z)).map
    (fun frontier => ((firstExitNextSelectionCandidates (fun p : ℕ => 1 / ((p : ℝ) - 1))
      frontier.selectedPrefix frontier.positive frontier.mass frontier.remaining).map
      (fun candidate => (candidate.selectedPrefix.map (fun p : ℕ => 1 / ((p : ℝ) - 1))).prod *
        (actualOwnCubeGatedMinusDensity N cap (level5 d (N : ℝ)) candidate.selectedPrefix -
          actualOwnCubeGatedMinusDensity N cap
            (fun pre => level4 d (N : ℝ) (rosserAncestor 4 pre)) candidate.selectedPrefix))).sum)).sum

def literalCharge (d : OriginalData) (N cap : ℕ) (z : ℝ) : ℝ :=
  ∑ p ∈ firstExitFrontierTuples 4 (common3 d (N : ℝ)) (roughPrimeUniverse N cap 0 z),
    (∏ i, 1 / ((p i : ℝ) - 1)) *
      literalTupleDifference (level4 d (N : ℝ)) (level5 d (N : ℝ)) N cap p

theorem actual_h45 (d : OriginalData) (N cap : ℕ) (hN : 1 ≤ (N : ℝ)) (z : ℝ)
    (frontier candidate : FirstExitDepthState ℕ)
    (hf : frontier ∈ firstExitDepthFrontier 4 (common3 d (N : ℝ))
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z))
    (hc : candidate ∈ firstExitNextSelectionCandidates
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) frontier.selectedPrefix
      frontier.positive frontier.mass frontier.remaining) :
    level4 d (N : ℝ) frontier.selectedPrefix ≤ level5 d (N : ℝ) candidate.selectedPrefix := by
  have hl := firstExitDepthFrontier_selected_length 4 _ _ [] _ true 1 (by simp) frontier hf
  obtain ⟨before, q, after, _hrem, hstate⟩ :=
    (mem_firstExitNextSelectionCandidates_iff (fun p : ℕ => 1 / ((p : ℝ) - 1))
      frontier.selectedPrefix frontier.remaining frontier.positive frontier.mass candidate).mp hc
  have ha : rosserAncestor 4 candidate.selectedPrefix = frontier.selectedPrefix := by
    rw [hstate]
    calc
      rosserAncestor 4 (q :: frontier.selectedPrefix) = rosserAncestor 4 frontier.selectedPrefix :=
        rosserAncestor_cons 4 q frontier.selectedPrefix (by omega)
      _ = frontier.selectedPrefix := rosserAncestor_self_of_length 4 frontier.selectedPrefix hl
  have hh := Real.rpow_le_rpow_of_exponent_le hN (inherited4_le_exponent5 d (N : ℝ) candidate.selectedPrefix)
  simpa only [ha] using hh

/-- The actual inherited tests are proved, rather than assumed as hpre. -/
theorem raw_fourth_sub_fifth_eq_actualCharge (d : OriginalData) (N cap : ℕ)
    (hN : 1 ≤ (N : ℝ)) (z : ℝ) :
    raw (policy4 d (N : ℝ)) N cap 0 z - raw (policy5 d (N : ℝ)) N cap 0 z =
      actualCharge d N cap z := by
  have h4 := UpperPolicyFiniteBridge.firstExitRetainedPolynomial_eq_fixedRoughDensity_of_even_retained
    (policy4 d (N : ℝ)) (policy4_even d (N : ℝ)) N cap 0 z
  have h5 := UpperPolicyFiniteBridge.firstExitRetainedPolynomial_eq_fixedRoughDensity_of_even_retained
    (policy5 d (N : ℝ)) (policy5_even d (N : ℝ)) N cap 0 z
  change _ = raw (policy4 d (N : ℝ)) N cap 0 z at h4
  change _ = raw (policy5 d (N : ℝ)) N cap 0 z at h5
  rw [← h4, ← h5]
  exact actual_frozen_upper_five_ownCube_saving (common3 d (N : ℝ))
    (level4 d (N : ℝ)) (level5 d (N : ℝ)) N cap z
    (actual_common_fourth_frontier_admissible d N cap hN z)
    (actual_h45 d N cap hN z)

/-- Normalization and prime-tuple reindex preserve the complete fifth
candidate history, before either of its own admission tests. -/
theorem normalized_actualCharge_eq_literalCharge (d : OriginalData) (N cap : ℕ) (z : ℝ) :
    actualCharge d N cap z * Real.log (N : ℝ) / singularSeries N = literalCharge d N cap z := by
  let parent := common3 d (N : ℝ)
  let h := fun p : ℕ => 1 / ((p : ℝ) - 1)
  let states := firstExitDepthFrontier 4 parent h [] true 1 (roughPrimeUniverse N cap 0 z)
  let candidates (s : FirstExitDepthState ℕ) :=
    firstExitNextSelectionCandidates h s.selectedPrefix s.positive s.mass s.remaining
  let residual (pre : List ℕ) :=
    actualOwnCubeGatedMinusDensity N cap (level5 d (N : ℝ)) pre -
      actualOwnCubeGatedMinusDensity N cap (fun q => level4 d (N : ℝ) (rosserAncestor 4 q)) pre
  let F := literalTupleDifference (level4 d (N : ℝ)) (level5 d (N : ℝ)) N cap
  have hn : actualCharge d N cap z * Real.log (N : ℝ) / singularSeries N =
      (states.map (fun s => ((candidates s).map (fun c =>
        (c.selectedPrefix.map h).prod * residual c.selectedPrefix *
          (Real.log (N : ℝ) / singularSeries N))).sum)).sum := by
    simp only [List.sum_map_mul_right]
    change _ * Real.log (N : ℝ) / singularSeries N =
      actualCharge d N cap z * (Real.log (N : ℝ) / singularSeries N)
    ring
  rw [hn]
  have heq : (states.map (fun s => ((candidates s).map (fun c =>
      (c.selectedPrefix.map h).prod * residual c.selectedPrefix *
        (Real.log (N : ℝ) / singularSeries N))).sum)).sum =
      (states.map (fun s => ((candidates s).map (fun c =>
        (c.selectedPrefix.map h).prod * F (primeHistoryTuple 5 c.selectedPrefix))).sum)).sum := by
    congr 1
    apply List.map_congr_left
    intro s hs
    congr 1
    apply List.map_congr_left
    intro c hc
    have hl := (actualPrimeNextSelection_geometry 4 parent N cap z s hs c hc).1
    dsimp [F]
    rw [literalTupleDifference_history _ _ N cap c.selectedPrefix hl]
    dsimp [residual]
    ring
  rw [heq]
  exact actualPrimeFrontier_candidates_weighted_sum_eq_tuple_sum 4 parent h N cap 0 z F

/-- The physical attachment keeps the genuine difference of negative
rough masses. It is never replaced by beta-plus alone. -/
theorem physical_fourth_sub_fifth (d : OriginalData) (N cap : ℕ)
    (hN : 1 ≤ (N : ℝ)) (z L : ℝ) :
    physical (policy4 d (N : ℝ)) N cap 0 z L - physical (policy5 d (N : ℝ)) N cap 0 z L =
      actualCharge d N cap z * smallPlus N cap 0 L +
        (negative (policy4 d (N : ℝ)) N cap 0 z - negative (policy5 d (N : ℝ)) N cap 0 z) *
          (smallPlus N cap 0 L - smallMinus N cap 0 L) := by
  rw [physical_eq_signed_raw, physical_eq_signed_raw,
    ← raw_fourth_sub_fifth_eq_actualCharge d N cap hN z]
  ring

theorem normalized_physical_fourth_sub_fifth (d : OriginalData) (N cap : ℕ)
    (hN : 1 ≤ (N : ℝ)) (z L : ℝ) :
    (physical (policy4 d (N : ℝ)) N cap 0 z L - physical (policy5 d (N : ℝ)) N cap 0 z L) *
        Real.log (N : ℝ) / singularSeries N =
      literalCharge d N cap z * smallPlus N cap 0 L +
        ((negative (policy4 d (N : ℝ)) N cap 0 z - negative (policy5 d (N : ℝ)) N cap 0 z) *
          Real.log (N : ℝ) / singularSeries N) * (smallPlus N cap 0 L - smallMinus N cap 0 L) := by
  rw [physical_fourth_sub_fifth d N cap hN z L,
    ← normalized_actualCharge_eq_literalCharge d N cap z]
  simp only [div_eq_mul_inv]
  ring

/-- Instantiates the real independently loaded archive and its ORIGINAL
licensed-owner filters. The physical correction remains on COMMON rho. -/
theorem archive_normalized_physical_difference
    (rows4 : Finset P2OriginalFourthCapProducerInterface.ProducerRow)
    (licensed4 : P2OriginalFourthCapProducerInterface.ProducerRow → Prop)
    (e : ℚ) (q : ℕ) (chi omega : ℝ) (N cap : ℕ) (hN : 1 ≤ (N : ℝ)) (z L : ℝ) :
    let d := P1HistoricalFifthCommonPolicyInputs.sourceData rows4 licensed4 e q chi omega
    (physical (policy4 d (N : ℝ)) N cap 0 z L - physical (policy5 d (N : ℝ)) N cap 0 z L) *
        Real.log (N : ℝ) / singularSeries N =
      P4AOriginalVariableFifthPhysicalLedger.fifthTupleCharge e chi
        (P1OriginalFifthGrid400RefinedFullBoxCover.refinedMesh q) omega rows4 licensed4
        (P1HistoricalFifthIndexedOwnerArchive.globalOwners e q chi omega)
        (P1HistoricalFifthIndexedOwnerArchive.licensedRows e q chi omega) N cap z * smallPlus N cap 0 L +
        ((negative (policy4 d (N : ℝ)) N cap 0 z - negative (policy5 d (N : ℝ)) N cap 0 z) *
          Real.log (N : ℝ) / singularSeries N) * (smallPlus N cap 0 L - smallMinus N cap 0 L) := by
  dsimp only
  rw [normalized_physical_fourth_sub_fifth _ N cap hN z L]
  exact congrArg (fun x : ℝ => x * smallPlus N cap 0 L + _)
    (P5OriginalFifthArchiveFiniteIdentity.commonLiteralCharge_eq_original
      rows4 licensed4 e q chi omega N cap z)

end
end ImbalancedChen.P5OriginalCommonFifthPhysicalCaller
