import ImbalancedChen.ActualExtendedThirdCompactFrontier
import ImbalancedChen.ActualExtendedThirdCompactResidualProfile
import ImbalancedChen.FirstExitCandidateGeometry
import ImbalancedChen.ActualFrozenOwnCubeDensity

/-!
# The same compact policy's exact third-test density correction

Both policies use the same actual rank-two frontier before the third
candidate's admission. An adopted cell supplies its inherited first cube
at both levels. Its admitted continuation is therefore the literal gated
lower density, with the actual negative third-prefix mass. Outside the
adopted cells the frozen level is exactly the initial level and the two
complete continuations cancel.

Unique owned-cell partition and the original candidate-to-prime dictionary
then give the already defined compact residual density sum. The cap is N,
the full polynomial uses w=0 and z=N^rho, and both strict own-cube gates
remain. The initial policy still contains its dyadic first stop. No
physical progression-error estimate or initial baseline estimate is made.
-/

namespace ImbalancedChen

noncomputable section

open Set
open scoped Classical BigOperators

private def compactThirdAdmitted (Q : List ℕ → ℝ)
    (candidate : FirstExitDepthState ℕ) : ℝ :=
  if frozenParityRosserPolicy false 3 Q candidate.positive candidate.selectedPrefix = true then
    firstExitRetainedPolynomial (frozenParityRosserPolicy false 3 Q)
      (fun q : ℕ => 1 / ((q : ℝ) - 1)) candidate.selectedPrefix candidate.positive
      candidate.mass candidate.remaining
  else 0

private theorem compactThirdAdmitted_congr (Q Q' : List ℕ → ℝ)
    (candidate : FirstExitDepthState ℕ) (hlen : candidate.selectedPrefix.length = 3)
    (hQ : Q candidate.selectedPrefix = Q' candidate.selectedPrefix) :
    compactThirdAdmitted Q candidate = compactThirdAdmitted Q' candidate := by
  unfold compactThirdAdmitted
  rw [firstExitRetainedPolynomial_frozenParityRosser_eq false 3 Q _ _ _ _ _ hlen,
    firstExitRetainedPolynomial_frozenParityRosser_eq false 3 Q' _ _ _ _ _ hlen]
  simp only [frozenParityRosserPolicy, ancestorFrozenPolicy,
    rosserAncestor_self_of_length 3 candidate.selectedPrefix hlen, hQ]

private theorem compactThirdAdmitted_three (Q : List ℕ → ℝ) (N cap : ℕ)
    (p0 p1 p2 : ℕ) (hp2 : 0 < p2) (h21 : p2 < p1) (h10 : p1 < p0)
    (mass : ℝ) (hfirst : (p0 : ℝ) ^ 3 < Q [p2, p1, p0]) :
    compactThirdAdmitted Q
        {selectedPrefix := [p2, p1, p0], positive := false, mass := mass,
          remaining := roughPrimeUniverse N cap 0 (p2 : ℝ)} =
      -mass * actualOwnCubeGatedMinusDensity N cap Q [p2, p1, p0] := by
  have hsort : ([p2, p1, p0] : List ℕ).Pairwise (· < ·) := by
    apply List.pairwise_cons.mpr
    refine ⟨?_, List.pairwise_pair.mpr h10⟩
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact h21
    · have hp' : p = p0 := List.mem_singleton.mp hp
      subst p
      exact h21.trans h10
  have hP : (0 : ℝ) < ([p2, p1, p0].prod : ℕ) := by
    have hp1 : 0 < p1 := hp2.trans h21
    have hp0 : 0 < p0 := hp1.trans h10
    have hPn : 0 < ([p2, p1, p0].prod : ℕ) := by
      simp only [List.prod_cons, List.prod_nil]
      positivity
    exact_mod_cast hPn
  have hcut : ∀ p ∈ [p2, p1, p0], (p2 : ℝ) ≤ (p : ℝ) := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact le_rfl
    · exact_mod_cast h21.le
    · exact_mod_cast (h21.trans h10).le
  have hprod : (([p2, p1, p0].prod : ℕ) : ℝ) * (p2 : ℝ) ^ 2 =
      (p0 : ℝ) * p1 * p2 ^ 3 := by
    simp only [List.prod_cons, List.prod_nil, Nat.cast_mul, mul_one]
    ring
  have htest : frozenParityRosserPolicy false 3 Q false [p2, p1, p0] = true ↔
      (([p2, p1, p0].prod : ℕ) : ℝ) * (p2 : ℝ) ^ 2 < Q [p2, p1, p0] := by
    change decide (ordinaryRosserPrefixAdmissible false (Q [p2, p1, p0])
      [p2, p1, p0]) = true ↔ _
    rw [decide_eq_true_eq, historicalUnorderedThird_admissible_iff _ p0 p1 p2 hp2 h21 h10,
      hprod]
    exact and_iff_right hfirst
  unfold compactThirdAdmitted
  by_cases hc : (([p2, p1, p0].prod : ℕ) : ℝ) * (p2 : ℝ) ^ 2 < Q [p2, p1, p0]
  · rw [if_pos (htest.mpr hc)]
    have hadm := (historicalUnorderedThird_admissible_iff _ p0 p1 p2 hp2 h21 h10).mpr
      ⟨hfirst, hprod ▸ hc⟩
    have hd := firstExitRetainedPolynomial_frozenParityRosser_actualDensity
      false 3 Q N cap (p2 : ℝ) [p2, p1, p0] rfl (by decide)
      hadm hsort hP hcut false mass rfl
    have hres : ordinaryRosserResidualLower false 3 = true := by decide
    rw [hd]
    simp only [hres, if_true, signedTreeCoefficient_false,
      actualOwnCubeGatedMinusDensity, List.headD_cons, if_pos hc]
  · rw [if_neg (fun ht => hc (htest.mp ht))]
    simp only [actualOwnCubeGatedMinusDensity, List.headD_cons, if_neg hc, mul_zero]

private theorem compactUpper_ownSplice (e h : ℝ) (m N : ℕ) :
    firstExitDepthSplicePolicy 2 (actualExtendedThirdCompactUpperPolicy e h m N)
        (frozenParityRosserPolicy false 3 (actualExtendedThirdCompactRawLevel e h m N)) =
      actualExtendedThirdCompactUpperPolicy e h m N := by
  funext positive history
  by_cases hlen : history.length ≤ 2
  · simp only [firstExitDepthSplicePolicy, if_pos hlen]
  · simp only [firstExitDepthSplicePolicy, if_neg hlen,
      actualExtendedThirdCompactUpperPolicy, thirdCappedUpperPolicy]

private theorem compactInitial_ownSplice (e h : ℝ) (m N : ℕ) :
    firstExitDepthSplicePolicy 2 (actualExtendedThirdCompactUpperPolicy e h m N)
        (frozenParityRosserPolicy false 3 (fun _ => (N : ℝ) ^ (thirdPrefixTheta - 2 * e))) =
      actualExtendedThirdCompactInitialPolicy e m N := by
  funext positive history
  by_cases hlen : history.length ≤ 2
  · rw [firstExitDepthSplicePolicy, if_pos hlen]
    exact actualExtendedThirdCompactUpperPolicy_through_two e h m N positive history hlen
  · have hne : history.length ≠ 1 := by omega
    simp [firstExitDepthSplicePolicy, hlen, frozenParityRosserPolicy, ancestorFrozenPolicy,
      ordinaryParityRosserPolicy, actualExtendedThirdCompactInitialPolicy, oddFirstExitPolicy, hne]

private theorem compactCandidate_cell {e h : ℝ} {m N cap : ℕ}
    (hN : 1 < N) (he0 : 0 < e) (he : e ≤ 1 / 384)
    (hmesh : actualExtendedThirdDyadicStep m ≤ e / 2)
    (frontier : FirstExitDepthState ℕ)
    (hf : frontier ∈ firstExitDepthFrontier 2 (actualExtendedThirdCompactUpperPolicy e h m N)
      (fun q : ℕ => 1 / ((q : ℝ) - 1)) [] true 1
      (roughPrimeUniverse N cap 0 ((N : ℝ) ^ thirdPrefixRho)))
    (candidate : FirstExitDepthState ℕ)
    (hc : candidate ∈ firstExitNextSelectionCandidates
      (fun q : ℕ => 1 / ((q : ℝ) - 1)) frontier.selectedPrefix
      frontier.positive frontier.mass frontier.remaining)
    {j : ActualExtendedThirdDyadicLabel m} (hj : j ∈ actualExtendedThirdCompactCells e h m)
    (ht : primeHistoryLogCoordinates (N : ℝ) 3 candidate.selectedPrefix ∈
      actualExtendedThirdOwnedCell m j) :
    (compactThirdAdmitted (actualExtendedThirdCompactRawLevel e h m N) candidate -
      compactThirdAdmitted (fun _ => (N : ℝ) ^ (thirdPrefixTheta - 2 * e)) candidate) *
        Real.log (N : ℝ) / singularSeries N =
      (candidate.selectedPrefix.map (fun q : ℕ => 1 / ((q : ℝ) - 1))).prod *
        (actualPrimeTupleOwnCubeMinus N cap (thirdPrefixTheta - 2 * e)
            (primeHistoryTuple 3 candidate.selectedPrefix) -
          actualPrimeTupleOwnCubeMinus N cap (actualExtendedThirdPhysicalLevel e m j)
            (primeHistoryTuple 3 candidate.selectedPrefix)) := by
  obtain ⟨hlen, hsort, _hP, _hcut, hrem, hsign, hmass, hprime⟩ :=
    actualPrimeNextSelection_geometry 2 (actualExtendedThirdCompactUpperPolicy e h m N)
      N cap _ frontier hf candidate hc
  obtain ⟨p2, tail2, hs2, hl2⟩ := List.length_eq_succ_iff.mp hlen
  obtain ⟨p1, tail1, hs1, hl1⟩ := List.length_eq_succ_iff.mp hl2
  obtain ⟨p0, tail0, hs0, hl0⟩ := List.length_eq_succ_iff.mp hl1
  have hz0 : tail0 = [] := List.length_eq_zero_iff.mp hl0
  have hhist : candidate.selectedPrefix = [p2, p1, p0] := by rw [← hs2, ← hs1, ← hs0, hz0]
  have hp2 : 0 < p2 := (hprime p2 (by simp [hhist])).pos
  have h21 : p2 < p1 := (List.pairwise_cons.mp (hhist ▸ hsort)).1 p1 (by simp)
  have h10 : p1 < p0 := (List.pairwise_cons.mp (List.pairwise_cons.mp
    (hhist ▸ hsort)).2).1 p0 (by simp)
  have hfalse : candidate.positive = false := by simpa [hhist, evenListLength] using hsign
  have hrem' : candidate.remaining = roughPrimeUniverse N cap 0 (p2 : ℝ) := by
    simpa only [hhist, List.headD_cons] using hrem
  have ht' : primeHistoryLogCoordinates (N : ℝ) 3 [p2, p1, p0] ∈
      actualExtendedThirdOwnedCell m j := hhist ▸ ht
  have hfirst := actualExtendedThirdCompactCell_prime_firstCube hN he0 he hmesh
    p0 p1 p2 (by omega) hj ht'
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hfirstOld : (p0 : ℝ) ^ 3 < (N : ℝ) ^ (thirdPrefixTheta - 2 * e) :=
    hfirst.trans_le (Real.rpow_le_rpow_of_exponent_le hNr.le
      (thirdPrefixBufferedCap_le_root e (actualExtendedThirdPhysicalGamma e m j)))
  have hlevel : actualExtendedThirdCompactRawLevel e h m N [p2, p1, p0] =
      (N : ℝ) ^ actualExtendedThirdPhysicalLevel e m j :=
    actualExtendedThirdCompactRawLevel_on_cell hj ht'
  have hnew := compactThirdAdmitted_three (actualExtendedThirdCompactRawLevel e h m N)
    N cap p0 p1 p2 hp2 h21 h10 candidate.mass (by rw [hlevel]; exact hfirst)
  have hold := compactThirdAdmitted_three (fun _ => (N : ℝ) ^ (thirdPrefixTheta - 2 * e))
    N cap p0 p1 p2 hp2 h21 h10 candidate.mass hfirstOld
  have hnew' : compactThirdAdmitted (actualExtendedThirdCompactRawLevel e h m N) candidate =
      -candidate.mass * actualOwnCubeGatedMinusDensity N cap
        (actualExtendedThirdCompactRawLevel e h m N) candidate.selectedPrefix := by
    simpa only [compactThirdAdmitted, hhist, hfalse, hrem'] using hnew
  have hold' : compactThirdAdmitted (fun _ => (N : ℝ) ^ (thirdPrefixTheta - 2 * e)) candidate =
      -candidate.mass * actualOwnCubeGatedMinusDensity N cap
        (fun _ => (N : ℝ) ^ (thirdPrefixTheta - 2 * e)) candidate.selectedPrefix := by
    simpa only [compactThirdAdmitted, hhist, hfalse, hrem'] using hold
  rw [hnew', hold', hmass,
    actualPrimeTupleOwnCubeMinus_primeHistoryTuple N cap (thirdPrefixTheta - 2 * e) hlen,
    actualPrimeTupleOwnCubeMinus_primeHistoryTuple N cap (actualExtendedThirdPhysicalLevel e m j) hlen]
  have hgate : actualOwnCubeGatedMinusDensity N cap (actualExtendedThirdCompactRawLevel e h m N)
      candidate.selectedPrefix = actualOwnCubeGatedMinusDensity N cap
        (fun _ => (N : ℝ) ^ actualExtendedThirdPhysicalLevel e m j) candidate.selectedPrefix := by
    unfold actualOwnCubeGatedMinusDensity
    rw [actualExtendedThirdCompactRawLevel_on_cell hj ht]
  rw [hgate]
  ring

private theorem compactCandidate_partition {e h : ℝ} {m N cap : ℕ}
    (hN : 1 < N) (he0 : 0 < e) (he : e ≤ 1 / 384)
    (hmesh : actualExtendedThirdDyadicStep m ≤ e / 2)
    (frontier : FirstExitDepthState ℕ)
    (hf : frontier ∈ firstExitDepthFrontier 2 (actualExtendedThirdCompactUpperPolicy e h m N)
      (fun q : ℕ => 1 / ((q : ℝ) - 1)) [] true 1
      (roughPrimeUniverse N cap 0 ((N : ℝ) ^ thirdPrefixRho)))
    (candidate : FirstExitDepthState ℕ)
    (hc : candidate ∈ firstExitNextSelectionCandidates
      (fun q : ℕ => 1 / ((q : ℝ) - 1)) frontier.selectedPrefix
      frontier.positive frontier.mass frontier.remaining) :
    (compactThirdAdmitted (actualExtendedThirdCompactRawLevel e h m N) candidate -
      compactThirdAdmitted (fun _ => (N : ℝ) ^ (thirdPrefixTheta - 2 * e)) candidate) *
        Real.log (N : ℝ) / singularSeries N =
      ∑ j ∈ actualExtendedThirdCompactCells e h m,
        (candidate.selectedPrefix.map (fun q : ℕ => 1 / ((q : ℝ) - 1))).prod *
          (if primeHistoryLogCoordinates (N : ℝ) 3 candidate.selectedPrefix ∈
              actualExtendedThirdOwnedCell m j then
            actualPrimeTupleOwnCubeMinus N cap (thirdPrefixTheta - 2 * e)
                (primeHistoryTuple 3 candidate.selectedPrefix) -
              actualPrimeTupleOwnCubeMinus N cap (actualExtendedThirdPhysicalLevel e m j)
                (primeHistoryTuple 3 candidate.selectedPrefix) else 0) := by
  by_cases ha : actualExtendedThirdCompactActive e h m N candidate.selectedPrefix
  · obtain ⟨j, hj, ht⟩ := ha
    rw [Finset.sum_eq_single_of_mem j hj]
    · rw [if_pos ht]
      exact compactCandidate_cell hN he0 he hmesh frontier hf candidate hc hj ht
    · intro k _hk hkj
      have hnot : primeHistoryLogCoordinates (N : ℝ) 3 candidate.selectedPrefix ∉
          actualExtendedThirdOwnedCell m k := by
        intro htk
        exact hkj (actualExtendedThirdOwnedCell_unique htk ht)
      rw [if_neg hnot, mul_zero]
  · have hlen := (actualPrimeNextSelection_geometry 2
      (actualExtendedThirdCompactUpperPolicy e h m N) N cap _ frontier hf candidate hc).1
    have hsame := compactThirdAdmitted_congr (actualExtendedThirdCompactRawLevel e h m N)
      (fun _ => (N : ℝ) ^ (thirdPrefixTheta - 2 * e)) candidate hlen
      (actualExtendedThirdCompactRawLevel_inactive ha)
    rw [hsame, sub_self, zero_mul, zero_div]
    symm
    apply Finset.sum_eq_zero
    intro j hj
    rw [if_neg (fun ht => ha ⟨j, hj, ht⟩), mul_zero]

private theorem compactFrontierCell_residual {e h : ℝ} {m N : ℕ}
    (hN : 1 < N) (hh : 0 < h) (he0 : 0 < e) (he : e ≤ 1 / 384)
    (hmesh : actualExtendedThirdDyadicStep m ≤ e / 2)
    {j : ActualExtendedThirdDyadicLabel m} (hj : j ∈ actualExtendedThirdCompactCells e h m) :
    actualExtendedThirdCompactFrontierCellSum e h m N N 0 j
        (fun p => actualPrimeTupleOwnCubeMinus N N (thirdPrefixTheta - 2 * e) p -
          actualPrimeTupleOwnCubeMinus N N (actualExtendedThirdPhysicalLevel e m j) p) =
      actualExtendedThirdCellResidualDensitySum N e h m j := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hcap : (N : ℝ) ^ thirdPrefixRho ≤ (N : ℝ) := by
    calc
      _ ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hNr.le
        (by norm_num [thirdPrefixRho])
      _ = _ := Real.rpow_one _
  rw [actualExtendedThirdCompactFrontierCellSum_eq_tuple_sum hN hh he0 he hmesh 0
    (by positivity) hcap hj]
  unfold actualExtendedThirdDistinctCellPrimeTuples actualExtendedThirdCellResidualDensitySum
    actualPrimeBoxOwnCubeMinusSum
  rw [Finset.sum_filter, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _hp
  by_cases hr : actualPrimeTupleLog N p ∈ actualExtendedThirdDistinctCellPrimeRegion m j
  · simp only [if_pos hr]
    ring
  · simp only [if_neg hr, mul_zero, sub_self]

/-- Exact finite identity for this same upper policy and this same initial
dyadic-first-stop policy. No analytic or saving identity is assumed. -/
theorem actualExtendedThirdCompactPolicySaving {e h : ℝ} {m N : ℕ}
    (hN : 1 < N) (hh : 0 < h) (he0 : 0 < e) (he : e ≤ 1 / 384)
    (hmesh : actualExtendedThirdDyadicStep m ≤ e / 2) :
    (firstExitRetainedPolynomial (actualExtendedThirdCompactUpperPolicy e h m N)
        (fun q : ℕ => 1 / ((q : ℝ) - 1)) [] true 1
        (roughPrimeUniverse N N 0 ((N : ℝ) ^ thirdPrefixRho)) -
      firstExitRetainedPolynomial (actualExtendedThirdCompactInitialPolicy e m N)
        (fun q : ℕ => 1 / ((q : ℝ) - 1)) [] true 1
        (roughPrimeUniverse N N 0 ((N : ℝ) ^ thirdPrefixRho))) *
        Real.log (N : ℝ) / singularSeries N =
      actualExtendedThirdCompactResidualDensitySum N e h m := by
  let parent := actualExtendedThirdCompactUpperPolicy e h m N
  let weight := fun q : ℕ => 1 / ((q : ℝ) - 1)
  let carrier := roughPrimeUniverse N N 0 ((N : ℝ) ^ thirdPrefixRho)
  let Qnew := actualExtendedThirdCompactRawLevel e h m N
  let Qold := fun _ : List ℕ => (N : ℝ) ^ (thirdPrefixTheta - 2 * e)
  let delta := fun c : FirstExitDepthState ℕ =>
    compactThirdAdmitted Qnew c - compactThirdAdmitted Qold c
  let F := fun (j : ActualExtendedThirdDyadicLabel m) (c : FirstExitDepthState ℕ) =>
    (c.selectedPrefix.map weight).prod *
      (if primeHistoryLogCoordinates (N : ℝ) 3 c.selectedPrefix ∈
          actualExtendedThirdOwnedCell m j then
        actualPrimeTupleOwnCubeMinus N N (thirdPrefixTheta - 2 * e)
            (primeHistoryTuple 3 c.selectedPrefix) -
          actualPrimeTupleOwnCubeMinus N N (actualExtendedThirdPhysicalLevel e m j)
            (primeHistoryTuple 3 c.selectedPrefix) else 0)
  have hroot := firstExitRetainedPolynomial_ownCubeSplice_root_sub_eq 2 parent
    (frozenParityRosserPolicy false 3 Qnew) (frozenParityRosserPolicy false 3 Qold) weight carrier
  rw [compactUpper_ownSplice e h m N, compactInitial_ownSplice e h m N] at hroot
  have hflat (states : List (FirstExitDepthState ℕ)) :
      (states.map (fun f => ((firstExitNextSelectionCandidates weight f.selectedPrefix
        f.positive f.mass f.remaining).map delta).sum)).sum =
      ((states.flatMap (fun f => firstExitNextSelectionCandidates weight f.selectedPrefix
        f.positive f.mass f.remaining)).map delta).sum := by
    induction states with
    | nil => rfl
    | cons f fs ih => simp only [List.map_cons, List.sum_cons, List.flatMap_cons,
        List.map_append, List.sum_append, ih]
  have hfinite :
      firstExitRetainedPolynomial parent weight [] true 1 carrier -
        firstExitRetainedPolynomial (actualExtendedThirdCompactInitialPolicy e m N)
          weight [] true 1 carrier =
        ((firstExitFrontierCandidates 2 parent weight carrier).map delta).sum := by
    exact hroot.trans (hflat _)
  have hnorm (states : List (FirstExitDepthState ℕ)) :
      (states.map delta).sum * Real.log (N : ℝ) / singularSeries N =
        (states.map (fun c => delta c * Real.log (N : ℝ) / singularSeries N)).sum := by
    induction states with
    | nil => simp
    | cons c cs ih =>
        simp only [List.map_cons, List.sum_cons]
        rw [← ih]
        ring
  have hswap (states : List (FirstExitDepthState ℕ)) :
      (states.map (fun c => ∑ j ∈ actualExtendedThirdCompactCells e h m, F j c)).sum =
        ∑ j ∈ actualExtendedThirdCompactCells e h m, (states.map (F j)).sum := by
    induction states with
    | nil => simp
    | cons c cs ih =>
        simp only [List.map_cons, List.sum_cons]
        rw [ih, Finset.sum_add_distrib]
  change (firstExitRetainedPolynomial parent weight [] true 1 carrier -
    firstExitRetainedPolynomial (actualExtendedThirdCompactInitialPolicy e m N)
      weight [] true 1 carrier) * Real.log (N : ℝ) / singularSeries N = _
  rw [hfinite, hnorm]
  have hpartition :
      ((firstExitFrontierCandidates 2 parent weight carrier).map
        (fun c => delta c * Real.log (N : ℝ) / singularSeries N)).sum =
      ((firstExitFrontierCandidates 2 parent weight carrier).map
        (fun c => ∑ j ∈ actualExtendedThirdCompactCells e h m, F j c)).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro c hc
    obtain ⟨frontier, hf, hc⟩ := List.mem_flatMap.mp hc
    exact compactCandidate_partition hN he0 he hmesh frontier hf c hc
  rw [hpartition, hswap]
  change (∑ j ∈ actualExtendedThirdCompactCells e h m,
    actualExtendedThirdCompactFrontierCellSum e h m N N 0 j
      (fun p => actualPrimeTupleOwnCubeMinus N N (thirdPrefixTheta - 2 * e) p -
        actualPrimeTupleOwnCubeMinus N N (actualExtendedThirdPhysicalLevel e m j) p)) = _
  unfold actualExtendedThirdCompactResidualDensitySum
  exact Finset.sum_congr rfl (fun _j hj => compactFrontierCell_residual hN hh he0 he hmesh hj)

end

end ImbalancedChen
