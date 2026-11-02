import ImbalancedChen.P1OriginalClippedSixthAttainedWinner
import ImbalancedChen.P5OriginalDescending33ActualOmission

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The two ORIGINAL ascending-tent source cells exclude every competing
clipped row, including the mask50 and pair rows. This is the original
sixth-tent33-ascending note's old-subset argument, not a transfer of a
tent source margin to a larger winning cap.

The old31 envelope of a tent source is R0. Each all11 selected mask is
an old nonempty subset plus slot6, so its tent is at most R0+t6/2=A33.
The source's strict priority says A33<clippedCap. A competing clipped
PhysicalCell would require clippedCap strictly BELOW its selected tent.
Thus only tent rows can be eligible, and all of them have the SAME cap
A33-eta and SAME selected mask33. The actual-parent seed is strictly
smaller by the existing original eligibility proof.

Together with H's nine non-tent rows, this proves source-cell attainment
for every one of the actual eleven rows. No compiler execution, numeric
search, boundary estimate or new hypothesis about winner slack occurs.
-/

namespace ImbalancedChen.P1OriginalTentSixthAttainedWinner

noncomputable section
open P1OriginalVariableFourthContinuation
open P5OriginalCommonRefinedConstructor P5OriginalCommonRefinedPreservation
open P1CommonSixthCompactActualCaller P1OriginalClippedSixthAttainedWinner
open P2CompactThirdHistorySelection P2OriginalSixthCommonScheduleAndFullQ
open P2OriginalSixthCompactArithmeticFibre P2OriginalFourthCapProducerInterface
open P5Z.OriginalDescending33ActualOmission
open Certificates.P2OriginalSixthElevenLogSemantics

/-- The original tent source's OWN old31 envelope controls every candidate
selected mask, not just mask33. The competitors remain all eleven rows. -/
theorem tent_source_all11_selected_tent_le_ascending33
    (c other : Cell) (t : Physical) (hc : c.family = .tent33)
    (hsource : PhysicalCell c t) :
    tent (selectedSum other.selectedMask t) ≤ ascending33 t := by
  have hold (mask : ℕ) (hm : mask ∈ Finset.Icc 1 31) :
      tent (subsetSum mask t) ≤ R0 t := by
    have h := branchLicense_sound (hsource.oldBranches mask hm)
    simpa only [oldCap, hc] using h
  rw [all11_selected_sum_split]
  calc
    _ ≤ tent (subsetSum (firstFiveSelectedMask other) t) + t 5 / 2 :=
      tent_add_last_le _ _ hsource.rpos.le
    _ ≤ R0 t + t 5 / 2 :=
      add_le_add_right (hold _ (firstFiveSelectedMask_mem other)) _
    _ = _ := by dsimp [R0, ascending33]; ring

/-- Literal exclusion of a different, higher clipped physical row on
either original tent source. No disjointness of invented label sets is used. -/
theorem tent_source_no_clipped_physical_cell
    (c other : Cell) (t : Physical) (hc : c.family = .tent33)
    (hsource : PhysicalCell c t) (hother : other.family ≠ .tent33) :
    ¬PhysicalCell other t := by
  intro ho
  have hpriority : ascending33 t < clippedCap t := by
    have h := hsource.priority
    cases c <;> simp_all [Cell.family, priority]
  have hlicense : newCap other t < tent (selectedSum other.selectedMask t) :=
    lt_min ho.selectedAscending ho.selectedDescending
  rw [newCap, if_neg hother] at hlicense
  have hupper := tent_source_all11_selected_tent_le_ascending33 c other t hc hsource
  exact (not_lt_of_ge hupper) (hpriority.trans hlicense)

/-- Actual winner stratification on a tent source: every eligible row has
the source's tent cap and mask33. This includes all eleven competitors and
does not require that the source and competitor have the same pattern. -/
theorem eligible_tent_competitors_same_cap_and_mask
    (d : OriginalData) (N : ℝ) (pre : List ℕ) (c : Cell)
    (hc : c.family = .tent33) (helig : eligibleSixth d N c pre)
    (other : Cell) (hother : eligibleSixth d N other pre) :
    other.family = .tent33 ∧
      newCap other (primeHistoryLogCoordinates N 6 pre) =
        newCap c (primeHistoryLogCoordinates N 6 pre) ∧
      other.selectedMask = c.selectedMask := by
  have hf : other.family = .tent33 := by
    by_contra hn
    exact tent_source_no_clipped_physical_cell c other _ hc helig.2.1 hn hother.2.1
  have hm (a : Cell) (ha : a.family = .tent33) : a.selectedMask = 33 := by
    cases a <;> simp_all [Cell.family, Cell.selectedMask]
  exact ⟨hf, by simp only [newCap, if_pos hf, if_pos hc],
    (hm other hf).trans (hm c hc).symm⟩

/-- A real original tent source attains the unchanged all11 maximum.
The existing seed is controlled by actual eligibility, not deleted. -/
theorem eligible_tent_attains_actual_lambda6
    (d : OriginalData) (N : ℝ) (pre : List ℕ) (c : Cell)
    (hc : c.family = .tent33) (helig : eligibleSixth d N c pre) :
    lambda6 d N pre = newCap c (primeHistoryLogCoordinates N 6 pre) := by
  apply le_antisymm
  · unfold lambda6
    apply finiteMax_le
    · exact (eligibleSixth_actualParent_lt_newCap d N c pre helig).le
    · intro other _hmem hother
      exact (eligible_tent_competitors_same_cap_and_mask
        d N pre c hc helig other hother).2.1.le
  · exact eligibleSixth_newCap_le_lambda6 d N c pre helig

/-- All eleven ORIGINAL source cells are actual attained winners.
H supplies the clipped case; the preceding argument closes BOTH tents. -/
theorem eligible_original_cell_attains_actual_lambda6
    (d : OriginalData) (N : ℝ) (pre : List ℕ) (c : Cell)
    (helig : eligibleSixth d N c pre) :
    lambda6 d N pre = newCap c (primeHistoryLogCoordinates N 6 pre) := by
  by_cases hc : c.family = .tent33
  · exact eligible_tent_attains_actual_lambda6 d N pre c hc helig
  · exact eligible_clipped_attains_actual_lambda6 d N pre c hc helig

/-- Original target-deleted compact tuples construct eligibility and
source-cell attainment, with no extra source/winner or slack premise. -/
theorem original_compact_cell_is_actual_winner
    {n : ℕ} (D : CompactThirdChoice (commonCore n))
    (N cap : ℕ) (hN : 1 < N) (omega : ℝ) (homega : omega ≤ D.roughFloor)
    (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ))
    (rows4 : Finset ProducerRow) (licensedOriginal : ProducerRow → Prop)
    (J5 : Finset (P1OriginalVariableFifthContinuation.Label5 D.mesh))
    (rows5 : Finset (P1OriginalVariableFifthContinuation.FifthRow D.mesh))
    (c : Cell) (p : Fin 6 → ℕ) (hp : p ∈ compactTuples c n N) :
    let d := dataOfChoice D omega rows4 licensedOriginal J5 rows5
    eligibleSixth d (N : ℝ) c (tupleHistory6 p) ∧
      lambda6 d (N : ℝ) (tupleHistory6 p) = newCap c (actualPrimeTupleLog N p) := by
  dsimp only
  let d := dataOfChoice D omega rows4 licensedOriginal J5 rows5
  have hcaller := compact_original_tuple_common_sixth_admitted D N cap hN omega homega hcap
    rows4 licensedOriginal J5 rows5 c p hp
  refine ⟨hcaller.2.1, ?_⟩
  simpa only [tupleHistory6_log] using
    eligible_original_cell_attains_actual_lambda6 d (N : ℝ) (tupleHistory6 p) c hcaller.2.1

end
end ImbalancedChen.P1OriginalTentSixthAttainedWinner
