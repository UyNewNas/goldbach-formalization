import ImbalancedChen.P1OriginalVariableFourthActiveOnly

/-!
# Original active mesh labels are covered at half the rough cutoff

SOURCE_WRITTEN / UNCOMPILED / NOT_ROOT_ACCEPTED / CODE_ONLY.

A mesh cell meeting t2>=omega has lower third endpoint above omega minus
one ACTUAL mesh step. Under the explicit finite geometric step bound it
is therefore selected at omega/2, even if it is not selected at omega.
The original Gamma, first-stop and all cube gates remain the same.

On actual tuples active at omega, lowering only this rough cutoff leaves
the literal rawQ3 seed, variable producerLevel4 and signed PLUS summand
unchanged. The actual fourth admission is unchanged there as well.
No arithmetic mean, complement estimate or endpoint coverage is assumed.
-/

namespace ImbalancedChen.P1OriginalVariableFourthActiveMeshCover

noncomputable section
open scoped Classical BigOperators
open Set HistoricalThirdCoarse
open P1OriginalCoarseContinuation P1OriginalCoarseFourthResidual
open P1OriginalVariableFourthContinuation
open P1OriginalVariableFourthFullSourceActivation
open P1OriginalVariableFourthActiveOnly
open HistoricalThirdCoarse.P1OriginalFourth
open P2OriginalFourthCapProducerInterface

/-- A genuine intersecting mesh cell loses at most its one actual width
from a pointwise coordinate lower bound. This includes a cutoff face. -/
theorem meshLo_gt_cutoff_sub_step {d : ℕ} (m : ℕ)
    (j : Fin d → Fin (m + 1)) {t : Fin d → ℝ}
    (ht : t ∈ logPrimeMeshCell 0 (19 / 96) m j) (i : Fin d)
    (omega : ℝ) (hactive : omega ≤ t i) :
    omega - logPrimeMeshStep 0 (19 / 96) m < logPrimeMeshLo 0 (19 / 96) m j i := by
  have hhi := (mem_logPrimeMeshCell.mp ht i).2
  rw [logPrimeMeshHi_eq_lo_add_step] at hhi
  linarith

theorem meshLo_ge_half_of_active (m : ℕ) (j : FourthCell m)
    {t : Fin 4 → ℝ} (ht : t ∈ logPrimeMeshCell 0 (19 / 96) m j)
    (omega : ℝ) (hactive : omega ≤ t 2)
    (hmesh : logPrimeMeshStep 0 (19 / 96) m ≤ omega / 2) :
    omega / 2 ≤ logPrimeMeshLo 0 (19 / 96) m (prefix3 j) 2 := by
  have ht3 := mem_logPrimeMeshCell_historicalPrefixProject (by omega : 3 ≤ 4) ht
  have hlo := meshLo_gt_cutoff_sub_step m (prefix3 j) ht3 2 omega hactive
  linarith

/-- Every actually occupied active adopted label has the SAME fourth
label among the finite all-label selection at the enlarged cutoff. -/
theorem active_source_label_selected_half
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (hmesh : logPrimeMeshStep 0 (19 / 96) m ≤ omega / 2)
    (label : Label m) (hl : label ∈ activeAdoptedLabels (e : ℝ) chi m)
    {t : Point} (ht : t ∈ sourceBranch (e : ℝ) chi m omega label) :
    label.1 ∈ selectedFourthCells e chi m (omega / 2) Finset.univ := by
  have hlic := (mem_activeAdoptedLabels (e : ℝ) chi m label).mp hl
  have hrough := activeAdopted_source_rough (e : ℝ) chi m omega label hl ht
  have hlo := meshLo_ge_half_of_active m label.1 ht.1.1 omega hrough hmesh
  apply (mem_selectedFourthCells e chi m (omega / 2) Finset.univ label.1).mpr
  refine ⟨Finset.mem_univ _, hlic.2, ?_⟩
  have hcast : (qLogPrimeMeshLo 0 (19 / 96) m (prefix3 label.1) 2 : ℝ) =
      logPrimeMeshLo 0 (19 / 96) m (prefix3 label.1) 2 := by
    simpa only [Rat.cast_zero, Rat.cast_div, Rat.cast_ofNat] using
      congrFun (cast_qLogPrimeMeshLo 0 (19 / 96) m (prefix3 label.1)) 2
  simpa only [hcast] using hlo

/-- Finite occupied branch carrier; nonempty geometric intersection is
retained explicitly rather than assigned to every active flag. -/
def occupiedActiveLabels (e chi : ℝ) (m : ℕ) (omega : ℝ) : Finset (Label m) :=
  (activeAdoptedLabels e chi m).filter fun label => (sourceBranch e chi m omega label).Nonempty

theorem occupiedActiveLabels_image_subset_selected_half
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (hmesh : logPrimeMeshStep 0 (19 / 96) m ≤ omega / 2) :
    (occupiedActiveLabels (e : ℝ) chi m omega).image Prod.fst ⊆
      selectedFourthCells e chi m (omega / 2) Finset.univ := by
  intro j hj
  obtain ⟨label, hl, rfl⟩ := Finset.mem_image.mp hj
  obtain ⟨hl, t, ht⟩ := Finset.mem_filter.mp hl
  exact active_source_label_selected_half e chi m omega hmesh label hl ht

/-- Only the inclusive rough row changes. Original firstStop, initial
cube and current Gamma cubes are literally preserved. -/
theorem jointRegion_mono_rough (e : ℝ) (m : ℕ) (omega' omega : ℝ)
    (hcut : omega' ≤ omega) (j : Cell m) :
    jointRegion e omega m j ⊆ jointRegion e omega' m j := by
  intro t ht
  exact ⟨ht.1, hcut.trans ht.2⟩

theorem active_source_branch_subset_half_sourceRegion
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) (homega : 0 ≤ omega)
    (label : Label m) (hl : label ∈ activeAdoptedLabels (e : ℝ) chi m) :
    sourceBranch (e : ℝ) chi m omega label ⊆
      P1OriginalFourthLimit.sourceRegion e m (omega / 2) label.1 := by
  intro t ht
  have hlic := (mem_activeAdoptedLabels (e : ℝ) chi m label).mp hl
  have hseed : branchSeed (e : ℝ) chi m label =
      levelExponent (e : ℝ) (box m (prefix3 label.1)) := if_pos hlic
  have hrough := activeAdopted_source_rough (e : ℝ) chi m omega label hl ht
  have hjoint : t ∈ jointRegion (e : ℝ) omega m (prefix3 label.1) := by
    refine ⟨?_, hrough⟩
    simpa only [hseed] using ht.2
  have hhalf := jointRegion_mono_rough (e : ℝ) m (omega / 2) omega
    (by linarith) (prefix3 label.1) hjoint
  rw [P1OriginalFourthLimit.sourceRegion, jointCell_same_mesh]
  exact ⟨ht.1.1, hhalf⟩

/-- Raw coordinate seeds agree at any two cutoffs below the actual
active coordinate. No whole-cell rough bound is required. -/
theorem seedExponent_cutoff_eq_on_active
    (e chi : ℝ) (m : ℕ) (omega' omega : ℝ) (hcut : omega' ≤ omega)
    (N : ℕ) (hN : 1 < N) (p : Fin 4 → ℕ) (hp : ∀ i, 0 < p i)
    (hactive : omega ≤ actualPrimeTupleLog N p 2) :
    seedExponent e chi m omega (N : ℝ) (tupleHistory p) =
      seedExponent e chi m omega' (N : ℝ) (tupleHistory p) := by
  rw [seedExponent_eq_coordinateSeed e chi m omega N hN p hp,
    seedExponent_eq_coordinateSeed e chi m omega' N hN p hp]
  simp only [coordinateSeed, if_pos hactive, if_pos (hcut.trans hactive)]

theorem rawLevel_cutoff_eq_on_active
    (e chi : ℝ) (m : ℕ) (omega' omega : ℝ) (hcut : omega' ≤ omega)
    (N : ℕ) (hN : 1 < N) (p : Fin 4 → ℕ) (hp : ∀ i, 0 < p i)
    (hactive : omega ≤ actualPrimeTupleLog N p 2) :
    rawLevel e chi m omega (N : ℝ) (history3 p) =
      rawLevel e chi m omega' (N : ℝ) (history3 p) := by
  have hold := P1OriginalVariableFourthContinuation.frozenLevel_eq_rpow_seed
    e chi m omega (N : ℝ) (tupleHistory p)
  have hnew := P1OriginalVariableFourthContinuation.frozenLevel_eq_rpow_seed
    e chi m omega' (N : ℝ) (tupleHistory p)
  change rawLevel e chi m omega (N : ℝ) (rosserAncestor 3 (tupleHistory p)) = _ at hold
  change rawLevel e chi m omega' (N : ℝ) (rosserAncestor 3 (tupleHistory p)) = _ at hnew
  rw [ancestor3_tupleHistory] at hold hnew
  rw [hold, hnew, seedExponent_cutoff_eq_on_active e chi m omega' omega hcut N hN p hp hactive]

theorem producerLevel4_cutoff_eq_on_active
    (e chi : ℝ) (m : ℕ) (omega' omega : ℝ) (hcut : omega' ≤ omega)
    (N : ℕ) (hN : 1 < N) (p : Fin 4 → ℕ) (hp : ∀ i, 0 < p i)
    (hactive : omega ≤ actualPrimeTupleLog N p 2)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) :
    producerLevel4 e chi m omega (N : ℝ) rows licensed (tupleHistory p) =
      producerLevel4 e chi m omega' (N : ℝ) rows licensed (tupleHistory p) := by
  have hs := seedExponent_cutoff_eq_on_active e chi m omega' omega hcut N hN p hp hactive
  simp only [producerLevel4, level4, exponent4, hs]

/-- Both ACTUAL densities have identical carrier, cutoff and physical
levels after this restriction; their equality is not a mean estimate. -/
theorem literalResidual_cutoff_eq_on_active
    (e chi : ℝ) (m : ℕ) (omega' omega : ℝ) (hcut : omega' ≤ omega)
    (N cap : ℕ) (hN : 1 < N) (p : Fin 4 → ℕ) (hp : ∀ i, 0 < p i)
    (hactive : omega ≤ actualPrimeTupleLog N p 2)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop) :
    literalTupleResidualDifference (rawLevel e chi m omega (N : ℝ))
        (producerLevel4 e chi m omega (N : ℝ) rows licensed) N cap p =
      literalTupleResidualDifference (rawLevel e chi m omega' (N : ℝ))
        (producerLevel4 e chi m omega' (N : ℝ) rows licensed) N cap p := by
  unfold literalTupleResidualDifference
  rw [ancestor3_tupleHistory,
    rawLevel_cutoff_eq_on_active e chi m omega' omega hcut N hN p hp hactive,
    producerLevel4_cutoff_eq_on_active e chi m omega' omega hcut N hN p hp hactive rows licensed]

/-- The actual original admission at the two cutoffs agrees on an active
tuple: the same original first-stop and three cube inequalities survive. -/
theorem admitted_cutoff_iff_on_active
    (e chi : ℝ) (m : ℕ) (omega' omega : ℝ) (hcut : omega' ≤ omega)
    (N cap : ℕ) (hN : 1 < N) (p : Fin 4 → ℕ) (hp : ∀ i, 0 < p i)
    (hs : StrictAnti p) (hactive : omega ≤ actualPrimeTupleLog N p 2) :
    p ∈ firstExitAdmittedTuples 4 (policy e chi m omega (N : ℝ))
        (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ))) ↔
      p ∈ firstExitAdmittedTuples 4 (policy e chi m omega' (N : ℝ))
        (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ))) := by
  rw [mem_firstExitAdmittedTuples_iff, mem_firstExitAdmittedTuples_iff]
  apply and_congr_right
  intro _hsub
  rw [valid_fourth_iff e chi m omega (N : ℝ) p hp hs,
    valid_fourth_iff e chi m omega' (N : ℝ) p hp hs,
    rawLevel_cutoff_eq_on_active e chi m omega' omega hcut N hN p hp hactive]

end
end ImbalancedChen.P1OriginalVariableFourthActiveMeshCover
