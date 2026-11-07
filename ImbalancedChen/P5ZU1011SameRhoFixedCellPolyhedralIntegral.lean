import ImbalancedChen.P5ZU1011SameRhoDensityErrorZero
import ImbalancedChen.P5ZU1011OriginalSixteenMixedGatePrimeTests

/-!
# The actual fixed-cell ordinary-F kernel has polyhedral primebox integrals

SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The static selected policy, its actual near-cap parameters, mesh and eta
precede N. The kernel is the finite Ico sum of the genuine Suzuki ordinary
density limits, with zero on the actual tag0 cells. Every Ico face is
retained by its literal weak-lower/strict-upper affine gate. Direct mixed-
gate PNT and finite weighted integral gluing supply the regional limit.
No hMean, boundary-nullity or cell convergence premise occurs.
-/

namespace ImbalancedChen.P5Z.U1011SameRhoFixedCellPolyhedralIntegral

noncomputable section

open Set MeasureTheory Classical Filter Topology
open scoped BigOperators
open U11Integral
open U1011OriginalSixteenEligibilityState U1011OriginalSixteenMixedGatePrimeTests
open U1011OriginalFifteenNativeGridCells
open U1011OriginalSixteenStaticNativeCompiler (boxPolicy tupleTag ownerBox)
open U1011SameRhoNativePrimeBoxDensity U1011SameRhoDensityErrorZero
open U1011OriginalSixteenArithmeticProducts

def cellValue (n : ℕ) (eta : ℚ) (j : Grid n) : ℝ :=
  if U1011OriginalSixteenStaticCellWinner.chosenTag (gridBox n j) = 0 then 0
  else ordinaryLimit (boxPolicy (gridBox n j)) (gridBox n j) eta

def ordinaryStep (n : ℕ) (eta : ℚ) (v : LogFour) : ℝ :=
  ∑ j : Grid n, (cell n j).indicator (fun _ => cellValue n eta j) v

def logWeight (v : LogFour) : ℝ := ∏ i, 1 / v i

theorem cube_eq_literal : cube = logPrimeBox (fun _ : Fin 4 => (417 / 5000 : ℝ))
    (fun _ => (59 / 250 : ℝ)) := by norm_num [cube, lower, upper]

def regionalMass {ι : Type*} (g : ι → MixedGate) (n : ℕ) (eta : ℚ) (N : ℕ) : ℝ :=
  actualPrimeBoxTestSum N (fun _ : Fin 4 => (417 / 5000 : ℝ)) (fun _ => (59 / 250 : ℝ))
    ((mixedRegion g).indicator (ordinaryStep n eta))

def regionalIntegral {ι : Type*} (g : ι → MixedGate) (n : ℕ) (eta : ℚ) : ℝ :=
  ∫ v in cube ∩ mixedRegion g, ordinaryStep n eta v * logWeight v

def cellGates (n : ℕ) (j : Grid n) : Fin 4 × Bool → MixedGate
  | (i, false) => ⟨-ContinuousLinearMap.proj i,
      -logPrimeMeshLo (lower : ℝ) (upper : ℝ) n j i, false⟩
  | (i, true) => ⟨ContinuousLinearMap.proj i,
      logPrimeMeshHi (lower : ℝ) (upper : ℝ) n j i, true⟩

theorem cell_eq_mixed (n : ℕ) (j : Grid n) : cell n j = mixedRegion (cellGates n j) := by
  ext v
  rw [cell, mem_logPrimeMeshCell]
  constructor
  · intro h k
    rcases k with ⟨i, b⟩
    cases b
    · simpa only [cellGates, MixedGate.Holds, Bool.false_eq_true, if_false,
        ContinuousLinearMap.neg_apply, ContinuousLinearMap.proj_apply, neg_le_neg_iff] using (h i).1
    · simpa only [cellGates, MixedGate.Holds, if_true, ContinuousLinearMap.proj_apply] using (h i).2
  · intro h i
    constructor
    · simpa only [cellGates, MixedGate.Holds, Bool.false_eq_true, if_false,
        ContinuousLinearMap.neg_apply, ContinuousLinearMap.proj_apply, neg_le_neg_iff] using h (i, false)
    · simpa only [cellGates, MixedGate.Holds, if_true, ContinuousLinearMap.proj_apply] using h (i, true)

theorem measurableSet_cell (n : ℕ) (j : Grid n) : MeasurableSet (cell n j) := by
  rw [cell_eq_mixed]
  exact measurableSet_mixedRegion _

def cutGates {ι : Type*} (g : ι → MixedGate) (n : ℕ) (j : Grid n) :
    ι ⊕ (Fin 4 × Bool) → MixedGate
  | .inl i => g i
  | .inr k => cellGates n j k

theorem cut_eq_mixed {ι : Type*} (g : ι → MixedGate) (n : ℕ) (j : Grid n) :
    mixedRegion g ∩ cell n j = mixedRegion (cutGates g n j) := by
  rw [cell_eq_mixed]
  ext v
  constructor
  · rintro ⟨hg, hc⟩ k
    cases k with
    | inl i => exact hg i
    | inr k => exact hc k
  · intro h
    exact ⟨fun i => h (.inl i), fun k => h (.inr k)⟩

theorem ordinaryStep_eq_owner (n : ℕ) (eta : ℚ) {v : LogFour} (hv : v ∈ cube) :
    ordinaryStep n eta v = cellValue n eta (owner n v) := by
  unfold ordinaryStep
  rw [Finset.sum_eq_single (owner n v)]
  · exact indicator_of_mem (owner_mem n hv) _
  · intro j hj hne
    exact indicator_of_notMem (fun hjv => hne (owner_eq_of_mem n hjv).symm) _
  · intro hnot
    exact (hnot (Finset.mem_univ _)).elim

theorem ordinaryStep_at_native_tuple {n N : ℕ} (eta : ℚ) (hN : 1 < N)
    {E : ℕ × ℕ → Prop} {t : Four} (ht : t ∈ P5U1011JointOverlap.jointSelector N E) :
    ordinaryStep n eta (coordinates N t) = if tupleTag n N t = 0 then 0
      else ownerLimit n eta (coordinates N t) := by
  rw [ordinaryStep_eq_owner n eta (U1011OriginalFifteenJointNativeRows.joint_coordinates_cube hN ht)]
  rfl

/-- The original full natural phi weights and both source bands are
unchanged. The finite fixed-cell test is exactly the selected native mass. -/
theorem ordinaryNativeMass_eq_nativeJoint_step {n N : ℕ} (eta : ℚ) (hN : 1 < N)
    (E : ℕ × ℕ → Prop) : ordinaryNativeMass n N eta E =
      U1011OriginalJointHarmonic.nativeJoint N E (ordinaryStep n eta) := by
  unfold ordinaryNativeMass JointNearCapPrimeReserve.jointMass U1011OriginalJointHarmonic.nativeJoint
  apply Finset.sum_congr rfl
  intro t ht
  rw [ordinaryStep_at_native_tuple eta hN ht]
  by_cases hz : tupleTag n N t = 0 <;> simp only [ordinaryKeep, hz, not_true_eq_false,
    not_false_eq_true, if_false, if_true, zero_div]

theorem indicator_step_split (D : Set LogFour) (n : ℕ) (eta : ℚ) (v : LogFour) :
    D.indicator (ordinaryStep n eta) v =
      ∑ j : Grid n, (D ∩ cell n j).indicator (fun _ => cellValue n eta j) v := by
  by_cases hd : v ∈ D
  · rw [indicator_of_mem hd]
    unfold ordinaryStep
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hc : v ∈ cell n j <;> simp [hd, hc]
  · rw [indicator_of_notMem hd]
    symm
    apply Finset.sum_eq_zero
    intro j hj
    exact indicator_of_notMem (fun h => hd h.1) _

private theorem weighted_cell_eq (n : ℕ) (eta : ℚ) (j : Grid n) :
    (fun v => (cell n j).indicator (fun _ => cellValue n eta j) v * logWeight v) =
      (cell n j).indicator (fun v => cellValue n eta j * logWeight v) := by
  funext v
  by_cases hv : v ∈ cell n j <;> simp [hv]

theorem integrableOn_weighted_cell (n : ℕ) (eta : ℚ) (j : Grid n) :
    IntegrableOn (fun v => (cell n j).indicator (fun _ => cellValue n eta j) v * logWeight v) cube := by
  rw [weighted_cell_eq, cube_eq_literal]
  exact (integrableOn_logPrimeBox_test_cube (by norm_num : (0 : ℝ) < 417 / 5000)
    (fun _ : LogFour => cellValue n eta j) continuousOn_const).indicator (measurableSet_cell n j)

theorem integrableOn_weighted_step (n : ℕ) (eta : ℚ) :
    IntegrableOn (fun v => ordinaryStep n eta v * logWeight v) cube := by
  have hi := integrable_finsetSum (Finset.univ : Finset (Grid n))
    (fun j _ => integrableOn_weighted_cell n eta j)
  simpa only [ordinaryStep, Finset.sum_mul] using hi

theorem regionalMass_eq_cell_sum {ι : Type*} (g : ι → MixedGate)
    (n N : ℕ) (eta : ℚ) : regionalMass g n eta N =
      ∑ j : Grid n, actualPrimeBoxTestSum N (fun _ : Fin 4 => (417 / 5000 : ℝ))
        (fun _ => (59 / 250 : ℝ))
        ((mixedRegion g ∩ cell n j).indicator (fun _ => cellValue n eta j)) := by
  unfold regionalMass actualPrimeBoxTestSum
  simp_rw [indicator_step_split, Finset.mul_sum]
  exact Finset.sum_comm

theorem regionalIntegral_eq_cell_sum {ι : Type*} [Fintype ι] (g : ι → MixedGate)
    (n : ℕ) (eta : ℚ) : regionalIntegral g n eta =
      ∑ j : Grid n, ∫ v in cube ∩ (mixedRegion g ∩ cell n j), cellValue n eta j * logWeight v := by
  unfold regionalIntegral
  calc
    _ = ∫ v in cube ∩ mixedRegion g,
        ∑ j : Grid n, (cell n j).indicator (fun _ => cellValue n eta j) v * logWeight v := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun v => by simp only [ordinaryStep, Finset.sum_mul])
    _ = ∑ j : Grid n, ∫ v in cube ∩ mixedRegion g,
        (cell n j).indicator (fun _ => cellValue n eta j) v * logWeight v :=
      integral_finsetSum _ (fun j _ => (integrableOn_weighted_cell n eta j).mono_set inter_subset_left)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [weighted_cell_eq, setIntegral_indicator (measurableSet_cell n j), inter_assoc]

/-- Direct finite-polyhedral integral limit of the ACTUAL ordinary-F
cell values. Arbitrary moving E is deliberately absent from this theorem. -/
theorem tendsto_regional_ordinaryStep {ι : Type*} [Fintype ι] (g : ι → MixedGate)
    (n : ℕ) (eta : ℚ) : Tendsto (regionalMass g n eta) atTop (𝓝 (regionalIntegral g n eta)) := by
  have hc (j : Grid n) : Tendsto (fun N : ℕ => actualPrimeBoxTestSum N
      (fun _ : Fin 4 => (417 / 5000 : ℝ)) (fun _ => (59 / 250 : ℝ))
      ((mixedRegion g ∩ cell n j).indicator (fun _ => cellValue n eta j))) atTop
      (𝓝 (∫ v in cube ∩ (mixedRegion g ∩ cell n j), cellValue n eta j * logWeight v)) := by
    have ht := tendsto_actualPrimeBox_mixedRegion (cutGates g n j)
      (fun _ : LogFour => cellValue n eta j) continuousOn_const
    simpa only [← cut_eq_mixed, cube_eq_literal, logWeight] using ht
  rw [regionalIntegral_eq_cell_sum]
  have ht := tendsto_finsetSum (Finset.univ : Finset (Grid n)) (fun j _ => hc j)
  exact ht.congr' (Eventually.of_forall (fun N => (regionalMass_eq_cell_sum g n N eta).symm))

end

end ImbalancedChen.P5Z.U1011SameRhoFixedCellPolyhedralIntegral
