import ImbalancedChen.OriginalFifthInheritedParentGeometry
import ImbalancedChen.P1ActualVariableFifthUntruncatedDomination

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT.

Signed integral accounting on the actual fifth source, with the inherited
fourth maximum replaced on each piece by its genuine positional owner.
Every parent position, including the raw-Q3 seed fallback, appears with
coefficient one. Old and new own-cube tests keep their own exact gates.
Neither positivity nor deletion of an open inherit/equality region is used
in the partition identity. The cutoff and full-domain instances consume
the existing actual-kernel integrability proofs, not an assumed saving.
-/

namespace ImbalancedChen.OriginalFifthParentSignedSaving20261026b

noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
open P2OriginalFourthCapProducerInterface
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalFullTableActualProducerAdapter
open P1OriginalVariableFifthContinuation
open P1ActualVariableFifthProfiles
open P1CorrectedFifthDensityDictionary
open P1ActualVariableFourthFifthCellTestLimit
open P1ActualVariableFifthPositiveCellLimit
open OriginalFifthInheritedParentGeometry20261026b

abbrev Point5 := Fin 5 → ℝ
abbrev Label5 (m : ℕ) := Fin 5 → Fin (m + 1)

theorem indicator_eq_sum_parent (records : List FourthWireRow) (e : ℚ)
    (m : ℕ) (j : Label5 m) (licensed : ProducerRow → Prop)
    (R : Set Point5) (f : Point5 → ℝ) (t : Point5) :
    R.indicator f t =
      ∑ i : OriginalFullFourthPriorityOwnership20261026a.BankPosition records,
        (parentRegion records e m j licensed R i).indicator f t := by
  symm
  rw [Finset.sum_eq_single (parentOwner records e m j licensed t)]
  · by_cases ht : t ∈ R
    · rw [indicator_of_mem ht, indicator_of_mem
        (show t ∈ parentRegion records e m j licensed R
          (parentOwner records e m j licensed t) from ⟨ht, rfl⟩)]
    · rw [indicator_of_notMem ht, indicator_of_notMem
        (show t ∉ parentRegion records e m j licensed R
          (parentOwner records e m j licensed t) from fun h => ht h.1)]
  · intro i _hi hine
    apply indicator_of_notMem
    intro ht
    exact hine ht.2.symm
  · simp

/-- The range R is complete. No parent is removed when its signed charge
is negative or when the fourth maximum equals its original seed. -/
theorem signed_integral_eq_parent_integrals (records : List FourthWireRow) (e : ℚ)
    (m : ℕ) (j : Label5 m) (licensed : ProducerRow → Prop)
    (R : Set Point5) (hR : MeasurableSet R) (f : Point5 → ℝ)
    (hf : IntegrableOn f R) :
    (∫ t in R, f t) =
      ∑ i : OriginalFullFourthPriorityOwnership20261026a.BankPosition records,
        ∫ t in parentRegion records e m j licensed R i, f t := by
  have hi (i : OriginalFullFourthPriorityOwnership20261026a.BankPosition records) :
      Integrable ((parentRegion records e m j licensed R i).indicator f) :=
    (integrable_indicator_iff (measurableSet_parentRegion records e m j licensed R hR i)).mpr
      (hf.mono_set (fun _ ht => ht.1))
  calc
    (∫ t in R, f t) = (∫ t, R.indicator f t) := (integral_indicator hR).symm
    _ = ∫ t, ∑ i : OriginalFullFourthPriorityOwnership20261026a.BankPosition records,
        (parentRegion records e m j licensed R i).indicator f t := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (indicator_eq_sum_parent records e m j licensed R f)
    _ = ∑ i : OriginalFullFourthPriorityOwnership20261026a.BankPosition records,
        ∫ t, (parentRegion records e m j licensed R i).indicator f t :=
      integral_finset_sum _ (fun i _ => hi i)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact integral_indicator (measurableSet_parentRegion records e m j licensed R hR i)

/-- This is a new-minus-ACTUAL-parent density, with each own-cube gate
inside its canonical profile. It is not a derivative estimate. -/
def parentSavingKernel (records4 : List FourthWireRow) (records5 : List FifthWireRow)
    (e : ℚ) (m : ℕ) (j : Label5 m)
    (i : OriginalFullFourthPriorityOwnership20261026a.BankPosition records4)
    (t : Point5) : ℝ :=
  (primeOwnCubeGatedProfile (nextFromParent records4 records5 e m j i t) t -
    primeOwnCubeGatedProfile (parentValue records4 e m j i t) t) * ∏ k, 1 / t k

theorem actualKernel_eq_parentSavingKernel
    (records4 : List FourthWireRow) (records5 : List FifthWireRow)
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J5 : Finset (Label5 m)) (j : Label5 m)
    (hj : j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5)
    (licensed : ProducerRow → Prop) (t : Point5)
    (ht : t ∈ logPrimeMeshCell 0 (19 / 96) m j)
    (i : OriginalFullFourthPriorityOwnership20261026a.BankPosition records4)
    (hi : parentOwner records4 e m j licensed t = i) :
    variableCellKernel e chi m omega j (fourthFamily records4) licensed
        (fifthFamily records5 m) t =
      parentSavingKernel records4 records5 e m j i t := by
  unfold variableCellKernel gatedDifference actualNewTest actualOldTest parentSavingKernel
  rw [actualOld4_eq_parentValue records4 e chi m omega J5 j hj licensed t ht i hi,
    actualNext5_eq_nextFromParent records4 records5 e chi m omega J5 j hj licensed t ht i hi]

theorem actual_integral_eq_parent_savings
    (records4 : List FourthWireRow) (records5 : List FifthWireRow)
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J5 : Finset (Label5 m)) (j : Label5 m)
    (hj : j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5)
    (licensed : ProducerRow → Prop) (R : Set Point5) (hR : MeasurableSet R)
    (hmesh : R ⊆ logPrimeMeshCell 0 (19 / 96) m j)
    (hf : IntegrableOn (variableCellKernel e chi m omega j (fourthFamily records4)
      licensed (fifthFamily records5 m)) R) :
    (∫ t in R, variableCellKernel e chi m omega j (fourthFamily records4) licensed
      (fifthFamily records5 m) t) =
      ∑ i : OriginalFullFourthPriorityOwnership20261026a.BankPosition records4,
        ∫ t in parentRegion records4 e m j licensed R i,
          parentSavingKernel records4 records5 e m j i t := by
  rw [signed_integral_eq_parent_integrals records4 e m j licensed R hR _ hf]
  apply Finset.sum_congr rfl
  intro i _hi
  apply setIntegral_congr_fun (measurableSet_parentRegion records4 e m j licensed R hR i)
  intro t ht
  exact actualKernel_eq_parentSavingKernel records4 records5 e chi m omega J5 j hj
    licensed t (hmesh ht.1) i ht.2

/-- Complete positive-cutoff saving theorem. The only inputs are the
literal records, original selected cell, positive cutoff, and external
fourth row licenses. The actual analytic integrability is supplied. -/
theorem actual_cutoff_saving_eq_parent_savings
    (records4 : List FourthWireRow) (records5 : List FifthWireRow)
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ) (ha : 0 < a)
    (J5 : Finset (Label5 m)) (j : Label5 m)
    (hj : j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5)
    (licensed : ProducerRow → Prop) :
    variableCellIntegral e chi m omega a j (fourthFamily records4) licensed
        (fifthFamily records5 m) =
      ∑ i : OriginalFullFourthPriorityOwnership20261026a.BankPosition records4,
        ∫ t in parentRegion records4 e m j licensed
          (P1OriginalFifthIntegral.truncatedCell e chi m omega a j) i,
          parentSavingKernel records4 records5 e m j i t := by
  exact actual_integral_eq_parent_savings records4 records5 e chi m omega J5 j hj licensed
    _ (P1OriginalFifthIntegral.truncatedCell_measurable e chi m omega a j)
    (fun _ ht => ht.2.1)
    (integrableOn_actualVariable5_kernel e chi m omega a ha J5 j hj
      (fourthFamily records4) licensed (fifthFamily records5 m))

/-- The same exact accounting also holds on the full source. The genuine
actual-kernel majorant/exhaustion theorem supplies integrability. -/
theorem actual_full_saving_eq_parent_savings
    (records4 : List FourthWireRow) (records5 : List FifthWireRow)
    (e : ℚ) (he : 0 ≤ e) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (J5 : Finset (Label5 m)) (j : Label5 m)
    (hj : j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5)
    (licensed : ProducerRow → Prop) :
    P1ActualVariableFifthUntruncatedDomination.fullCellIntegral e chi m omega
        (fourthFamily records4) licensed (fifthFamily records5 m) j =
      ∑ i : OriginalFullFourthPriorityOwnership20261026a.BankPosition records4,
        ∫ t in parentRegion records4 e m j licensed
          (P1OriginalFifthUntruncatedIntegral.fullCell e chi m omega j) i,
          parentSavingKernel records4 records5 e m j i t := by
  exact actual_integral_eq_parent_savings records4 records5 e chi m omega J5 j hj licensed
    _ (P1OriginalFifthUntruncatedIntegral.fullCell_measurable e chi m omega j)
    (fun _ ht => ht.2.2.1)
    (P1ActualVariableFifthUntruncatedDomination.integrableOn_actualKernel_fullCell
      e he chi m omega homega homegaRho J5 j hj (fourthFamily records4) licensed
      (fifthFamily records5 m))

end
end ImbalancedChen.OriginalFifthParentSignedSaving20261026b
