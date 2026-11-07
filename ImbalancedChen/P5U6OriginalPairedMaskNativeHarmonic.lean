import ImbalancedChen.P5U6AdoptedEnhancedHarmonic
import ImbalancedChen.P5ZU1011OriginalPairedFixedMaskHarmonic

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
Concrete binding of the actual adopted17572 paired-v2 outer rows to the
corrected ORIGINAL Runbo U6 native harmonic supplier. The original row
coordinates(t,u) are transposed to native U6 coordinates(u,t). Every row
keeps its lower-inclusive and upper-exclusive walls and unique ownership.
The correction is4*h/R, R=1/2-u-t, never the auxiliary a-denominator model.
This is a harmonic estimator theorem, not a causal count or table license.
-/
namespace ImbalancedChen.P5U6OriginalPairedMaskNativeHarmonicSourceOnly

noncomputable section

open Set MeasureTheory Filter Topology
open Classical
open scoped BigOperators
open P5U6AdoptedEnhancedHarmonicSourceOnly P5U6RetainedAdoptedIntegralSourceOnly
open P5U6SteppedPrimeAdmissibilitySourceOnly P5U6AdoptedH248BindingSourceOnly
open P5Z.U1011OriginalPairedRowPrimeTests
open P5Z.U1011OriginalPairedFixedMaskHarmonic (outerUnion outerUnion_all)
open Certificates.PairedV2

abbrev U6Point := Fin 2 → ℝ
abbrev RowIndex (S : Finset Row) := {r : Row // r ∈ S}

def rowAt (S : Finset Row) (j : Fin (Fintype.card (RowIndex S))) : Row :=
  ((Fintype.equivFin (RowIndex S)).symm j).val

def rowLo (r : Row) : U6Point :=
  ![(uLower (FullMask.indices r).2 : ℝ), (tLower (FullMask.indices r).1 : ℝ)]
def rowHi (r : Row) : U6Point :=
  ![(uUpper (FullMask.indices r).2 : ℝ), (tUpper (FullMask.indices r).1 : ℝ)]
def lows (S : Finset Row) (j : Fin (Fintype.card (RowIndex S))) : U6Point := rowLo (rowAt S j)
def highs (S : Finset Row) (j : Fin (Fintype.card (RowIndex S))) : U6Point := rowHi (rowAt S j)

theorem rowBox_dictionary (r : Row) (x : U6Point) :
    x ∈ box (rowLo r) (rowHi r) ↔ (x 1, x 0) ∈ FullMask.P1E0E1.pairCell r := by
  simp only [box, rowLo, rowHi, FullMask.P1E0E1.pairCell, mem_setOf_eq,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  tauto

/-- Disjointness is supplied by the original17572 row owner theorem. -/
theorem actual_rowBoxes_disjoint (S : Finset Row) :
    Pairwise (fun i j => Disjoint (box (lows S i) (highs S i))
      (box (lows S j) (highs S j))) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hi hj
  have hr : rowAt S i = rowAt S j := FullMask.P1E0E1.pairCell_unique_owner
    ((rowBox_dictionary (rowAt S i) x).1 hi) ((rowBox_dictionary (rowAt S j) x).1 hj)
  have hindex : (Fintype.equivFin (RowIndex S)).symm i =
      (Fintype.equivFin (RowIndex S)).symm j := Subtype.ext hr
  exact hij ((Fintype.equivFin (RowIndex S)).symm.injective hindex)

def ascendingPointMask (S : Finset Row) : Set U6Point :=
  {x | (x 1, x 0) ∈ outerUnion S}

/-- Exact finite family identification, not a numerical coverage check. -/
theorem actual_boxMask_eq (S : Finset Row) :
    boxMask (lows S) (highs S) = ascendingPointMask S := by
  ext x
  constructor
  · intro hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    have hpair := (rowBox_dictionary (rowAt S j) x).1 hj
    exact mem_iUnion.mpr ⟨rowAt S j, mem_iUnion.mpr
      ⟨((Fintype.equivFin (RowIndex S)).symm j).property, hpair⟩⟩
  · intro hx
    obtain ⟨r, hr⟩ := mem_iUnion.mp hx
    obtain ⟨hrS, hrx⟩ := mem_iUnion.mp hr
    let j := (Fintype.equivFin (RowIndex S)) ⟨r, hrS⟩
    have hj : rowAt S j = r := by simp only [rowAt, j, Equiv.symm_apply_apply]
    apply mem_iUnion.mpr
    refine ⟨j, ?_⟩
    change x ∈ box (rowLo (rowAt S j)) (rowHi (rowAt S j))
    rw [hj]
    exact (rowBox_dictionary r x).2 hrx

def enhancedFactor (x : U6Point) : ℝ := currentChenUpsilon6OrdinaryClippedTest x +
  adoptedH248Floor (currentChenUpsilon6OrdinaryProfile x) * bareCorrection x

theorem correction_original_R (x : U6Point) : bareCorrection x =
    4 / ((1 / 2 : ℝ) - x 0 - x 1) := rfl

/-- The actual native numerator has precisely the ORIGINAL R-weighted
enhancement after the two prime harmonic reciprocals are attached. -/
theorem enhancedFactor_density {eta : ℝ} (heta : 0 ≤ eta) {x : U6Point}
    (hx : x ∈ currentChenUpsilon6LogDomain eta) :
    enhancedFactor x * (∏ i, 1 / x i) = adoptedKernel x := by
  rw [enhancedFactor, currentChenUpsilon6OrdinaryClippedTest_eq hx.1]
  unfold currentChenUpsilon6OrdinaryFactor adoptedKernel originalEnhancedKernel
    currentChenUpsilon6OrdinaryKernel originalEnhancement bareCorrection
  simp only [Fin.prod_univ_two, div_eq_mul_inv, mul_inv_rev]
  ring

def nativeU6 (S : Finset Row) (eta : ℝ) (N : ℕ) : ℝ :=
  ∑ p ∈ currentChenUpsilon6OrdinarySelector N eta,
    (if nativeMask (outerUnion S) N p then 0 else
      enhancedFactor (actualPrimeTupleLog N ![p.1, p.2])) /
        (Nat.totient (p.1 * p.2) : ℝ)

theorem nativeMask_u6_dictionary (S : Finset Row) (N : ℕ) (p : ℕ × ℕ) :
    nativeMask (outerUnion S) N p ↔
      actualPrimeTupleLog N ![p.1, p.2] ∈ ascendingPointMask S := Iff.rfl

theorem nativeU6_eq_literal_retained_sum (S : Finset Row) (eta : ℝ) (N : ℕ) :
    nativeU6 S eta N = ∑ p ∈ currentChenUpsilon6OrdinarySelector N eta,
      ({x : U6Point | x ∉ boxMask (lows S) (highs S)}).indicator enhancedFactor
        (actualPrimeTupleLog N ![p.1, p.2]) / (Nat.totient (p.1 * p.2) : ℝ) := by
  unfold nativeU6
  apply Finset.sum_congr rfl
  intro p _
  rw [actual_boxMask_eq]
  by_cases hm : nativeMask (outerUnion S) N p
  · have hx := (nativeMask_u6_dictionary S N p).1 hm
    simp only [if_pos hm, indicator_of_notMem (not_not.mpr hx)]
  · have hx : actualPrimeTupleLog N ![p.1, p.2] ∉ ascendingPointMask S :=
      fun hx => hm ((nativeMask_u6_dictionary S N p).2 hx)
    simp only [if_neg hm, indicator_of_mem hx]

/-- Concrete supplier for the corrected Runbo U6 retained mean with the
SAME actual finite original outer-row deletion mask as U11. Existing true
401-atom prime suppliers, including knots, discharge the mean internally. -/
theorem tendsto_nativeU6 (S : Finset Row) (eta : ℝ) (heta : 0 ≤ eta) :
    Tendsto (nativeU6 S eta) atTop
      (𝓝 (retainedEstimatorIntegral (fun x => x ∈ ascendingPointMask S) eta)) := by
  have ht := tendsto_retained_pair_sum eta heta (lows S) (highs S) (actual_rowBoxes_disjoint S)
  rw [actual_boxMask_eq] at ht
  have heq : nativeU6 S eta = fun N => ∑ p ∈ currentChenUpsilon6OrdinarySelector N eta,
      ({x : U6Point | x ∉ ascendingPointMask S}).indicator enhancedFactor
        (actualPrimeTupleLog N ![p.1, p.2]) / (Nat.totient (p.1 * p.2) : ℝ) := by
    funext N
    rw [nativeU6_eq_literal_retained_sum, actual_boxMask_eq]
  rw [heq]
  exact ht

theorem nativeU6_actual_adopted (eta : ℝ) (N : ℕ) :
    nativeU6 (Finset.univ : Finset Row) eta N =
      ∑ p ∈ currentChenUpsilon6OrdinarySelector N eta,
        (if FullMask.P1E0E1.deletionMask (N : ℝ) p then 0 else
          enhancedFactor (actualPrimeTupleLog N ![p.1, p.2])) /
            (Nat.totient (p.1 * p.2) : ℝ) := by
  simp only [nativeU6, outerUnion_all, nativeMask_actual_adopted]

end
end ImbalancedChen.P5U6OriginalPairedMaskNativeHarmonicSourceOnly
