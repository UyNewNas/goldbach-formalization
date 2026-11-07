import ImbalancedChen.P5ArbitraryMaskChildVertexRatio
import ImbalancedChen.P5ChildSelectedOwnerJensenReserve

/-!
SOURCE_ONLY / UNCOMPILED_ZERO_CREDIT.
An original integer child row is consumed through explicit finite rational
checks: SAME d, actual chosen-plane vertex inequalities, actual e-domain,
and equality of original expanded floor with directed rational rounding.
No desired real integral/mean/density is an input. This receiver is for
arbitrary original rows and arbitrary original fifth masks.
-/
namespace ImbalancedChen.P5OriginalGenericWireFloorReceiver
open scoped BigOperators
open P1OriginalPrefixRowDecodeSoundness P1OriginalFifthRawBoxSelectorEquivalence
open P5OriginalChildIntegerWireBinding P5ArbitraryMaskChildVertexRatio
open P5NamedFifthPayloadSemantics P5NamedFifthQ80FloorSoundness
open P5OldFifthExact64ChildTiling P5OldFifthOneCoordinateVertexChord
open P5OldFifthChildGapIntegral P5OldFifthPointwiseQ
open P5OldFifthActualChildJensenIntegral P5OldFifthFrozenUpperSurrogate
open P5ChildSelectedOwnerJensenReserve
open ImbalancedChen.Certificates.P2DirectedLogRounding

def rowD (raw : FifthWireRow) (c : ChildIndex) : ℤ := (originalFields raw c).d

def rowEQ (raw : FifthWireRow) (c : ChildIndex) : ℚ :=
  (rowD raw c : ℚ) / (1024 * ((originalFields raw c).hi 4 : ℚ))

def rowPrefactorQ (raw : FifthWireRow) (c : ChildIndex) : ℚ :=
  (4 * 1600 * ∏ i : Fin 5, (width i : ℚ)) /
    ((childRightNumer raw c 4 : ℚ) * ∏ i : Fin 5, (childRightNumer raw c i : ℚ))

def rowFloorQ (raw : FifthWireRow) (c : ChildIndex) : ℚ :=
  (originalExactFloor (originalFields raw c) : ℚ) / dyadicScale 80

/-- Executable rational input obligations, not an assumed target gain.
Negative-d children require neither an artificial b>2 nor an e-range. -/
def SourceChildFacts (raw : FifthWireRow) (c : ChildIndex) : Prop :=
  (∀ i : Fin 5, raw.upper i ≤ 19 / 96) ∧
  (rowD raw c : ℚ) = childDQ raw c ∧
  (0 < rowD raw c →
    2 < originalRatioQ raw c ∧ originalRatioQ raw c ≤ 4 ∧
    0 ≤ rowEQ raw c ∧ rowEQ raw c ≤ originalRatioQ raw c - 2 ∧
    0 ≤ rowPrefactorQ raw c ∧
    (∀ w : Word, vertexRatioQ raw (originalChosenSide raw c)
      (childVertexQ raw c (wordChoice w)) ≤ originalRatioQ raw c) ∧
    originalExactFloor (originalFields raw c) =
      Int.floor (rowPrefactorQ raw c * directedQQ (originalRatioQ raw c) (rowEQ raw c) *
        dyadicScale 80))

instance (raw : FifthWireRow) (c : ChildIndex) : Decidable (SourceChildFacts raw c) := by
  unfold SourceChildFacts
  infer_instance

/-- Real same-child numerators, independent of named rows. -/
theorem original_hi_eq_actual (raw : FifthWireRow) (c : ChildIndex) (i : Fin 5) :
    (originalFields raw c).hi i = childRightNumer raw c i := by
  have hw : wireWidth i = (width i : ℤ) := by fin_cases i <;> decide
  simp [originalFields, wireHi, wireLo, childRightNumer, childLeftNumer, hw]

noncomputable section
open Set MeasureTheory
open scoped Classical

theorem rowEQ_eq_actual_scale (raw : FifthWireRow) (c : ChildIndex) :
    (rowEQ raw c : ℝ) = (rowD raw c : ℝ) /
      (1024 * 1600 * childRight raw c 4) := by
  simp [rowEQ, original_hi_eq_actual, childRight]
  ring

theorem rowD_eq_actual_vertexD (raw : FifthWireRow) (c : ChildIndex)
    (hf : SourceChildFacts raw c) :
    (rowD raw c : ℝ) = vertexD (sourcePicks raw) raw c := by
  have hr : (rowD raw c : ℝ) = (childDQ raw c : ℝ) := by exact_mod_cast hf.2.1
  exact hr.trans (cast_childDQ raw c)

theorem rowPrefactorQ_cast (raw : FifthWireRow) (c : ChildIndex)
    (hleft : ∀ i, 0 < childLeft raw c i) :
    (rowPrefactorQ raw c : ℝ) = childVolume raw c * childPrefactor raw c := by
  symm
  simpa [rowPrefactorQ] using child_volume_mul_prefactor_integerScale raw c hleft

/-- Original signed d and expanded integer floor are bound to the actual
whole-child kernel. No numeric integral lower bound has been assumed. -/
theorem original_wire_floor_le_actual_child
    (raw : FifthWireRow) (c : ChildIndex)
    (hpositive : ∀ i : Fin 5, 1 ≤ raw.lo i)
    (hf : SourceChildFacts raw c) :
    (rowFloorQ raw c : ℝ) ≤
      ∫ t in childBox raw c, frozenUpperPositiveKernel (sourcePicks raw) raw t := by
  have hleft := positiveKey_childLeft_pos raw hpositive c
  by_cases hd : 0 < rowD raw c
  · obtain ⟨hb2, hb4, he0, heB, hpref, hvertex, hfloor⟩ := hf.2.2 hd
    have hnew := actual_child_ratio_of_rational_vertices raw c hleft
      (originalChosenSide raw c) (originalRatioQ raw c) hvertex
    have hround : rowFloorQ raw c ≤
        rowPrefactorQ raw c * directedQQ (originalRatioQ raw c) (rowEQ raw c) := by
      simpa [rowFloorQ, hfloor, roundDown] using roundDown_le 80
        (rowPrefactorQ raw c * directedQQ (originalRatioQ raw c) (rowEQ raw c))
    have hr : (rowFloorQ raw c : ℝ) ≤
        (rowPrefactorQ raw c : ℝ) * (directedQQ (originalRatioQ raw c) (rowEQ raw c) : ℝ) := by
      exact_mod_cast hround
    have hlog := directedQQ_le_Q (originalRatioQ raw c) (rowEQ raw c) hb2 he0 heB
    have hprefR : (0 : ℝ) ≤ (rowPrefactorQ raw c : ℝ) := by exact_mod_cast hpref
    have hJ := integral_frozenUpperPositiveKernel_ge_child_Jensen
      (sourcePicks raw) raw c hleft (by exact_mod_cast hb2) (by exact_mod_cast hb4)
      hnew (rowD raw c) hd.le (rowD_eq_actual_vertexD raw c hf)
    have hlower : (rowFloorQ raw c : ℝ) ≤ childVolume raw c * childPrefactor raw c *
        Q (originalRatioQ raw c) ((rowD raw c : ℝ) / (1024 * 1600 * childRight raw c 4)) := by
      have hh := hr.trans (mul_le_mul_of_nonneg_left hlog hprefR)
      simpa only [rowPrefactorQ_cast raw c hleft, rowEQ_eq_actual_scale] using hh
    exact hlower.trans hJ
  · have hdn : (originalFields raw c).d ≤ 0 := le_of_not_gt hd
    have hzero : rowFloorQ raw c = 0 := by
      simp [rowFloorQ, originalExactFloor, hdn]
    rw [hzero, Rat.cast_zero]
    exact integral_nonneg (fun _ => frozenUpperPositiveKernel_nonneg (sourcePicks raw) raw _)

/-- The original fullCell clipping is paid by the SAME actual reserve.
No mask5/6 history or selected/fifth gate is erased at this stage. -/
theorem original_wire_floor_sub_reserve_le_clipped
    (raw : FifthWireRow) (hgrid : raw.grid = 400)
    (hpositive : ∀ i : Fin 5, 1 ≤ raw.lo i)
    (c : ChildIndex) (hf : SourceChildFacts raw c)
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) (J5 : Finset (Owner m)) :
    (rowFloorQ raw c : ℝ) - childOwnerReserve raw c e chi m omega J5 ≤
      ∑ j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5,
        ∫ t in childOwnerDomain raw c e chi m omega j, literalPositiveRawKernel e raw t := by
  have hupper : ∀ i : Fin 5, (raw.upper i : ℝ) ≤ (19 / 96 : ℝ) := by
    intro i
    exact_mod_cast hf.1 i
  have hh := whole_child_sub_reserve_le_retained_positive (sourcePicks raw) raw hgrid
    hpositive hupper c e chi m omega J5
  rw [retained_positive_integral_eq_sum_child_owners raw hgrid hpositive c e chi m omega J5] at hh
  exact (sub_le_sub_right (original_wire_floor_le_actual_child raw c hpositive hf) _).trans hh

/-- Per-original-parent COMPLETE64 sum, with its original fields and
same actual selected-owner domain; no duplicated128-child gain. -/
theorem original_parent64_wire_floor_sub_reserve
    (raw : FifthWireRow) (hgrid : raw.grid = 400)
    (hpositive : ∀ i : Fin 5, 1 ≤ raw.lo i)
    (hf : ∀ c : ChildIndex, SourceChildFacts raw c)
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) (J5 : Finset (Owner m)) :
    (∑ c : ChildIndex, (rowFloorQ raw c : ℝ)) -
        (∑ c : ChildIndex, childOwnerReserve raw c e chi m omega J5) ≤
      ∑ j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5,
        literalPositiveRawOwnerIntegral raw e chi m omega j := by
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset ChildIndex))
    (fun c _ => original_wire_floor_sub_reserve_le_clipped raw hgrid hpositive c (hf c)
      e chi m omega J5)
  rw [Finset.sum_comm] at hs
  have heq : (∑ j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5,
      ∑ c : ChildIndex, ∫ t in childOwnerDomain raw c e chi m omega j,
        literalPositiveRawKernel e raw t) =
      ∑ j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5,
        literalPositiveRawOwnerIntegral raw e chi m omega j := by
    apply Finset.sum_congr rfl
    intro j _
    exact (positive_rawOwnerIntegral_eq_sum_64_children raw hgrid hpositive e chi m omega j).symm
  rw [heq] at hs
  simpa only [Finset.sum_sub_distrib] using hs

end
end ImbalancedChen.P5OriginalGenericWireFloorReceiver
