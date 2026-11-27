import ImbalancedChen.P5OriginalGenericWireFloorReceiver
import ImbalancedChen.P5OriginalWireExpandedFloorAlgebra

/-! Adapt the original integer quotient algebra to the original arbitrary-row
receiver. Only the actual active rational domain and positive source indices
are inputs; no SourceChildFacts, stored floor, Jensen or integral is assumed. -/
namespace ImbalancedChen.P5OriginalWireFloorInstantiation

open scoped BigOperators
open P1OriginalPrefixRowDecodeSoundness
open P5OriginalChildIntegerWireBinding P5OriginalGenericWireFloorReceiver
open P5ArbitraryMaskChildVertexRatio P5NamedFifthQ80FloorSoundness
open P5OldFifthExact64ChildTiling
open ImbalancedChen.Certificates.P2DirectedLogRounding

private theorem hi_pos (raw : FifthWireRow) (c : ChildIndex)
    (hpositive : ∀ i : Fin 5, 1 ≤ raw.lo i) (i : Fin 5) :
    0 < (originalFields raw c).hi i := by
  rw [original_hi_eq_actual]
  have hp : 0 < raw.lo i := lt_of_lt_of_le (by norm_num) (hpositive i)
  have hw : (0 : ℤ) < (width i : ℤ) := by fin_cases i <;> decide
  dsimp only [childRightNumer, childLeftNumer]
  positivity

private theorem active_integer_gates (raw : FifthWireRow) (c : ChildIndex)
    (hpositive : ∀ i : Fin 5, 1 ≤ raw.lo i)
    (hB : 0 < (originalFields raw c).B)
    (hb : 2 < originalRatioQ raw c)
    (he : rowEQ raw c ≤ originalRatioQ raw c - 2) :
    2 * (originalFields raw c).B < (originalFields raw c).A ∧
    2 * (1024 * (originalFields raw c).hi 4) * (originalFields raw c).B ≤
      (1024 * (originalFields raw c).hi 4) * (originalFields raw c).A -
        (originalFields raw c).d * (originalFields raw c).B := by
  have hBq : (0 : ℚ) < ((originalFields raw c).B : ℚ) := by exact_mod_cast hB
  have hH : (0 : ℚ) < 1024 * ((originalFields raw c).hi 4 : ℚ) := by
    exact mul_pos (by norm_num) (by exact_mod_cast hi_pos raw c hpositive 4)
  have htwo := (lt_div_iff₀ hBq).mp hb
  refine ⟨by exact_mod_cast htwo, ?_⟩
  change ((originalFields raw c).d : ℚ) / (1024 * ((originalFields raw c).hi 4 : ℚ)) ≤
    ((originalFields raw c).A : ℚ) / ((originalFields raw c).B : ℚ) - 2 at he
  have heNum := (div_le_iff₀ hH).mp he
  have heMul := mul_le_mul_of_nonneg_right heNum hBq.le
  have hclear :
      (((originalFields raw c).A : ℚ) / ((originalFields raw c).B : ℚ) - 2) *
          (1024 * ((originalFields raw c).hi 4 : ℚ)) * ((originalFields raw c).B : ℚ) =
        (1024 * ((originalFields raw c).hi 4 : ℚ)) * ((originalFields raw c).A : ℚ) -
          2 * (1024 * ((originalFields raw c).hi 4 : ℚ)) * ((originalFields raw c).B : ℚ) := by
    field_simp [hBq.ne'] <;> ring
  rw [hclear] at heMul
  have hgoal : (2 : ℚ) * (1024 * ((originalFields raw c).hi 4 : ℚ)) *
        ((originalFields raw c).B : ℚ) ≤
      (1024 * ((originalFields raw c).hi 4 : ℚ)) * ((originalFields raw c).A : ℚ) -
        ((originalFields raw c).d : ℚ) * ((originalFields raw c).B : ℚ) := by linarith
  exact_mod_cast hgoal

/-- Arbitrary original rows and masks: the original receiver's floor identity
follows from its active rational domain, without evaluating a stored floor. -/
theorem original_floor_eq_row_directed (raw : FifthWireRow) (c : ChildIndex)
    (hpositive : ∀ i : Fin 5, 1 ≤ raw.lo i)
    (hactive : 0 < rowD raw c →
      0 < (originalFields raw c).B ∧ 2 < originalRatioQ raw c ∧
        rowEQ raw c ≤ originalRatioQ raw c - 2) :
    originalExactFloor (originalFields raw c) =
      if 0 < rowD raw c then
        Int.floor (rowPrefactorQ raw c * directedQQ (originalRatioQ raw c) (rowEQ raw c) *
          dyadicScale 80) else 0 := by
  have h := P5OriginalWireExpandedFloorAlgebra.originalExactFloor_eq_directed_floor
    (originalFields raw c) (by
      intro hd
      obtain ⟨hB, hb, he⟩ := hactive hd
      obtain ⟨hA, hg⟩ := active_integer_gates raw c hpositive hB hb he
      exact ⟨hi_pos raw c hpositive, hB, hA, hg⟩)
  have hn : (originalFields raw c).n = 1600 := rfl
  have hw : ∀ i : Fin 5, (wireWidth i : ℚ) = (width i : ℚ) := by
    intro i
    fin_cases i <;> norm_num [wireWidth, width]
  simpa only [rowD, rowPrefactorQ, originalRatioQ, rowEQ, hn,
    original_hi_eq_actual, hw, Int.cast_ofNat] using h

/-- Positive-branch component in the existing SourceChildFacts interface.
No additional sign of row.n/DN or upper range b≤4 is needed for this identity. -/
theorem active_original_floor_eq_row_directed (raw : FifthWireRow) (c : ChildIndex)
    (hpositive : ∀ i : Fin 5, 1 ≤ raw.lo i) (hd : 0 < rowD raw c)
    (hB : 0 < (originalFields raw c).B) (hb : 2 < originalRatioQ raw c)
    (he : rowEQ raw c ≤ originalRatioQ raw c - 2) :
    originalExactFloor (originalFields raw c) =
      Int.floor (rowPrefactorQ raw c * directedQQ (originalRatioQ raw c) (rowEQ raw c) *
        dyadicScale 80) := by
  rw [original_floor_eq_row_directed raw c hpositive (fun _ => ⟨hB, hb, he⟩), if_pos hd]

end ImbalancedChen.P5OriginalWireFloorInstantiation
