import ImbalancedChen.P5OriginalChildIntegerWireDefinitions
import ImbalancedChen.P5NamedFifthPayloadSemantics

/-! Exact first-argmin agreement for the original grid400 parent scores.
No chosen-parent, positive-coordinate or desired-bound premise is used. -/
namespace ImbalancedChen.P5OriginalWireParentPickAlignment

open scoped BigOperators
open P1OriginalPrefixRowDecodeSoundness
open P5OldFifthFrozenUpperSurrogate
open P5OriginalChildIntegerWireBinding
open P5NamedFifthPayloadSemantics

theorem originalPick_eq_sourcePick (raw : FifthWireRow) (hg : raw.grid = 400)
    (I : OldMask) : originalPick raw I = sourcePick raw I := by
  let ss : ℤ := ∑ i ∈ I, (2 * raw.lo i.castSucc + 1)
  have hsum : (∑ i ∈ I, (2 * (raw.lo i.castSucc : ℚ) + 1)) = (ss : ℚ) := by
    norm_num [ss]
  have hs := parent_score_alignment raw hg I
  dsimp only at hs
  obtain ⟨ha, hc, hk⟩ := hs
  rw [hsum] at ha hc
  have hAC : ((1 + parentSumQ raw I) / 2 ≤ 57 / 64 - 3 * parentSumQ raw I / 2) ↔
      (32 * 400 + 16 * ss : ℤ) ≤ 57 * 400 - 48 * ss := by
    rw [ha, hc, div_le_div_iff_of_pos_right (by norm_num : (0 : ℚ) < 64 * 400)]
    norm_cast
  have hAK : ((1 + parentSumQ raw I) / 2 ≤ (153 / 256 : ℚ)) ↔
      (32 * 400 + 16 * ss : ℤ) ≤ 153 * 400 / 4 := by
    rw [ha, hk, div_le_div_iff_of_pos_right (by norm_num : (0 : ℚ) < 64 * 400)]
    norm_num <;> norm_cast
  have hCK : (57 / 64 - 3 * parentSumQ raw I / 2 ≤ (153 / 256 : ℚ)) ↔
      (57 * 400 - 48 * ss : ℤ) ≤ 153 * 400 / 4 := by
    rw [hc, hk, div_le_div_iff_of_pos_right (by norm_num : (0 : ℚ) < 64 * 400)]
    norm_num <;> norm_cast
  dsimp only [originalPick, sourcePick]
  simp only [hg, hAC, hAK, hCK, ss]

end ImbalancedChen.P5OriginalWireParentPickAlignment
