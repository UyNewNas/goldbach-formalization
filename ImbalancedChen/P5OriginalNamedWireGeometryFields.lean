import ImbalancedChen.P5OriginalWireChildDIdentity

/-! The three original named geometry/field targets, without recomputing d.
The old namespace and full theorem names are preserved for compatibility. -/
namespace ImbalancedChen.P5OriginalChildIntegerWireBinding

open P1OriginalPrefixRowDecodeSoundness
open P5NamedFifthPayloadSemantics P5NamedFifthAllChildren
open P5NamedFifthChildSpecificRatio
open P5OldFifthExact64ChildTiling P5OldFifthFrozenUpperSurrogate
open P5OriginalWireParentPickAlignment P5OriginalWireChildDIdentity

private theorem named_AB_fields :
    ∀ b : Bool, ∀ c : ChildIndex,
      0 < (originalFields (namedParent b) c).B ∧
      ((originalFields (namedParent b) c).A : ℚ) /
        ((originalFields (namedParent b) c).B : ℚ) = childBQ b c := by
  decide +kernel

theorem original_parent_picks_exact :
    ∀ b : Bool, ∀ I : OldMask, originalPick (namedParent b) I = sourcePick (namedParent b) I := by
  intro b I
  exact originalPick_eq_sourcePick (namedParent b) (named_grid b) I

theorem original_all128_geometry_fields :
    ∀ b : Bool, ∀ c : ChildIndex,
      (originalFields (namedParent b) c).d = sourceChildD (namedParent b) c ∧
      0 < (originalFields (namedParent b) c).B ∧
      ((originalFields (namedParent b) c).A : ℚ) /
        ((originalFields (namedParent b) c).B : ℚ) = childBQ b c := by
  intro b c
  exact ⟨originalD_eq_sourceChildD (namedParent b) (named_grid b) c, named_AB_fields b c⟩

theorem original_all128_active_field_gates :
    ∀ b : Bool, ∀ c : ChildIndex,
      let row := originalFields (namedParent b) c
      0 < row.d →
        2 * row.B < row.A ∧ row.A ≤ 4 * row.B ∧
        2 * (1024 * row.hi 4) * row.B ≤
          (1024 * row.hi 4) * row.A - row.d * row.B := by
  intro b c
  dsimp only
  intro hd
  obtain ⟨hd_eq, hB, hAB⟩ := original_all128_geometry_fields b c
  have hBQ : (0 : ℚ) < ((originalFields (namedParent b) c).B : ℚ) := by exact_mod_cast hB
  have hsmall : (2 : ℚ) <
      ((originalFields (namedParent b) c).A : ℚ) /
        ((originalFields (namedParent b) c).B : ℚ) := by
    rw [hAB]
    exact (all_child_ratio_ranges b c).1
  have hlarge : ((originalFields (namedParent b) c).A : ℚ) /
        ((originalFields (namedParent b) c).B : ℚ) ≤ 4 := by
    rw [hAB]
    exact (all_child_ratio_ranges b c).2.2
  have htwo := (lt_div_iff₀ hBQ).mp hsmall
  have hfour := (div_le_iff₀ hBQ).mp hlarge
  refine ⟨by exact_mod_cast htwo, by exact_mod_cast hfour, ?_⟩
  have hhi : 0 < (originalFields (namedParent b) c).hi 4 := by
    rw [P5OriginalGenericWireFloorReceiver.original_hi_eq_actual]
    have hp := named_positive_indices b (4 : Fin 5)
    have hc : (0 : ℤ) ≤ ((c 4).val : ℤ) := Int.natCast_nonneg _
    norm_num [childRightNumer, childLeftNumer, width]
    omega
  have hH : (0 : ℚ) < 1024 * ((originalFields (namedParent b) c).hi 4 : ℚ) := by
    exact mul_pos (by norm_num) (by exact_mod_cast hhi)
  have hdSrc : 0 ≤ sourceChildD (namedParent b) c := by
    rw [← hd_eq]
    exact hd.le
  have he := (all_active_e_ranges b c hdSrc).2
  rw [childEQ, ← hd_eq, ← hAB,
    ← P5OriginalGenericWireFloorReceiver.original_hi_eq_actual (namedParent b) c 4] at he
  have heNum := (div_le_iff₀ hH).mp he
  have heMul := mul_le_mul_of_nonneg_right heNum hBQ.le
  have hclear :
      (((originalFields (namedParent b) c).A : ℚ) /
          ((originalFields (namedParent b) c).B : ℚ) - 2) *
          (1024 * ((originalFields (namedParent b) c).hi 4 : ℚ)) *
          ((originalFields (namedParent b) c).B : ℚ) =
        (1024 * ((originalFields (namedParent b) c).hi 4 : ℚ)) *
          ((originalFields (namedParent b) c).A : ℚ) -
        2 * (1024 * ((originalFields (namedParent b) c).hi 4 : ℚ)) *
          ((originalFields (namedParent b) c).B : ℚ) := by
    field_simp [hBQ.ne'] <;> ring
  rw [hclear] at heMul
  have heGoal : (2 : ℚ) * (1024 * ((originalFields (namedParent b) c).hi 4 : ℚ)) *
        ((originalFields (namedParent b) c).B : ℚ) ≤
      (1024 * ((originalFields (namedParent b) c).hi 4 : ℚ)) *
          ((originalFields (namedParent b) c).A : ℚ) -
        ((originalFields (namedParent b) c).d : ℚ) *
          ((originalFields (namedParent b) c).B : ℚ) := by
    linarith
  exact_mod_cast heGoal

end ImbalancedChen.P5OriginalChildIntegerWireBinding
