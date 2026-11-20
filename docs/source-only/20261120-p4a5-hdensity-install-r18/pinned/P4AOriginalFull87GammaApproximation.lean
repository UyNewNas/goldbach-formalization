import ImbalancedChen.HistoricalThirdCoarsePolicy

/-!
SOURCE ONLY / UNCOMPILED / NO KERNEL CREDIT.

A lower approximation for the ACTUAL HistoricalThirdCoarse.gamma, not for
an alternative rational-box enclosure. The two pair entries keep their
original whole-box gates. A pair which loses to the baseline is paid by
that baseline; a winning pair has the original 3/256 gate surplus.
No source-specific winning plane or asserted Gamma approximation is input.
-/
namespace ImbalancedChen.P4AOriginalFull87GammaApproximation
noncomputable section
open VariableEnvelope HistoricalThirdCoarse

 theorem side_widths {b : RationalBox} {chi : ℝ}
    (hw : (b.width : ℝ) ≤ chi) :
    (b.ux : ℝ) - b.lx ≤ chi ∧ (b.uy : ℝ) - b.ly ≤ chi ∧
      (b.uz : ℝ) - b.lz ≤ chi := by
  have hx : (b.ux : ℝ) - b.lx ≤ b.width := by
    exact_mod_cast b.coordinate_widths_le.1
  have hy : (b.uy : ℝ) - b.ly ≤ b.width := by
    exact_mod_cast b.coordinate_widths_le.2.1
  have hz : (b.uz : ℝ) - b.lz ≤ b.width := by
    exact_mod_cast b.coordinate_widths_le.2.2
  exact ⟨hx.trans hw, hy.trans hw, hz.trans hw⟩

/-- Two coordinate intervals debit at most 3*chi from their tent value. -/
theorem upper_pair_tent (a b A B chi : ℝ)
    (ha : a ≤ A) (hb : b ≤ B) (hA : A - a ≤ chi) (hB : B - b ≤ chi) :
    v (a + b) - 3 * chi ≤ v (A + B) := by
  have hvA : v (a + b) ≤ VariableEnvelope.A (a + b) := by
    rw [v_eq_min]; exact min_le_left _ _
  have hvC : v (a + b) ≤ C (a + b) := by
    rw [v_eq_min]; exact min_le_right _ _
  rw [v_eq_min]
  apply le_min <;> dsimp [VariableEnvelope.A, C] at * <;> linarith

/-- A winning original xz pair survives the literal whole-box gate. -/
theorem winning_xz_gate {b : RationalBox} {x y z e chi : ℝ}
    (ho : Ordered x y z) (hb : b.InBox x y z) (hw : (b.width : ℝ) ≤ chi)
    (hsmall : e + 7 * chi ≤ 3 / 256) (hwin : v x ≤ v (x + z)) :
    e ≤ xzGap b := by
  obtain ⟨hx, hy, hz⟩ := side_widths hw
  have ht := upper_pair_tent x z (b.ux : ℝ) (b.uz : ℝ) chi
    hb.2.1 hb.2.2.2.2.2 (by linarith [hb.1]) (by linarith [hb.2.2.2.2.1])
  have hm := xz_gate_margin ho hwin
  dsimp [xzGap]
  linarith [hb.1, hb.2.2.1, hb.2.2.2.2.1]

/-- A winning original yz pair survives the literal whole-box gate. -/
theorem winning_yz_gate {b : RationalBox} {x y z e chi : ℝ}
    (ho : Ordered x y z) (hb : b.InBox x y z) (hw : (b.width : ℝ) ≤ chi)
    (hsmall : e + 7 * chi ≤ 3 / 256) (hwin : v x ≤ v (y + z)) :
    e ≤ yzGap b := by
  obtain ⟨hx, hy, hz⟩ := side_widths hw
  have ht := upper_pair_tent y z (b.uy : ℝ) (b.uz : ℝ) chi
    hb.2.2.2.1 hb.2.2.2.2.2 (by linarith [hb.2.2.1]) (by linarith [hb.2.2.2.2.1])
  have hm := yz_gate_margin ho hwin
  dsimp [yzGap]
  linarith [hb.1, hb.2.2.1, hb.2.2.2.2.1]

/-- All SIX continuous branch values are approximated by the unchanged
GATED finite maximum. No pair gate is removed to obtain this estimate. -/
theorem six_le_fullGamma_add_error {b : RationalBox} {x y z e chi : ℝ}
    (ho : Ordered x y z) (hb : b.InBox x y z) (hw : (b.width : ℝ) ≤ chi)
    (hsmall : e + 7 * chi ≤ 3 / 256) :
    six x y z ≤ (fullGamma e b : ℝ) + (9 / 2 : ℝ) * chi := by
  obtain ⟨hx, hy, hz⟩ := side_widths hw
  have hchi : 0 ≤ chi :=
    (show (0 : ℝ) ≤ b.width by exact_mod_cast b.width_nonneg).trans hw
  have h0 : (qVLo b.lx b.ux : ℝ) ≤ (fullGamma e b : ℝ) := by
    exact_mod_cast baseline_le_fullGamma e b
  have hxy : (qVLo (b.lx + b.ly) (b.ux + b.uy) : ℝ) ≤ (fullGamma e b : ℝ) := by
    exact_mod_cast (show qVLo (b.lx + b.ly) (b.ux + b.uy) ≤ fullGamma e b from
      le_max_of_le_right (le_max_left _ _))
  have hxyz : (qVLo (b.lx + b.ly + b.lz) (b.ux + b.uy + b.uz) : ℝ) ≤
      (fullGamma e b : ℝ) := by
    exact_mod_cast (show qVLo (b.lx + b.ly + b.lz) (b.ux + b.uy + b.uz) ≤ fullGamma e b from
      le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))
  have hr : (rescue b : ℝ) ≤ (fullGamma e b : ℝ) := by
    exact_mod_cast (show rescue b ≤ fullGamma e b from
      le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))))
  have hv0 : v x ≤ (fullGamma e b : ℝ) + (9 / 2 : ℝ) * chi := by
    have hh := rationalInterval_v_error hb.1 hb.2.1
    linarith
  have hvxy : v (x + y) ≤ (fullGamma e b : ℝ) + (9 / 2 : ℝ) * chi := by
    have hh := rationalInterval_v_error
      (l := b.lx + b.ly) (u := b.ux + b.uy) (x := x + y)
      (by push_cast; linarith [hb.1, hb.2.2.1])
      (by push_cast; linarith [hb.2.1, hb.2.2.2.1])
    push_cast at hh
    linarith
  have hvxyz : v (x + y + z) ≤ (fullGamma e b : ℝ) + (9 / 2 : ℝ) * chi := by
    have hh := rationalInterval_v_error
      (l := b.lx + b.ly + b.lz) (u := b.ux + b.uy + b.uz) (x := x + y + z)
      (by push_cast; linarith [hb.1, hb.2.2.1, hb.2.2.2.2.1])
      (by push_cast; linarith [hb.2.1, hb.2.2.2.1, hb.2.2.2.2.2])
    push_cast at hh
    linarith
  have hvB : B z ≤ (fullGamma e b : ℝ) + (9 / 2 : ℝ) * chi := by
    have hB : B (b.uz : ℝ) ≤ (rescue b : ℝ) := by
      simp only [rescue, Rat.cast_max, cast_qA, cast_qB]
      exact le_max_right _ _
    dsimp [B] at hB ⊢
    linarith [hb.2.2.2.2.1]
  have hvxz : v (x + z) ≤ (fullGamma e b : ℝ) + (9 / 2 : ℝ) * chi := by
    by_cases hwin : v x ≤ v (x + z)
    · have hgate := winning_xz_gate ho hb hw hsmall hwin
      have hq : (qVLo (b.lx + b.lz) (b.ux + b.uz) : ℝ) ≤ (fullGamma e b : ℝ) := by
        have hqr : qVLo (b.lx + b.lz) (b.ux + b.uz) ≤ fullGamma e b := by
          dsimp only [fullGamma]
          rw [if_pos hgate]
          exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
            (le_max_of_le_right (le_max_left _ _))))
        exact_mod_cast hqr
      have hh := rationalInterval_v_error
        (l := b.lx + b.lz) (u := b.ux + b.uz) (x := x + z)
        (by push_cast; linarith [hb.1, hb.2.2.2.2.1])
        (by push_cast; linarith [hb.2.1, hb.2.2.2.2.2])
      push_cast at hh
      linarith
    · exact (lt_of_not_ge hwin).le.trans hv0
  have hvyz : v (y + z) ≤ (fullGamma e b : ℝ) + (9 / 2 : ℝ) * chi := by
    by_cases hwin : v x ≤ v (y + z)
    · have hgate := winning_yz_gate ho hb hw hsmall hwin
      have hq : (qVLo (b.ly + b.lz) (b.uy + b.uz) : ℝ) ≤ (fullGamma e b : ℝ) := by
        have hqr : qVLo (b.ly + b.lz) (b.uy + b.uz) ≤ fullGamma e b := by
          dsimp only [fullGamma]
          rw [if_pos hgate]
          exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
            (le_max_of_le_right (le_max_right _ _))))
        exact_mod_cast hqr
      have hh := rationalInterval_v_error
        (l := b.ly + b.lz) (u := b.uy + b.uz) (x := y + z)
        (by push_cast; linarith [hb.2.2.1, hb.2.2.2.2.1])
        (by push_cast; linarith [hb.2.2.2.1, hb.2.2.2.2.2])
      push_cast at hh
      linarith
    · exact (lt_of_not_ge hwin).le.trans hv0
  exact max_le hv0 (max_le hvxy (max_le hvxyz (max_le hvB (max_le hvxz hvyz))))

/-- The actual whole-box Gamma approximation with its original buffer
subtracted ONCE. The source may use ANY winning original branch. -/
theorem actual_gamma_sandwich {b : RationalBox} {x y z e chi : ℝ}
    (he : 0 ≤ e) (ho : Ordered x y z) (hb : b.InBox x y z)
    (hw : (b.width : ℝ) ≤ chi) (hfull : (b.ux : ℝ) ≤ mu - 4 * e)
    (hsmall : e + 7 * chi ≤ 3 / 256) :
    six x y z - ((9 / 2 : ℝ) * chi + 2 * e) ≤ levelExponent e b ∧
      levelExponent e b ≤ six x y z := by
  have hlo := six_le_fullGamma_add_error ho hb hw hsmall
  have hup := fullGamma_le_original e b hb ho
  rw [original_eq_six ho] at hup
  simp only [levelExponent, gamma, if_pos hfull]
  constructor <;> linarith

end
end ImbalancedChen.P4AOriginalFull87GammaApproximation
