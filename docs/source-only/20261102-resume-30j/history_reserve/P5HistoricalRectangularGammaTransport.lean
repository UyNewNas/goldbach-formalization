import ImbalancedChen.HistoricalThirdCoarsePolicy

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Quantitative transport for HistoricalThirdCoarse.fullGamma itself. The
closed rectangular endpoints and the two actual whole-box pair gates are
retained. This is not the distinct robust dyadic physical-cell Gamma.
The baseline absorbs a pair that loses at the point; a winning pair has
the original 3/256 gate margin, losing at most seven rectangle widths.
-/
namespace ImbalancedChen.P5HistoricalRectangularGammaTransport
noncomputable section
open VariableEnvelope HistoricalThirdCoarse

theorem coordinate_widths (b : RationalBox) (chi : ℝ)
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

/-- The actual upper-corner selected gaps lose at most 7 chi. -/
theorem pair_gap_lower (b : RationalBox) (chi : ℝ)
    (hw : (b.width : ℝ) ≤ chi) {x y z : ℝ} (ht : b.InBox x y z) :
    v (x + z) - (x + 2 * y + z) - 7 * chi ≤ xzGap b ∧
      v (y + z) - (2 * x + y + z) - 7 * chi ≤ yzGap b := by
  obtain ⟨hx, hy, hz⟩ := coordinate_widths b chi hw
  have hxz : |((b.ux : ℝ) + b.uz) - (x + z)| ≤ 2 * chi := by
    apply abs_le.mpr
    constructor <;> linarith [ht.1, ht.2.1, ht.2.2.2.2.1, ht.2.2.2.2.2]
  have hyz : |((b.uy : ℝ) + b.uz) - (y + z)| ≤ 2 * chi := by
    apply abs_le.mpr
    constructor <;> linarith [ht.2.2.1, ht.2.2.2.1,
      ht.2.2.2.2.1, ht.2.2.2.2.2]
  have hvxz := (abs_le.mp (v_abs_sub_le_of_le hxz)).1
  have hvyz := (abs_le.mp (v_abs_sub_le_of_le hyz)).1
  constructor <;> dsimp only [xzGap, yzGap] <;>
    linarith [ht.1, ht.2.2.1, ht.2.2.2.2.1]

theorem winning_pairs_admitted (e chi : ℝ) (b : RationalBox)
    (hw : (b.width : ℝ) ≤ chi) {x y z : ℝ} (ht : b.InBox x y z)
    (ho : Ordered x y z) (hfine : e + 7 * chi ≤ 3 / 256) :
    (v x ≤ v (x + z) → e ≤ xzGap b) ∧
      (v x ≤ v (y + z) → e ≤ yzGap b) := by
  have hg := pair_gap_lower b chi hw ht
  constructor
  · intro hwin
    have hm := xz_gate_margin ho hwin
    linarith [hg.1]
  · intro hwin
    have hm := yz_gate_margin ho hwin
    linarith [hg.2]

/-- All six original branches, including both selected nonleading pairs
and the max(A,W) rescue, feed the independently defined rectangular rule.
No branch choice, pair licence or approximation estimate is an input. -/
theorem fullGamma_error (e chi : ℝ) (b : RationalBox)
    (hchi : 0 ≤ chi) (hw : (b.width : ℝ) ≤ chi)
    {x y z : ℝ} (ht : b.InBox x y z) (ho : Ordered x y z)
    (hfine : e + 7 * chi ≤ 3 / 256) :
    0 ≤ six x y z - (fullGamma e b : ℝ) ∧
      six x y z - (fullGamma e b : ℝ) ≤ (9 / 2 : ℝ) * chi := by
  obtain ⟨hx, hy, hz⟩ := coordinate_widths b chi hw
  have hbase := rationalInterval_v_error ht.1 ht.2.1
  have hxy := rationalInterval_v_error
    (l := b.lx + b.ly) (u := b.ux + b.uy) (x := x + y)
    (by push_cast; linarith [ht.1, ht.2.2.1])
    (by push_cast; linarith [ht.2.1, ht.2.2.2.1])
  have hxyz := rationalInterval_v_error
    (l := b.lx + b.ly + b.lz) (u := b.ux + b.uy + b.uz) (x := x + y + z)
    (by push_cast; linarith [ht.1, ht.2.2.1, ht.2.2.2.2.1])
    (by push_cast; linarith [ht.2.1, ht.2.2.2.1, ht.2.2.2.2.2])
  have hxz := rationalInterval_v_error
    (l := b.lx + b.lz) (u := b.ux + b.uz) (x := x + z)
    (by push_cast; linarith [ht.1, ht.2.2.2.2.1])
    (by push_cast; linarith [ht.2.1, ht.2.2.2.2.2])
  have hyz := rationalInterval_v_error
    (l := b.ly + b.lz) (u := b.uy + b.uz) (x := y + z)
    (by push_cast; linarith [ht.2.2.1, ht.2.2.2.2.1])
    (by push_cast; linarith [ht.2.2.2.1, ht.2.2.2.2.2])
  push_cast at hxy hxyz hxz hyz
  have hb : (qVLo b.lx b.ux : ℝ) ≤ fullGamma e b := by
    exact_mod_cast baseline_le_fullGamma e b
  have hp : (qVLo (b.lx + b.ly) (b.ux + b.uy) : ℝ) ≤ fullGamma e b := by
    simp [fullGamma]
  have ht3 : (qVLo (b.lx + b.ly + b.lz) (b.ux + b.uy + b.uz) : ℝ) ≤
      fullGamma e b := by simp [fullGamma]
  have hr : (rescue b : ℝ) ≤ fullGamma e b := by simp [fullGamma]
  have hWr : B z - (3 / 8 : ℝ) * chi ≤ (rescue b : ℝ) := by
    simp only [rescue, Rat.cast_max, cast_qA, cast_qB]
    apply le_max_of_le_right
    dsimp only [B]
    linarith [ht.2.2.2.2.1]
  have hpair := winning_pairs_admitted e chi b hw ht ho hfine
  have hXZ : v (x + z) ≤ (fullGamma e b : ℝ) + (9 / 2 : ℝ) * chi := by
    by_cases hwin : v x ≤ v (x + z)
    · have hg : (qVLo (b.lx + b.lz) (b.ux + b.uz) : ℝ) ≤ fullGamma e b := by
        simp [fullGamma, hpair.1 hwin]
      linarith
    · have hlose := lt_of_not_ge hwin
      linarith
  have hYZ : v (y + z) ≤ (fullGamma e b : ℝ) + (9 / 2 : ℝ) * chi := by
    by_cases hwin : v x ≤ v (y + z)
    · have hg : (qVLo (b.ly + b.lz) (b.uy + b.uz) : ℝ) ≤ fullGamma e b := by
        simp [fullGamma, hpair.2 hwin]
      linarith
    · have hlose := lt_of_not_ge hwin
      linarith
  have hupper := fullGamma_le_original e b ht ho
  rw [original_eq_six ho] at hupper
  refine ⟨sub_nonneg.mpr hupper, ?_⟩
  have hmax : six x y z ≤ (fullGamma e b : ℝ) + (9 / 2 : ℝ) * chi := by
    unfold six
    exact max_le (by linarith) (max_le (by linarith)
      (max_le (by linarith) (max_le (by linarith) (max_le hXZ hYZ))))
  linarith

/-- The zero-buffer history uses exactly this full rule below mu. -/
theorem zero_level_error (chi : ℝ) (b : RationalBox)
    (hchi : 0 ≤ chi) (hw : (b.width : ℝ) ≤ chi)
    {x y z : ℝ} (ht : b.InBox x y z) (ho : Ordered x y z)
    (hfull : (b.ux : ℝ) ≤ mu) (hfine : 7 * chi ≤ 3 / 256) :
    0 ≤ six x y z - levelExponent 0 b ∧
      six x y z - levelExponent 0 b ≤ (9 / 2 : ℝ) * chi := by
  simpa only [levelExponent, gamma, mul_zero, sub_zero, if_pos hfull] using
    fullGamma_error 0 chi b hchi hw ht ho (by simpa using hfine)

end
end ImbalancedChen.P5HistoricalRectangularGammaTransport
