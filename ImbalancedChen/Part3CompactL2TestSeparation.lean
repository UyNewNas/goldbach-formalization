import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Basic

/-! SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
Actual compact continuous scalar tests separate native planar complex L2.
The test density is proved from native regular-measure Lp approximation;
it is not a premise. This is used to identify Bochner and scalar convolutions.
-/
namespace ImbalancedChen.Part3.CompactL2TestSeparation20261026a
noncomputable section
open MeasureTheory Set

abbrev Plane := ℝ × ℝ
abbrev PlaneL2 := Lp ℂ 2 (volume : Measure Plane)

theorem eq_zero_of_compact_continuous_tests (u : PlaneL2)
    (hzero : ∀ (h : Plane → ℂ) (hh : Continuous h) (hc : HasCompactSupport h)
      (hm : MemLp h 2 volume), inner ℂ (hm.toLp h) u = 0) : u = 0 := by
  by_contra hu
  have hpos : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have heps : ENNReal.ofReal (‖u‖ / 2) ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (half_pos hpos))
  obtain ⟨h, hc, happrox, hh, hm⟩ :=
    u.memLp.exists_hasCompactSupport_eLpNorm_sub_le (by norm_num) heps
  have hn : ‖u - hm.toLp h‖ ≤ ‖u‖ / 2 := by
    rw [Lp.norm_def]
    have heq : eLpNorm (u - hm.toLp h) 2 volume =
        eLpNorm (fun p => u p - h p) 2 volume := by
      apply eLpNorm_congr_ae
      filter_upwards [Lp.coeFn_sub u (hm.toLp h), hm.coeFn_toLp] with p hp hhp
      rw [hp, hhp]
    rw [heq]
    exact (ENNReal.toReal_mono (by simp) happrox).trans_eq
      (ENNReal.toReal_ofReal (half_pos hpos).le)
  have hb := re_inner_le_norm (𝕜 := ℂ) (u - hm.toLp h) u
  rw [inner_sub_left, hzero h hh hc hm, sub_zero,
    ← InnerProductSpace.norm_sq_eq_re_inner] at hb
  have hm' := mul_le_mul_of_nonneg_right hn (norm_nonneg u)
  nlinarith

theorem eq_of_compact_continuous_tests (u v : PlaneL2)
    (heq : ∀ (h : Plane → ℂ) (hh : Continuous h) (hc : HasCompactSupport h)
      (hm : MemLp h 2 volume), inner ℂ (hm.toLp h) u = inner ℂ (hm.toLp h) v) :
    u = v := by
  apply sub_eq_zero.mp
  apply eq_zero_of_compact_continuous_tests
  intro h hh hc hm
  rw [inner_sub_right, heq h hh hc hm, sub_self]

end
end ImbalancedChen.Part3.CompactL2TestSeparation20261026a
