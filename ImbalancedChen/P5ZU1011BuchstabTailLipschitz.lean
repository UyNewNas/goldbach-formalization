import MathlibNt.SieveTheory.LiLiuBuchstabTailPropagation
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
The actual rebased Buchstab integral equation gives a quantitative
one-half Lipschitz bound on ALL [2,infinity), hence throughout the true
original sixteen-bank switched argument interval [77/38,8]. No derivative,
modulus of continuity or tail-oscillation estimate is a premise.
-/

namespace ImbalancedChen.P5Z.U1011BuchstabTailLipschitz

noncomputable section

open Set MeasureTheory LiLiuPrereqBuchstab
open scoped Interval

/-- The genuine weighted increment is paid by its true unit-height
delay-integral interval, at arbitrary real anchors beyond two. -/
theorem weighted_increment_bounds {s t : ℝ} (hs : 2 ≤ s) (hst : s ≤ t) :
    0 ≤ t * buchstab t - s * buchstab s ∧
      t * buchstab t - s * buchstab s ≤ t - s := by
  have hc : Continuous (fun x : ℝ => buchstab (x - 1)) :=
    continuous_buchstab.comp (continuous_id.sub continuous_const)
  have hi0 : 0 ≤ ∫ x in s..t, buchstab (x - 1) := by
    apply intervalIntegral.integral_nonneg hst
    intro x hx
    exact buchstab_nonneg (by linarith only [hs, hx.1])
  have hi1 := intervalIntegral.integral_mono_on hst (hc.intervalIntegrable s t)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume s t)
    (fun x hx => buchstab_le_one (by linarith only [hs, hx.1] : 1 ≤ x - 1))
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one] at hi1
  rw [buchstab_weighted_sub_eq_integral hs hst]
  exact ⟨hi0, hi1⟩

/-- The TRUE Buchstab function is one-half Lipschitz for s,t>=2.
No upper truncation of this tail estimate is required. -/
theorem abs_sub_le_half {s t : ℝ} (hs : 2 ≤ s) (ht : 2 ≤ t) :
    |buchstab s - buchstab t| ≤ |s - t| / 2 := by
  have hordered : ∀ s t : ℝ, 2 ≤ s → 2 ≤ t → s ≤ t →
      |buchstab s - buchstab t| ≤ |s - t| / 2 := by
    intro s t hs ht hst
    have hinc := weighted_increment_bounds hs hst
    have hδ : 0 ≤ t - s := sub_nonneg.mpr hst
    have hω0 := buchstab_nonneg (show 1 ≤ s by linarith only [hs])
    have hω1 := buchstab_le_one (show 1 ≤ s by linarith only [hs])
    have hmul0 : 0 ≤ (t - s) * buchstab s := mul_nonneg hδ hω0
    have hmul1 : (t - s) * buchstab s ≤ t - s := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hω1 hδ
    have hLo : -(t - s) ≤ t * (buchstab t - buchstab s) := by
      nlinarith only [hinc.1, hmul1]
    have hHi : t * (buchstab t - buchstab s) ≤ t - s := by
      nlinarith only [hinc.2, hmul0]
    have hAbs : |t * (buchstab t - buchstab s)| ≤ t - s := abs_le.mpr ⟨hLo, hHi⟩
    rw [abs_mul, abs_of_pos (show 0 < t by linarith only [ht]),
      abs_sub_comm (buchstab t) (buchstab s)] at hAbs
    have hscale := mul_le_mul_of_nonneg_right ht (abs_nonneg (buchstab s - buchstab t))
    rw [abs_of_nonpos (sub_nonpos.mpr hst)]
    nlinarith only [hAbs, hscale]
  rcases le_total s t with h | h
  · exact hordered s t hs ht h
  · simpa only [abs_sub_comm] using hordered t s ht hs h

theorem lipschitzOn_tail : LipschitzOnWith (1 / 2) buchstab (Ici (2 : ℝ)) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro s hs t ht
  have h := abs_sub_le_half hs ht
  change |buchstab s - buchstab t| ≤ (1 / 2 : ℝ) * |s - t|
  nlinarith only [h]

theorem abs_sub_le_original_switched {s t : ℝ}
    (hs : s ∈ Icc (77 / 38 : ℝ) 8) (ht : t ∈ Icc (77 / 38 : ℝ) 8) :
    |buchstab s - buchstab t| ≤ |s - t| / 2 :=
  abs_sub_le_half (by linarith only [hs.1]) (by linarith only [ht.1])

end

end ImbalancedChen.P5Z.U1011BuchstabTailLipschitz
