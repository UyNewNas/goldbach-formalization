import ImbalancedChen.HistoricalThirdCoarsePolicy

-- SOURCE ONLY / UNCOMPILED_ZERO_CREDIT / ready=false.
-- A first-coordinate rise bound from the literal original Gamma max/if.
-- The xz/yz Boolean gates may change from true to false. No equality is used.
namespace ImbalancedChen.P1OriginalThirdGammaFirstCoordinateRise

noncomputable section
open VariableEnvelope HistoricalThirdCoarse

def shiftX (b : RationalBox) (d : ℚ) : RationalBox :=
  { lx := b.lx + d, ux := b.ux + d,
    ly := b.ly, uy := b.uy, lz := b.lz, uz := b.uz }

private theorem v_shift_le (t d : ℝ) (hd : 0 ≤ d) :
    v (t + d) ≤ v t + d / 2 := by
  rw [v_eq_min, v_eq_min]
  have hA : A (t + d) ≤ A t + d / 2 := by dsimp [A]; linarith
  have hC : C (t + d) ≤ C t + d / 2 := by dsimp [C]; linarith
  calc
    min (A (t + d)) (C (t + d)) ≤
        min (A t + d / 2) (C t + d / 2) := min_le_min hA hC
    _ = min (A t) (C t) + d / 2 := by rw [min_add_add_right]

private theorem qVLo_shift_le (l u d : ℚ) (hd : 0 ≤ d) :
    qVLo (l + d) (u + d) ≤ qVLo l u + d / 2 := by
  have hA : qA (l + d) ≤ qA l + d / 2 := by dsimp [qA]; linarith
  have hC : qC (u + d) ≤ qC u + d / 2 := by dsimp [qC]; linarith
  dsimp [qVLo]
  calc
    min (qA (l + d)) (qC (u + d)) ≤
        min (qA l + d / 2) (qC u + d / 2) := min_le_min hA hC
    _ = min (qA l) (qC u) + d / 2 := by rw [min_add_add_right]

private theorem xzGap_shift_le (b : RationalBox) (d : ℚ) (hd : 0 ≤ d) :
    xzGap (shiftX b d) ≤ xzGap b := by
  have hdR : (0 : ℝ) ≤ d := by exact_mod_cast hd
  have hv := v_shift_le ((b.ux : ℝ) + b.uz) d hdR
  dsimp [xzGap, shiftX] at *
  push_cast at *
  have harg : (b.ux : ℝ) + (d : ℝ) + b.uz =
      (b.ux : ℝ) + b.uz + (d : ℝ) := by ring
  rw [harg]
  linarith

private theorem yzGap_shift_le (b : RationalBox) (d : ℚ) (hd : 0 ≤ d) :
    yzGap (shiftX b d) ≤ yzGap b := by
  have hdR : (0 : ℝ) ≤ d := by exact_mod_cast hd
  dsimp [yzGap, shiftX]
  push_cast
  linarith

private theorem rescue_shift_le (b : RationalBox) (d : ℚ) (hd : 0 ≤ d) :
    rescue (shiftX b d) ≤ rescue b + d / 2 := by
  have hA : qA (b.lx + d) ≤ qA b.lx + d / 2 := by dsimp [qA]; linarith
  have hB : qB b.uz ≤ qB b.uz + d / 2 := by linarith
  dsimp [rescue, shiftX]
  exact (max_le_max hA hB).trans (by rw [max_add_add_right])

theorem fullGamma_shift_le (e : ℝ) (b : RationalBox) (d : ℚ) (hd : 0 ≤ d) :
    fullGamma e (shiftX b d) ≤ fullGamma e b + d / 2 := by
  let G := fullGamma e b
  have h0 : qVLo b.lx b.ux ≤ G := baseline_le_fullGamma e b
  have hxy : qVLo (b.lx + b.ly) (b.ux + b.uy) ≤ G := by
    dsimp [G, fullGamma]
    exact le_max_of_le_right (le_max_left _ _)
  have hxyz : qVLo (b.lx + b.ly + b.lz) (b.ux + b.uy + b.uz) ≤ G := by
    dsimp [G, fullGamma]
    exact le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
  have hr : rescue b ≤ G := by
    dsimp [G, fullGamma]
    exact le_max_of_le_right (le_max_of_le_right
      (le_max_of_le_right (le_max_left _ _)))
  have hxz (hg : e ≤ xzGap b) :
      qVLo (b.lx + b.lz) (b.ux + b.uz) ≤ G := by
    have h : (if e ≤ xzGap b then qVLo (b.lx + b.lz) (b.ux + b.uz)
      else qVLo b.lx b.ux) ≤ G := by
      dsimp [G, fullGamma]
      exact le_max_of_le_right (le_max_of_le_right
        (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))))
    simpa [hg] using h
  have hyz (hg : e ≤ yzGap b) :
      qVLo (b.ly + b.lz) (b.uy + b.uz) ≤ G := by
    have h : (if e ≤ yzGap b then qVLo (b.ly + b.lz) (b.uy + b.uz)
      else qVLo b.lx b.ux) ≤ G := by
      dsimp [G, fullGamma]
      exact le_max_of_le_right (le_max_of_le_right
        (le_max_of_le_right (le_max_of_le_right (le_max_right _ _))))
    simpa [hg] using h
  have hnew0 : qVLo (b.lx + d) (b.ux + d) ≤ G + d / 2 :=
    (qVLo_shift_le b.lx b.ux d hd).trans (add_le_add_right h0 _)
  have hnewxy : qVLo (b.lx + d + b.ly) (b.ux + d + b.uy) ≤ G + d / 2 := by
    simpa only [add_assoc, add_left_comm, add_comm] using
      (qVLo_shift_le (b.lx + b.ly) (b.ux + b.uy) d hd).trans
        (add_le_add_right hxy (d / 2))
  have hnewxyz : qVLo (b.lx + d + b.ly + b.lz)
      (b.ux + d + b.uy + b.uz) ≤ G + d / 2 := by
    simpa only [add_assoc, add_left_comm, add_comm] using
      (qVLo_shift_le (b.lx + b.ly + b.lz)
        (b.ux + b.uy + b.uz) d hd).trans (add_le_add_right hxyz (d / 2))
  have hnewres : rescue (shiftX b d) ≤ G + d / 2 :=
    (rescue_shift_le b d hd).trans (add_le_add_right hr _)
  have hnewxz : (if e ≤ xzGap (shiftX b d) then
      qVLo (b.lx + d + b.lz) (b.ux + d + b.uz)
      else qVLo (b.lx + d) (b.ux + d)) ≤ G + d / 2 := by
    by_cases hg : e ≤ xzGap (shiftX b d)
    · rw [if_pos hg]
      have hg0 : e ≤ xzGap b := hg.trans (xzGap_shift_le b d hd)
      simpa only [add_assoc, add_left_comm, add_comm] using
        (qVLo_shift_le (b.lx + b.lz) (b.ux + b.uz) d hd).trans
          (add_le_add_right (hxz hg0) (d / 2))
    · simpa [hg] using hnew0
  have hnewyz : (if e ≤ yzGap (shiftX b d) then
      qVLo (b.ly + b.lz) (b.uy + b.uz)
      else qVLo (b.lx + d) (b.ux + d)) ≤ G + d / 2 := by
    by_cases hg : e ≤ yzGap (shiftX b d)
    · rw [if_pos hg]
      exact (hyz (hg.trans (yzGap_shift_le b d hd))).trans
        (le_add_of_nonneg_right (by positivity))
    · simpa [hg] using hnew0
  dsimp [fullGamma, shiftX]
  simp only [max_le_iff]
  exact ⟨hnew0, hnewxy, hnewxyz, hnewres, hnewxz, hnewyz⟩

-- This is a genuine Gamma statement, with full-dispatch facts exposed.
-- A contained key<=77 raw child supplies both facts for z in [0,3/51200].
theorem gamma_shift_le (e : ℝ) (b : RationalBox) (d : ℚ) (hd : 0 ≤ d)
    (hb : (b.ux : ℝ) ≤ mu - 4 * e)
    (hshift : ((shiftX b d).ux : ℝ) ≤ mu - 4 * e) :
    gamma e (shiftX b d) ≤ gamma e b + d / 2 := by
  rw [gamma, if_pos hshift, gamma, if_pos hb]
  exact fullGamma_shift_le e b d hd

end
end ImbalancedChen.P1OriginalThirdGammaFirstCoordinateRise
