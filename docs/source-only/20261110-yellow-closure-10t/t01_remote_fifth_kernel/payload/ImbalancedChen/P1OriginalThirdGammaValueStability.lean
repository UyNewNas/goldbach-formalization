import ImbalancedChen.HistoricalThirdCoarsePolicy
import ImbalancedChen.P1OriginalFifthGrid400RefinedFullBoxCover
import ImbalancedChen.P1OriginalPrefixRowDecodeSoundness
import ImbalancedChen.P1OriginalCoarseFifthJointGeometry

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

One-sided VALUE stability of the actual third Gamma on an original
grid400 fifth-row key <= 77, its contained refined cell, and an adopted
ordered third-owner box. A changed Boolean pair gate need not change the
maximum: if its whole-box gap is below the small buffer, the original
ordered-envelope margin forces its upper-corner value below the leading
branch. The only possible loss is the leading cell's half-width.

The refinement q, contained-cell test and third-owner projection are the
existing manuscript-internal constructors. The caller supplies the actual
schedule inequalities e <= 3/51200, step(refinedMesh q) <= chi <= e/10;
the positive q and geometric adopted-cell membership are explicit. No
upper integral or slab estimate is asserted. No compiler or replay ran.
-/

namespace ImbalancedChen.P1OriginalThirdGammaValueStability

noncomputable section

open VariableEnvelope HistoricalThirdCoarse
open P1OriginalFifthGrid400RefinedFullBoxCover
open P1OriginalPrefixRowDecodeSoundness
open HistoricalThirdCoarse.P1OriginalCoarseFifth

private theorem gamma_zero_le_buffer_box
    (e chi : ℝ) (b : RationalBox)
    (he : 0 ≤ e) (hesmall : e ≤ 3 / 51200)
    (hw : b.WellFormed) (hz : 0 ≤ b.lz)
    (hzy : b.uz ≤ b.ly) (hyx : b.uy ≤ b.lx)
    (hux : (b.ux : ℝ) ≤ 78 / 400)
    (hwidth : (b.ux : ℝ) - b.lx ≤ chi)
    (hchi : chi ≤ e / 10) :
    (gamma 0 b : ℝ) ≤ (gamma e b : ℝ) + e / 20 := by
  have huxmu : (b.ux : ℝ) ≤ mu := by
    dsimp [mu] at *
    linarith
  have hfullE : (b.ux : ℝ) ≤ mu - 4 * e := by
    dsimp [mu] at *
    linarith
  have hfull0 : (b.ux : ℝ) ≤ mu - 4 * (0 : ℝ) := by
    linarith [huxmu]
  have hordered : Ordered (b.ux : ℝ) (b.uy : ℝ) (b.uz : ℝ) := by
    have hz0 : (0 : ℝ) ≤ b.uz := by exact_mod_cast hz.trans hw.2.2
    have hzyR : (b.uz : ℝ) ≤ b.uy := by
      exact_mod_cast hzy.trans hw.2.1
    have hyxR : (b.uy : ℝ) ≤ b.ux := by
      exact_mod_cast hyx.trans hw.1
    exact ⟨hz0, hzyR, hyxR, huxmu⟩
  have hbase : (qVLo b.lx b.ux : ℝ) = A (b.lx : ℝ) := by
    rw [cast_qVLo]
    apply min_eq_left
    have hlx : (b.lx : ℝ) ≤ b.ux := by exact_mod_cast hw.1
    dsimp [A, C, mu] at *
    linarith
  have huxA : v (b.ux : ℝ) = A (b.ux : ℝ) := v_eq_A huxmu
  have hXZLo :
      (qVLo (b.lx + b.lz) (b.ux + b.uz) : ℝ) ≤
        v ((b.ux : ℝ) + b.uz) := by
    apply qVLo_le_v
    · push_cast
      exact_mod_cast add_le_add hw.1 hw.2.2
    · push_cast
      exact le_rfl
  have hYZLo :
      (qVLo (b.ly + b.lz) (b.uy + b.uz) : ℝ) ≤
        v ((b.uy : ℝ) + b.uz) := by
    apply qVLo_le_v
    · push_cast
      exact_mod_cast add_le_add hw.2.1 hw.2.2
    · push_cast
      exact le_rfl
  have hXZNear (hgap : xzGap b < e) :
      (qVLo (b.lx + b.lz) (b.ux + b.uz) : ℝ) ≤
        (qVLo b.lx b.ux : ℝ) + e / 20 := by
    have hnot : ¬v (b.ux : ℝ) ≤ v ((b.ux : ℝ) + b.uz) := by
      intro hwin
      have hm := xz_gate_margin hordered hwin
      change (3 / 256 : ℝ) ≤ xzGap b at hm
      linarith [hm, hgap, hesmall]
    have hlt : v ((b.ux : ℝ) + b.uz) < v (b.ux : ℝ) := lt_of_not_ge hnot
    rw [hbase, huxA] at *
    dsimp [A] at *
    linarith [hXZLo, hlt, hwidth, hchi]
  have hYZNear (hgap : yzGap b < e) :
      (qVLo (b.ly + b.lz) (b.uy + b.uz) : ℝ) ≤
        (qVLo b.lx b.ux : ℝ) + e / 20 := by
    have hnot : ¬v (b.ux : ℝ) ≤ v ((b.uy : ℝ) + b.uz) := by
      intro hwin
      have hm := yz_gate_margin hordered hwin
      change (3 / 256 : ℝ) ≤ yzGap b at hm
      linarith [hm, hgap, hesmall]
    have hlt : v ((b.uy : ℝ) + b.uz) < v (b.ux : ℝ) := lt_of_not_ge hnot
    rw [hbase, huxA] at *
    dsimp [A] at *
    linarith [hYZLo, hlt, hwidth, hchi]
  let G : ℝ := (fullGamma e b : ℝ)
  have hG0 : (qVLo b.lx b.ux : ℝ) ≤ G := by
    exact_mod_cast baseline_le_fullGamma e b
  have hGxy : (qVLo (b.lx + b.ly) (b.ux + b.uy) : ℝ) ≤ G := by
    have h : qVLo (b.lx + b.ly) (b.ux + b.uy) ≤ fullGamma e b := by
      unfold fullGamma
      exact le_max_of_le_right (le_max_left _ _)
    exact_mod_cast h
  have hGxyz :
      (qVLo (b.lx + b.ly + b.lz) (b.ux + b.uy + b.uz) : ℝ) ≤ G := by
    have h : qVLo (b.lx + b.ly + b.lz) (b.ux + b.uy + b.uz) ≤
        fullGamma e b := by
      unfold fullGamma
      exact le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
    exact_mod_cast h
  have hGrescue : (rescue b : ℝ) ≤ G := by
    have h : rescue b ≤ fullGamma e b := by
      unfold fullGamma
      exact le_max_of_le_right (le_max_of_le_right
        (le_max_of_le_right (le_max_left _ _)))
    exact_mod_cast h
  have hGxz (hgate : e ≤ xzGap b) :
      (qVLo (b.lx + b.lz) (b.ux + b.uz) : ℝ) ≤ G := by
    have h : (if e ≤ xzGap b then
        qVLo (b.lx + b.lz) (b.ux + b.uz) else qVLo b.lx b.ux) ≤
        fullGamma e b := by
      unfold fullGamma
      exact le_max_of_le_right (le_max_of_le_right
        (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))))
    rw [if_pos hgate] at h
    exact_mod_cast h
  have hGyz (hgate : e ≤ yzGap b) :
      (qVLo (b.ly + b.lz) (b.uy + b.uz) : ℝ) ≤ G := by
    have h : (if e ≤ yzGap b then
        qVLo (b.ly + b.lz) (b.uy + b.uz) else qVLo b.lx b.ux) ≤
        fullGamma e b := by
      unfold fullGamma
      exact le_max_of_le_right (le_max_of_le_right
        (le_max_of_le_right (le_max_of_le_right (le_max_right _ _))))
    rw [if_pos hgate] at h
    exact_mod_cast h
  have hXZ0 :
      ((if (0 : ℝ) ≤ xzGap b then qVLo (b.lx + b.lz) (b.ux + b.uz)
        else qVLo b.lx b.ux : ℚ) : ℝ) ≤ G + e / 20 := by
    by_cases h0 : (0 : ℝ) ≤ xzGap b
    · rw [if_pos h0]
      by_cases hg : e ≤ xzGap b
      · linarith [hGxz hg, he]
      · linarith [hXZNear (lt_of_not_ge hg), hG0]
    · rw [if_neg h0]
      linarith [hG0, he]
  have hYZ0 :
      ((if (0 : ℝ) ≤ yzGap b then qVLo (b.ly + b.lz) (b.uy + b.uz)
        else qVLo b.lx b.ux : ℚ) : ℝ) ≤ G + e / 20 := by
    by_cases h0 : (0 : ℝ) ≤ yzGap b
    · rw [if_pos h0]
      by_cases hg : e ≤ yzGap b
      · linarith [hGyz hg, he]
      · linarith [hYZNear (lt_of_not_ge hg), hG0]
    · rw [if_neg h0]
      linarith [hG0, he]
  have hfull : (fullGamma 0 b : ℝ) ≤ G + e / 20 := by
    unfold fullGamma
    dsimp only
    simp only [Rat.cast_max, max_le_iff]
    exact ⟨by linarith [hG0, he], by linarith [hGxy, he],
      by linarith [hGxyz, he], by linarith [hGrescue, he], hXZ0, hYZ0⟩
  have hgamma0 : gamma 0 b = fullGamma 0 b := by
    rw [gamma, if_pos hfull0]
  have hgammaE : gamma e b = fullGamma e b := by
    rw [gamma, if_pos hfullE]
  rw [hgamma0, hgammaE]
  exact hfull

/-- Actual decoded grid400/key77 refined third owner. A pair gate may
switch as e varies, but the value of Gamma at e loses at most e/20 from
its zero-buffer value. The q schedule is represented by its exact mesh
step inequality; no branch-decision constancy is assumed. -/
theorem actual_refined_grid400_gamma_zero_le_buffer
    (q : ℕ) (hq : 0 < q) (raw : FifthWireRow)
    (j : Fin 5 → Fin (refinedMesh q + 1)) (e chi : ℝ)
    (he : 0 ≤ e) (hesmall : e ≤ 3 / 51200)
    (hchi : chi ≤ e / 10)
    (hstep : logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ chi)
    (hgrid : raw.grid = 400) (hkey : raw.lo 0 ≤ 77)
    (hcontained : fifthCellContained raw (refinedMesh q) j)
    (hadopted : thirdOwner j ∈ cells e chi (refinedMesh q)) :
    let b := box (refinedMesh q) (thirdOwner j)
    (gamma 0 b : ℝ) ≤ (gamma e b : ℝ) + e / 20 := by
  let b : RationalBox := box (refinedMesh q) (thirdOwner j)
  change (gamma 0 b : ℝ) ≤ (gamma e b : ℝ) + e / 20
  rcases (mem_cells e chi (refinedMesh q) (thirdOwner j)).mp hadopted with
    ⟨hw, hz, hzy, hyx, _hstop, _hwidth⟩
  have hUXRaw : b.ux ≤ raw.upper 0 := by
    simpa [b, box, thirdOwner, historicalPrefixProject] using
      (hcontained (0 : Fin 5)).2
  have hRawBound : raw.upper 0 ≤ (78 / 400 : ℚ) := by
    unfold FifthWireRow.upper
    rw [hgrid]
    have hk : (raw.lo 0 : ℚ) ≤ 77 := by exact_mod_cast hkey
    norm_num at *
    linarith
  have hUX : (b.ux : ℝ) ≤ 78 / 400 := by
    exact_mod_cast hUXRaw.trans hRawBound
  have hLoCast : (b.lx : ℝ) =
      logPrimeMeshLo 0 (19 / 96) (refinedMesh q) (thirdOwner j) 0 := by
    simpa only [b, box] using
      congrFun (cast_qLogPrimeMeshLo 0 (19 / 96) (refinedMesh q) (thirdOwner j)) 0
  have hHiCast : (b.ux : ℝ) =
      logPrimeMeshHi 0 (19 / 96) (refinedMesh q) (thirdOwner j) 0 := by
    simpa only [b, box] using
      congrFun (cast_qLogPrimeMeshHi 0 (19 / 96) (refinedMesh q) (thirdOwner j)) 0
  have hWidth : (b.ux : ℝ) - b.lx ≤ chi := by
    have hm := logPrimeMeshHi_eq_lo_add_step
      (0 : ℝ) (19 / 96 : ℝ) (refinedMesh q) (thirdOwner j) (0 : Fin 3)
    rw [← hHiCast, ← hLoCast] at hm
    linarith [hm, hstep]
  exact gamma_zero_le_buffer_box e chi b he hesmall hw hz hzy hyx
    hUX hWidth hchi

end

end ImbalancedChen.P1OriginalThirdGammaValueStability
