import ImbalancedChen.P5ZU1011BufferedOrdinaryOffKnots

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
Quantitative literal H248 lookup stability off ALL 151 above-clamp walls,
including knot50. The ENTIRE clamp itself is handled separately, so no
claim of absolute lookup stability on that positive-measure cell occurs.
-/

namespace ImbalancedChen.P5Z.BufferedUniformLookup

noncomputable section

open Set Part5UpperTables Part5OriginalUpsilon5CausalDictionary
open U11H248 U1011H248Clamp U1011H248Partition

def Separated (s δ : ℝ) : Prop := ∀ j : Fin 151, δ ≤ |s - floorGrid (50 + j.val)|

/-- A fixed scalar wall margin is a genuine lookup stability radius
above two. This is a quantitative theorem about the ACTUAL partition. -/
theorem lookup_eq_of_separated {s q δ : ℝ} (hs : 2 < s) (hd : 0 < δ)
    (hsep : Separated s δ) (hq : |q - s| < δ) :
    H248 (max 2 q) = H248 (max 2 s) := by
  obtain ⟨state, hstate⟩ := exists_scalarCell s
  cases state with
  | none =>
      have hs5 := (mem_scalarCell_none_iff s).mp hstate
      have h200 := hsep ⟨150, by norm_num⟩
      have hGrid : floorGrid (50 + (⟨150, by norm_num⟩ : Fin 151).val) = 5 := by norm_num [floorGrid]
      rw [hGrid, abs_of_pos (sub_pos.mpr hs5)] at h200
      have hh := (abs_lt.mp hq).1
      have hq5 : 5 < q := by linarith only [hh, h200]
      rw [H248_eq_stateValue ((mem_scalarCell_none_iff q).mpr hq5), H248_eq_stateValue hstate]
  | some atom =>
      cases atom with
      | inr j =>
          change max 2 s ∈ Icc (1 : ℝ) 5 ∧ max 2 s = floorGrid j.val at hstate
          have heq : s = floorGrid j.val := by simpa only [max_eq_right hs.le] using hstate.2
          have hJ : 50 ≤ j.val := by
            have hjReal : (50 : ℝ) < (j.val : ℝ) := by
              dsimp only [floorGrid] at heq
              linarith only [hs, heq]
            have hjNat : 50 < j.val := by exact_mod_cast hjReal
            omega
          let k : Fin 151 := ⟨j.val - 50, by have hh := j.isLt; omega⟩
          have hk : 50 + k.val = j.val := by dsimp only [k]; omega
          have hh := hsep k
          rw [hk, ← heq, sub_self, abs_zero] at hh
          exact (not_le_of_gt hd hh).elim
      | inl i =>
          change max 2 s ∈ Icc (1 : ℝ) 5 ∩
            Ioo (floorGrid i.val) (floorGrid (i.val + 1)) at hstate
          have hOpen : floorGrid i.val < s ∧ s < floorGrid (i.val + 1) := by
            simpa only [max_eq_right hs.le] using hstate.2
          have hI : 50 ≤ i.val := by
            have hiReal : (50 : ℝ) < ((i.val + 1 : ℕ) : ℝ) := by
              have hh := hs.trans hOpen.2
              dsimp only [floorGrid] at hh
              linarith only [hh]
            have hiNat : 50 < i.val + 1 := by exact_mod_cast hiReal
            omega
          let left : Fin 151 := ⟨i.val - 50, by have hh := i.isLt; omega⟩
          let right : Fin 151 := ⟨i.val + 1 - 50, by have hh := i.isLt; omega⟩
          have hLidx : 50 + left.val = i.val := by dsimp only [left]; omega
          have hUidx : 50 + right.val = i.val + 1 := by dsimp only [right]; omega
          have hL := hsep left
          have hU := hsep right
          rw [hLidx, abs_of_pos (sub_pos.mpr hOpen.1)] at hL
          rw [hUidx, abs_of_neg (sub_neg.mpr hOpen.2)] at hU
          have hLower := (abs_lt.mp hq).1
          have hUpper := (abs_lt.mp hq).2
          have hqLo : floorGrid i.val < q := by linarith only [hLower, hL]
          have hqHi : q < floorGrid (i.val + 1) := by linarith only [hUpper, hU]
          have hg2 : 2 ≤ floorGrid i.val := by
            have hiReal : (50 : ℝ) ≤ (i.val : ℝ) := by exact_mod_cast hI
            dsimp only [floorGrid]
            linarith only [hiReal]
          have hg5 : floorGrid (i.val + 1) ≤ 5 := by
            have hiNat : i.val + 1 ≤ 200 := by have hh := i.isLt; omega
            have hiReal : ((i.val + 1 : ℕ) : ℝ) ≤ 200 := by exact_mod_cast hiNat
            dsimp only [floorGrid]
            linarith only [hiReal]
          have hq2 : 2 ≤ q := hg2.trans hqLo.le
          have hqState : q ∈ scalarCell (some (.inl i)) := by
            change max 2 q ∈ Icc (1 : ℝ) 5 ∩ Ioo (floorGrid i.val) (floorGrid (i.val + 1))
            rw [max_eq_right hq2]
            exact ⟨⟨(by norm_num : (1 : ℝ) ≤ 2).trans hq2, hqHi.le.trans hg5⟩, hqLo, hqHi⟩
          rw [H248_eq_stateValue hqState]
          have hsState : s ∈ scalarCell (some (.inl i)) := hstate
          rw [H248_eq_stateValue hsState]

/-- Physical affine wall separation implies scalar separation on the
actual compact w<=1. No cell lookup conclusion is a hypothesis. -/
theorem separated_of_affine_walls {R w δ : ℝ} (hw : 0 < w) (hw1 : w ≤ 1)
    (hwall : ∀ j : Fin 151, δ ≤ |R - floorGrid (50 + j.val) * w|) :
    Separated (R / w) δ := by
  intro j
  have heq : R - floorGrid (50 + j.val) * w = w * (R / w - floorGrid (50 + j.val)) := by
    field_simp [hw.ne']
    <;> ring
  have hh := hwall j
  rw [heq, abs_mul, abs_of_pos hw] at hh
  have hprod := mul_le_mul_of_nonneg_right hw1 (abs_nonneg (R / w - floorGrid (50 + j.val)))
  simpa only [one_mul] using hh.trans hprod

end

end ImbalancedChen.P5Z.BufferedUniformLookup
