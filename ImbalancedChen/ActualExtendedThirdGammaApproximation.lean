import ImbalancedChen.ActualExtendedThirdDyadicCoverage

/-!
# Quantitative approximation by the actual robust extended-third caps

The infima are those of the actual closed ordered dyadic portions. Scalar
regularity is supplied by the existing global `3/2` Lipschitz theorem for v.
The two pair gate errors are at most seven mesh widths. A pair that can win
against the baseline has the already proved positive gate margin `3/256`,
so a sufficiently fine actual grid admits it robustly. Losing pairs are
absorbed by the actual baseline; no gated function is treated as continuous.

This file proves a scalar coarse-cap approximation. Choosing the physical
factorization action and evaluating its same-policy arithmetic mean remain
separate obligations.
-/

namespace ImbalancedChen

noncomputable section

open Set Filter Topology
open VariableEnvelope
open scoped Classical

theorem actualExtendedThirdPhysicalCell_coordinate_error {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m} {s t : Fin 3 → ℝ}
    (hs : s ∈ actualExtendedThirdPhysicalCell m j)
    (ht : t ∈ actualExtendedThirdPhysicalCell m j) (i : Fin 3) :
    |s i - t i| ≤ actualExtendedThirdDyadicStep m := by
  simpa only [Real.dist_eq] using
    (dist_le_pi_dist s t i).trans (actualExtendedThirdPhysicalCell_dist_le_step hs ht)

private theorem sum_error {a b c d χ : ℝ} (ha : |a - b| ≤ χ) (hc : |c - d| ≤ χ) :
    |(a + c) - (b + d)| ≤ 2 * χ := by
  obtain ⟨ha₁, ha₂⟩ := abs_le.mp ha
  obtain ⟨hc₁, hc₂⟩ := abs_le.mp hc
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private theorem inf_ge {m : ℕ} {j : ActualExtendedThirdDyadicLabel m}
    {f : (Fin 3 → ℝ) → ℝ} {c : ℝ} {t : Fin 3 → ℝ}
    (ht : t ∈ actualExtendedThirdPhysicalCell m j)
    (hf : ∀ s ∈ actualExtendedThirdPhysicalCell m j, c ≤ f s) :
    c ≤ actualExtendedThirdCellInf m j f := by
  apply le_csInf ((show (actualExtendedThirdPhysicalCell m j).Nonempty from ⟨t, ht⟩).image _)
  rintro _ ⟨s, hs, rfl⟩
  exact hf s hs

theorem actualExtendedThirdBaselineInf_lower {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m} {t : Fin 3 → ℝ}
    (ht : t ∈ actualExtendedThirdPhysicalCell m j) :
    v (t 0) - (3 / 2 : ℝ) * actualExtendedThirdDyadicStep m ≤
      actualExtendedThirdCellInf m j (actualExtendedThirdRobustBaseBranch 0) := by
  apply inf_ge ht
  intro s hs
  change v (t 0) - (3 / 2 : ℝ) * actualExtendedThirdDyadicStep m ≤ v (s 0)
  have h := (abs_le.mp (v_abs_sub_le_of_le
    (actualExtendedThirdPhysicalCell_coordinate_error hs ht 0))).1
  linarith

private theorem prefixInf_lower {m : ℕ} {j : ActualExtendedThirdDyadicLabel m}
    {t : Fin 3 → ℝ} (ht : t ∈ actualExtendedThirdPhysicalCell m j) :
    v (t 0 + t 1) - (9 / 2 : ℝ) * actualExtendedThirdDyadicStep m ≤
      actualExtendedThirdCellInf m j (actualExtendedThirdRobustBaseBranch 2) ∧
    v (t 0 + t 1 + t 2) - (9 / 2 : ℝ) * actualExtendedThirdDyadicStep m ≤
      actualExtendedThirdCellInf m j (actualExtendedThirdRobustBaseBranch 3) := by
  have hχ := (actualExtendedThirdDyadicStep_pos m).le
  constructor
  · apply inf_ge ht
    intro s hs
    change v (t 0 + t 1) - (9 / 2 : ℝ) * actualExtendedThirdDyadicStep m ≤ v (s 0 + s 1)
    have hab := sum_error (actualExtendedThirdPhysicalCell_coordinate_error hs ht 0)
      (actualExtendedThirdPhysicalCell_coordinate_error hs ht 1)
    have hv := (abs_le.mp (v_abs_sub_le_of_le hab)).1
    linarith
  · apply inf_ge ht
    intro s hs
    change v (t 0 + t 1 + t 2) - (9 / 2 : ℝ) * actualExtendedThirdDyadicStep m ≤
      v (s 0 + s 1 + s 2)
    have hxy := abs_le.mp (sum_error (actualExtendedThirdPhysicalCell_coordinate_error hs ht 0)
      (actualExtendedThirdPhysicalCell_coordinate_error hs ht 1))
    have hz := abs_le.mp (actualExtendedThirdPhysicalCell_coordinate_error hs ht 2)
    have hab : |(s 0 + s 1 + s 2) - (t 0 + t 1 + t 2)| ≤
        3 * actualExtendedThirdDyadicStep m := abs_le.mpr ⟨by linarith [hxy.1, hz.1],
          by linarith [hxy.2, hz.2]⟩
    have hv := (abs_le.mp (v_abs_sub_le_of_le hab)).1
    linarith

private theorem rescueInf_lower {m : ℕ} {j : ActualExtendedThirdDyadicLabel m}
    {t : Fin 3 → ℝ} (ht : t ∈ actualExtendedThirdPhysicalCell m j)
    (hmu : actualExtendedThirdDyadicHi m j 0 ≤ mu) :
    B (t 2) - (9 / 2 : ℝ) * actualExtendedThirdDyadicStep m ≤
      actualExtendedThirdCellInf m j (actualExtendedThirdRobustBaseBranch 4) := by
  apply inf_ge ht
  intro s hs
  have hsy : s 1 ≤ mu := hs.2.2.2.trans ((hs.1 0 (mem_univ _)).2.trans hmu)
  change B (t 2) - (9 / 2 : ℝ) * actualExtendedThirdDyadicStep m ≤
    max (v (s 0)) (wInner (s 0) (s 1) (s 2))
  rw [wInner_eq_B (s 0) hsy hs.2.1]
  apply le_max_of_le_right
  have hz := (abs_le.mp (actualExtendedThirdPhysicalCell_coordinate_error hs ht 2)).2
  have hχ := (actualExtendedThirdDyadicStep_pos m).le
  dsimp [B]
  linarith

theorem actualExtendedThirdPairXZInf_lower {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m} {t : Fin 3 → ℝ}
    (ht : t ∈ actualExtendedThirdPhysicalCell m j) :
    actualExtendedThirdPairXZ t - 3 * actualExtendedThirdDyadicStep m ≤
      actualExtendedThirdCellInf m j actualExtendedThirdPairXZ := by
  apply inf_ge ht
  intro s hs
  have hab := sum_error (actualExtendedThirdPhysicalCell_coordinate_error hs ht 0)
    (actualExtendedThirdPhysicalCell_coordinate_error hs ht 2)
  have hv := (abs_le.mp (v_abs_sub_le_of_le hab)).1
  dsimp [actualExtendedThirdPairXZ]
  linarith

theorem actualExtendedThirdPairYZInf_lower {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m} {t : Fin 3 → ℝ}
    (ht : t ∈ actualExtendedThirdPhysicalCell m j) :
    actualExtendedThirdPairYZ t - 3 * actualExtendedThirdDyadicStep m ≤
      actualExtendedThirdCellInf m j actualExtendedThirdPairYZ := by
  apply inf_ge ht
  intro s hs
  have hab := sum_error (actualExtendedThirdPhysicalCell_coordinate_error hs ht 1)
    (actualExtendedThirdPhysicalCell_coordinate_error hs ht 2)
  have hv := (abs_le.mp (v_abs_sub_le_of_le hab)).1
  dsimp [actualExtendedThirdPairYZ]
  linarith

theorem actualExtendedThirdGateXZInf_lower {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m} {t : Fin 3 → ℝ}
    (ht : t ∈ actualExtendedThirdPhysicalCell m j) :
    actualExtendedThirdGateXZ t - 7 * actualExtendedThirdDyadicStep m ≤
      actualExtendedThirdCellInf m j actualExtendedThirdGateXZ := by
  apply inf_ge ht
  intro s hs
  have hab := sum_error (actualExtendedThirdPhysicalCell_coordinate_error hs ht 0)
    (actualExtendedThirdPhysicalCell_coordinate_error hs ht 2)
  have hv := (abs_le.mp (v_abs_sub_le_of_le hab)).1
  have hx := (abs_le.mp (actualExtendedThirdPhysicalCell_coordinate_error hs ht 0)).2
  have hy := (abs_le.mp (actualExtendedThirdPhysicalCell_coordinate_error hs ht 1)).2
  have hz := (abs_le.mp (actualExtendedThirdPhysicalCell_coordinate_error hs ht 2)).2
  dsimp [actualExtendedThirdGateXZ, actualExtendedThirdPairXZ]
  linarith

theorem actualExtendedThirdGateYZInf_lower {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m} {t : Fin 3 → ℝ}
    (ht : t ∈ actualExtendedThirdPhysicalCell m j) :
    actualExtendedThirdGateYZ t - 7 * actualExtendedThirdDyadicStep m ≤
      actualExtendedThirdCellInf m j actualExtendedThirdGateYZ := by
  apply inf_ge ht
  intro s hs
  have hab := sum_error (actualExtendedThirdPhysicalCell_coordinate_error hs ht 1)
    (actualExtendedThirdPhysicalCell_coordinate_error hs ht 2)
  have hv := (abs_le.mp (v_abs_sub_le_of_le hab)).1
  have hx := (abs_le.mp (actualExtendedThirdPhysicalCell_coordinate_error hs ht 0)).2
  have hy := (abs_le.mp (actualExtendedThirdPhysicalCell_coordinate_error hs ht 1)).2
  have hz := (abs_le.mp (actualExtendedThirdPhysicalCell_coordinate_error hs ht 2)).2
  dsimp [actualExtendedThirdGateYZ, actualExtendedThirdPairYZ]
  linarith

/-- A pointwise winning pair is admitted by the actual whole-cell robust
test, because its actual gate has the verified uniform positive surplus. -/
theorem actualExtendedThirdWinningPairs_admitted {e : ℝ} {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m} {t : Fin 3 → ℝ}
    (ht : t ∈ actualExtendedThirdPhysicalCell m j) (ho : Ordered (t 0) (t 1) (t 2))
    (hfine : e + 7 * actualExtendedThirdDyadicStep m ≤ 3 / 256) :
    (v (t 0) ≤ v (t 0 + t 2) → e ≤ actualExtendedThirdCellInf m j actualExtendedThirdGateXZ) ∧
    (v (t 0) ≤ v (t 1 + t 2) → e ≤ actualExtendedThirdCellInf m j actualExtendedThirdGateYZ) := by
  constructor
  · intro hwin
    have hmargin : 3 / 256 ≤ actualExtendedThirdGateXZ t := xz_gate_margin ho hwin
    have hinf := actualExtendedThirdGateXZInf_lower ht
    linarith
  · intro hwin
    have hmargin : 3 / 256 ≤ actualExtendedThirdGateYZ t := yz_gate_margin ho hwin
    have hinf := actualExtendedThirdGateYZInf_lower ht
    linarith

private theorem fullGamma_ge_base (e : ℝ) (m : ℕ)
    (j : ActualExtendedThirdDyadicLabel m) (k : Fin 6) :
    actualExtendedThirdCellInf m j (actualExtendedThirdRobustBaseBranch k) ≤
      actualExtendedThirdFullGamma e m j := by
  fin_cases k <;> simp [actualExtendedThirdFullGamma]

private theorem fullGamma_ge_pairXZ {e : ℝ} {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m}
    (hg : e ≤ actualExtendedThirdCellInf m j actualExtendedThirdGateXZ) :
    actualExtendedThirdCellInf m j actualExtendedThirdPairXZ ≤ actualExtendedThirdFullGamma e m j := by
  simp [actualExtendedThirdFullGamma, hg]

private theorem fullGamma_ge_pairYZ {e : ℝ} {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m}
    (hg : e ≤ actualExtendedThirdCellInf m j actualExtendedThirdGateYZ) :
    actualExtendedThirdCellInf m j actualExtendedThirdPairYZ ≤ actualExtendedThirdFullGamma e m j := by
  simp [actualExtendedThirdFullGamma, hg]

/-- Actual robust full caps approximate the true six-branch value uniformly
over every closed ordered portion, including portions meeting ordering walls. -/
theorem actualExtendedThirdFullGamma_error {e : ℝ} {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m} {t : Fin 3 → ℝ}
    (ht : t ∈ actualExtendedThirdPhysicalCell m j)
    (hmu : actualExtendedThirdDyadicHi m j 0 ≤ mu)
    (hfine : e + 7 * actualExtendedThirdDyadicStep m ≤ 3 / 256) :
    0 ≤ six (t 0) (t 1) (t 2) - actualExtendedThirdFullGamma e m j ∧
      six (t 0) (t 1) (t 2) - actualExtendedThirdFullGamma e m j ≤
        (9 / 2 : ℝ) * actualExtendedThirdDyadicStep m := by
  have ho : Ordered (t 0) (t 1) (t 2) :=
    ⟨ht.2.1, ht.2.2.1, ht.2.2.2, (ht.1 0 (mem_univ _)).2.trans hmu⟩
  have hle := actualExtendedThirdFullGamma_le_original (e := e) ht ho
  rw [original_eq_six ho] at hle
  have hχ := (actualExtendedThirdDyadicStep_pos m).le
  have hbase := (actualExtendedThirdBaselineInf_lower ht).trans (fullGamma_ge_base e m j 0)
  have hprefix := prefixInf_lower ht
  have hxy := hprefix.1.trans (fullGamma_ge_base e m j 2)
  have hxyz := hprefix.2.trans (fullGamma_ge_base e m j 3)
  have hB := (rescueInf_lower ht hmu).trans (fullGamma_ge_base e m j 4)
  have hp := actualExtendedThirdWinningPairs_admitted ht ho hfine
  have hxz : v (t 0 + t 2) ≤ actualExtendedThirdFullGamma e m j +
      (9 / 2 : ℝ) * actualExtendedThirdDyadicStep m := by
    by_cases hwin : v (t 0) ≤ v (t 0 + t 2)
    · have hb := (actualExtendedThirdPairXZInf_lower ht).trans (fullGamma_ge_pairXZ (hp.1 hwin))
      dsimp [actualExtendedThirdPairXZ] at hb
      linarith
    · have hh := lt_of_not_ge hwin
      linarith
  have hyz : v (t 1 + t 2) ≤ actualExtendedThirdFullGamma e m j +
      (9 / 2 : ℝ) * actualExtendedThirdDyadicStep m := by
    by_cases hwin : v (t 0) ≤ v (t 1 + t 2)
    · have hb := (actualExtendedThirdPairYZInf_lower ht).trans (fullGamma_ge_pairYZ (hp.2 hwin))
      dsimp [actualExtendedThirdPairYZ] at hb
      linarith
    · have hh := lt_of_not_ge hwin
      linarith
  have hsix : six (t 0) (t 1) (t 2) ≤ actualExtendedThirdFullGamma e m j +
      (9 / 2 : ℝ) * actualExtendedThirdDyadicStep m := by
    unfold six
    exact max_le (by linarith) (max_le (by linarith) (max_le (by linarith)
      (max_le (by linarith) (max_le hxz hyz))))
  exact ⟨sub_nonneg.mpr hle, by linarith⟩

/-- The actual endpoint dispatch localizes every omitted full-envelope cell
below mu to an explicit strip, rather than assuming a null transition wall. -/
theorem actualExtendedThirdFallback_in_transition_strip {e : ℝ} {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m} {t : Fin 3 → ℝ}
    (ht : t ∈ actualExtendedThirdPhysicalCell m j)
    (hfallback : ¬actualExtendedThirdDyadicHi m j 0 ≤ mu - 4 * e)
    (hx : t 0 ≤ mu) :
    mu - 4 * e - actualExtendedThirdDyadicStep m < t 0 ∧ t 0 ≤ mu := by
  have hhi := actualExtendedThirdDyadicHi_le_point_add_step ht 0
  exact ⟨by linarith [lt_of_not_ge hfallback], hx⟩

/-- Above mu both the ideal envelope and the actual coarse dispatch use v.
The proof pays that dispatch from the true upper endpoint and e >= 0. -/
theorem actualExtendedThirdPhysicalGamma_above_mu_error {e : ℝ} {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m} {t : Fin 3 → ℝ}
    (he : 0 ≤ e) (ht : t ∈ actualExtendedThirdPhysicalCell m j) (hx : mu < t 0) :
    0 ≤ actualExtendedThirdEnvelope (t 0) (t 1) (t 2) - actualExtendedThirdPhysicalGamma e m j ∧
      actualExtendedThirdEnvelope (t 0) (t 1) (t 2) - actualExtendedThirdPhysicalGamma e m j ≤
        (3 / 2 : ℝ) * actualExtendedThirdDyadicStep m := by
  have hhi := (ht.1 0 (mem_univ _)).2
  have hfallback : ¬actualExtendedThirdDyadicHi m j 0 ≤ mu - 4 * e := by linarith
  rw [actualExtendedThirdPhysicalGamma, if_neg hfallback,
    actualExtendedThirdEnvelope, if_neg (not_le.mpr hx)]
  have hl := actualExtendedThirdBaselineInf_lower ht
  have hu : actualExtendedThirdCellInf m j (actualExtendedThirdRobustBaseBranch 0) ≤ v (t 0) :=
    actualExtendedThirdCellInf_le (continuous_actualExtendedThirdRobustBaseBranch 0) ht
  exact ⟨sub_nonneg.mpr hu, by linarith⟩

/-- The robust buffered cap converges to the literal ideal cap away from the
explicit transition strip. Every assumption is a concrete mesh/wall condition;
no closeness property of an unspecified selector is supplied. -/
theorem actualExtendedThirdPhysicalLevel_error {e : ℝ} {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m} {t : Fin 3 → ℝ}
    (he : 0 ≤ e) (ht : t ∈ actualExtendedThirdPhysicalCell m j)
    (hfine : e + 7 * actualExtendedThirdDyadicStep m ≤ 3 / 256)
    (hwall : actualExtendedThirdDyadicHi m j 0 ≤ mu - 4 * e ∨ mu < t 0) :
    0 ≤ actualExtendedThirdIdealCap (t 0) (t 1) (t 2) - actualExtendedThirdPhysicalLevel e m j ∧
      actualExtendedThirdIdealCap (t 0) (t 1) (t 2) - actualExtendedThirdPhysicalLevel e m j ≤
        2 * e + (9 / 2 : ℝ) * actualExtendedThirdDyadicStep m := by
  have hχ := (actualExtendedThirdDyadicStep_pos m).le
  have hg : actualExtendedThirdEnvelope (t 0) (t 1) (t 2) -
      actualExtendedThirdPhysicalGamma e m j ≤ (9 / 2 : ℝ) * actualExtendedThirdDyadicStep m := by
    rcases hwall with hfull | hx
    · have hmu : actualExtendedThirdDyadicHi m j 0 ≤ mu := by linarith
      have hxmu := (ht.1 0 (mem_univ _)).2.trans hmu
      have ho : Ordered (t 0) (t 1) (t 2) := ⟨ht.2.1, ht.2.2.1, ht.2.2.2, hxmu⟩
      rw [actualExtendedThirdPhysicalGamma, if_pos hfull, actualExtendedThirdEnvelope_eq_six ho]
      exact (actualExtendedThirdFullGamma_error ht hmu hfine).2
    · have hh := (actualExtendedThirdPhysicalGamma_above_mu_error he ht hx).2
      linarith
  have hLtheta : actualExtendedThirdIdealCap (t 0) (t 1) (t 2) ≤ thirdPrefixTheta := by
    rw [actualExtendedThirdIdealCap_eq]
    exact min_le_left _ _
  have hLA : actualExtendedThirdIdealCap (t 0) (t 1) (t 2) ≤
      actualExtendedThirdEnvelope (t 0) (t 1) (t 2) := by
    rw [actualExtendedThirdIdealCap_eq]
    exact min_le_right _ _
  have hlower : actualExtendedThirdIdealCap (t 0) (t 1) (t 2) -
      (2 * e + (9 / 2 : ℝ) * actualExtendedThirdDyadicStep m) ≤
        actualExtendedThirdPhysicalLevel e m j := by
    unfold actualExtendedThirdPhysicalLevel thirdPrefixBufferedCap
    exact le_min (by linarith) (by linarith)
  exact ⟨sub_nonneg.mpr (actualExtendedThirdPhysicalLevel_le_ideal he ht), by linarith⟩

end

end ImbalancedChen
