import ImbalancedChen.ActualExtendedThirdDyadicCoverage
import ImbalancedChen.ActualExtendedThirdLowerFactorRegularity

/-!
# The actual finite robust-cap lookup and its canonical kernel

The finite policy reads only the genuine retained dyadic Ico owners. Each
owned cell receives its actual physical lambda; outside the retained union
the third level is the old level, giving zero third correction. Uniqueness
and measurability are proved for this lookup, rather than supplied as data.

This analytic kernel is not yet an arithmetic density asymptotic or a
factorization action. The nested tail below is the canonical Core tail with
this exact finite lookup substituted. Its tuple-space Tonelli identification
is not asserted by this file.
-/

namespace ImbalancedChen

noncomputable section

open Set Filter Topology MeasureTheory
open VariableEnvelope
open scoped Classical BigOperators ENNReal

def actualExtendedThirdFiniteLevel (e : ℝ) (m : ℕ) (t : Fin 3 → ℝ) : ℝ :=
  thirdPrefixTheta - 2 * e + ∑ j ∈ actualExtendedThirdRetainedCells e m,
    if t ∈ actualExtendedThirdOwnedCell m j then
      actualExtendedThirdPhysicalLevel e m j - (thirdPrefixTheta - 2 * e) else 0

theorem actualExtendedThirdFiniteLevel_on_cell {e : ℝ} {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m} (hj : j ∈ actualExtendedThirdRetainedCells e m)
    {t : Fin 3 → ℝ} (ht : t ∈ actualExtendedThirdOwnedCell m j) :
    actualExtendedThirdFiniteLevel e m t = actualExtendedThirdPhysicalLevel e m j := by
  unfold actualExtendedThirdFiniteLevel
  rw [Finset.sum_eq_single_of_mem j hj]
  · rw [if_pos ht]
    ring
  · intro k _hk hkj
    apply if_neg
    intro htk
    exact hkj (actualExtendedThirdOwnedCell_unique htk ht)

theorem actualExtendedThirdFiniteLevel_outside {e : ℝ} {m : ℕ} {t : Fin 3 → ℝ}
    (ht : ∀ j ∈ actualExtendedThirdRetainedCells e m, t ∉ actualExtendedThirdOwnedCell m j) :
    actualExtendedThirdFiniteLevel e m t = thirdPrefixTheta - 2 * e := by
  unfold actualExtendedThirdFiniteLevel
  rw [Finset.sum_eq_zero (fun j hj => if_neg (ht j hj)), add_zero]

theorem measurable_actualExtendedThirdFiniteLevel (e : ℝ) (m : ℕ) :
    Measurable (actualExtendedThirdFiniteLevel e m) := by
  apply measurable_const.add
  apply Finset.measurable_sum
  intro j _hj
  exact measurable_const.piecewise (measurableSet_actualExtendedThirdOwnedCell m j) measurable_const

theorem actualExtendedThirdFiniteLevel_le_root (e : ℝ) (m : ℕ) (t : Fin 3 → ℝ) :
    actualExtendedThirdFiniteLevel e m t ≤ thirdPrefixTheta - 2 * e := by
  by_cases hj : ∃ j ∈ actualExtendedThirdRetainedCells e m, t ∈ actualExtendedThirdOwnedCell m j
  · obtain ⟨j, hj, ht⟩ := hj
    rw [actualExtendedThirdFiniteLevel_on_cell hj ht]
    exact thirdPrefixBufferedCap_le_root _ _
  · have hout : ∀ j ∈ actualExtendedThirdRetainedCells e m,
        t ∉ actualExtendedThirdOwnedCell m j := by
      intro j hj' ht
      exact hj ⟨j, hj', ht⟩
    rw [actualExtendedThirdFiniteLevel_outside hout]

/-- The actual finite lookup has the same residual margin at every ordered
point, including the inherited old-level region outside all retained cells. -/
theorem actualExtendedThirdFiniteLevel_tail_geometry {e : ℝ} {m : ℕ}
    (he0 : 0 ≤ e) (he : e ≤ 1 / 384) {t : Fin 3 → ℝ}
    (ht : t ∈ actualExtendedThirdClosedOrder) (hx : t 0 ≤ thirdPrefixRho) :
    thirdPrefixTailMargin ≤ actualExtendedThirdFiniteLevel e m t - t 0 - t 1 := by
  by_cases hj : ∃ j ∈ actualExtendedThirdRetainedCells e m, t ∈ actualExtendedThirdOwnedCell m j
  · obtain ⟨j, hj, htj⟩ := hj
    rw [actualExtendedThirdFiniteLevel_on_cell hj htj]
    exact (actualExtendedThirdPhysicalLevel_tail_geometry he0 he hj
      (actualExtendedThirdOwnedCell_subset_physicalCell m j htj)).1
  · have hout : ∀ j ∈ actualExtendedThirdRetainedCells e m,
        t ∉ actualExtendedThirdOwnedCell m j := by
      intro j hj' htj
      exact hj ⟨j, hj', htj⟩
    rw [actualExtendedThirdFiniteLevel_outside hout]
    have hy : t 1 ≤ thirdPrefixRho := ht.2.2.trans hx
    dsimp [thirdPrefixTailMargin, thirdPrefixTheta, thirdPrefixRho] at *
    linarith

def actualExtendedThirdCapKernel (e λ x y z : ℝ) : ℝ :=
  4 * (actualExtendedThirdLowerFactor ((thirdPrefixTheta - 2 * e - x - y - z) / z) -
    actualExtendedThirdLowerFactor ((λ - x - y - z) / z)) / (x * y * z ^ 2)

def actualExtendedThirdCompactKernelBound (h : ℝ) : ℝ :=
  (4 * (1 / (2 * Real.exp Real.eulerMascheroniConstant))) / h ^ 4

theorem actualExtendedThirdCompactKernelBound_pos {h : ℝ} (hh : 0 < h) :
    0 < actualExtendedThirdCompactKernelBound h := by
  unfold actualExtendedThirdCompactKernelBound
  positivity

/-- The true zero-extended factor is bounded globally, so this compact bound
does not need a cube-gate or a prior integrability assumption. -/
theorem actualExtendedThirdCapKernel_abs_le {e λ x y z h : ℝ} (hh : 0 < h)
    (hx : h ≤ x) (hy : h ≤ y) (hz : h ≤ z) :
    |actualExtendedThirdCapKernel e λ x y z| ≤ actualExtendedThirdCompactKernelBound h := by
  let M : ℝ := 1 / (2 * Real.exp Real.eulerMascheroniConstant)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hx0 : 0 < x := hh.trans_le hx
  have hy0 : 0 < y := hh.trans_le hy
  have hz0 : 0 < z := hh.trans_le hz
  have hd : 0 < x * y * z ^ 2 := by positivity
  have hxy : h * h ≤ x * y := mul_le_mul hx hy hh.le hx0.le
  have hz2 : h ^ 2 ≤ z ^ 2 := pow_le_pow_left₀ hh.le hz 2
  have hden : h ^ 4 ≤ x * y * z ^ 2 := by
    calc
      h ^ 4 = (h * h) * h ^ 2 := by ring
      _ ≤ (x * y) * z ^ 2 := mul_le_mul hxy hz2 (sq_nonneg _) (by positivity)
  have hdiff : |actualExtendedThirdLowerFactor ((thirdPrefixTheta - 2 * e - x - y - z) / z) -
      actualExtendedThirdLowerFactor ((λ - x - y - z) / z)| ≤ M := by
    have ha0 := actualExtendedThirdLowerFactor_nonneg
      ((thirdPrefixTheta - 2 * e - x - y - z) / z)
    have hb0 := actualExtendedThirdLowerFactor_nonneg ((λ - x - y - z) / z)
    have ha := actualExtendedThirdLowerFactor_le_normalization
      ((thirdPrefixTheta - 2 * e - x - y - z) / z)
    have hb := actualExtendedThirdLowerFactor_le_normalization ((λ - x - y - z) / z)
    change _ ≤ M at ha hb
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  unfold actualExtendedThirdCapKernel actualExtendedThirdCompactKernelBound
  rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4), abs_of_pos hd]
  apply le_trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hdiff (by norm_num)) hd.le)
  change 4 * M / (x * y * z ^ 2) ≤ 4 * M / h ^ 4
  exact (div_le_div_iff₀ hd (pow_pos hh 4)).mpr (mul_le_mul_of_nonneg_left hden (by positivity))

def actualExtendedThirdFiniteKernel (e : ℝ) (m : ℕ) (t : Fin 3 → ℝ) : ℝ :=
  actualExtendedThirdCapKernel e (actualExtendedThirdFiniteLevel e m t) (t 0) (t 1) (t 2)

theorem measurable_actualExtendedThirdFiniteKernel (e : ℝ) (m : ℕ) :
    Measurable (actualExtendedThirdFiniteKernel e m) := by
  have hx : Measurable (fun t : Fin 3 → ℝ => t 0) := (continuous_apply 0).measurable
  have hy : Measurable (fun t : Fin 3 → ℝ => t 1) := (continuous_apply 1).measurable
  have hz : Measurable (fun t : Fin 3 → ℝ => t 2) := (continuous_apply 2).measurable
  have hold : Measurable (fun t : Fin 3 → ℝ =>
      (thirdPrefixTheta - 2 * e - t 0 - t 1 - t 2) / t 2) :=
    (((measurable_const.sub hx).sub hy).sub hz).div hz
  have hnew : Measurable (fun t : Fin 3 → ℝ =>
      (actualExtendedThirdFiniteLevel e m t - t 0 - t 1 - t 2) / t 2) :=
    ((((measurable_actualExtendedThirdFiniteLevel e m).sub hx).sub hy).sub hz).div hz
  unfold actualExtendedThirdFiniteKernel actualExtendedThirdCapKernel
  exact (measurable_const.mul
    ((measurable_actualExtendedThirdLowerFactor.comp hold).sub
      (measurable_actualExtendedThirdLowerFactor.comp hnew))).div
        ((hx.mul hy).mul (hz.pow_const 2))

theorem actualExtendedThirdFiniteKernel_abs_le {e h : ℝ} {m : ℕ} (hh : 0 < h)
    {t : Fin 3 → ℝ} (hx : h ≤ t 0) (hy : h ≤ t 1) (hz : h ≤ t 2) :
    |actualExtendedThirdFiniteKernel e m t| ≤ actualExtendedThirdCompactKernelBound h :=
  actualExtendedThirdCapKernel_abs_le hh hx hy hz

theorem actualExtendedThirdGatedKernel_abs_le {e h : ℝ} (hh : 0 < h)
    {t : Fin 3 → ℝ} (hx : h ≤ t 0) (hy : h ≤ t 1) (hz : h ≤ t 2) :
    |actualExtendedThirdGatedKernel e (t 0) (t 1) (t 2)| ≤
      actualExtendedThirdCompactKernelBound h := by
  unfold actualExtendedThirdGatedKernel
  split_ifs
  · exact actualExtendedThirdCapKernel_abs_le hh hx hy hz
  · simpa only [abs_zero] using (actualExtendedThirdCompactKernelBound_pos hh).le

/-- This actual constructor consumes the previously proved canonical tail
bound uniformly over the entire finite mesh, with no assumed selector floor. -/
def actualExtendedThirdFiniteNestedTailMass (e : ℝ) (m : ℕ) (h : ℝ) : ℝ≥0∞ :=
  thirdPrefixTailMass (thirdPrefixTheta - 2 * e)
    (fun x y z => actualExtendedThirdFiniteLevel e m ![x, y, z]) thirdPrefixRho h

theorem actualExtendedThirdFiniteNestedTailMass_le {e h : ℝ} {m : ℕ}
    (he0 : 0 ≤ e) (he : e ≤ 1 / 384) (hh : 0 < h)
    (hsmall : h ≤ thirdPrefixTailMargin / 4) :
    actualExtendedThirdFiniteNestedTailMass e m h ≤
      ENNReal.ofReal (18 * h / (thirdPrefixTailMargin - h) ^ 2 *
        (Real.log (thirdPrefixRho / h) ^ 2 + 2 * Real.log (thirdPrefixRho / h) + 2)) := by
  apply thirdPrefixTailMass_le_eighteen hh hsmall
  intro x y z hz _hzh hzy hyx hx
  have ht : ![x, y, z] ∈ actualExtendedThirdClosedOrder := by
    simp only [actualExtendedThirdClosedOrder, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two]
    exact ⟨hz.le, hzy, hyx⟩
  have hmargin := actualExtendedThirdFiniteLevel_tail_geometry (m := m) he0 he ht
    (by simpa only [Matrix.cons_val_zero] using hx)
  have hroot := actualExtendedThirdFiniteLevel_le_root e m ![x, y, z]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hmargin
  exact ⟨hmargin, hroot⟩

/-- The small cutoff is chosen before the buffer and mesh. The genuine
canonical tail estimate is uniform over every actual finite lookup here. -/
theorem actualExtendedThirdFiniteNestedTailMass_uniform_small {ε : ℝ} (hε : 0 < ε) :
    ∃ h : ℝ, 0 < h ∧ h ≤ thirdPrefixTailMargin / 4 ∧
      ∀ e : ℝ, 0 ≤ e → e ≤ 1 / 384 → ∀ m : ℕ,
        actualExtendedThirdFiniteNestedTailMass e m h ≤ ENNReal.ofReal ε := by
  have hupper : Tendsto (fun h : ℝ => ENNReal.ofReal
      (18 * h / (thirdPrefixTailMargin - h) ^ 2 *
        (Real.log (thirdPrefixRho / h) ^ 2 +
          2 * Real.log (thirdPrefixRho / h) + 2)))
      (𝓝[>] 0) (𝓝 (0 : ℝ≥0∞)) := by
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal
      (tendsto_roughActivationTailEnvelope_zero
        (a := thirdPrefixRho) (c := thirdPrefixTailMargin)
        (by norm_num [thirdPrefixRho]) (by norm_num [thirdPrefixTailMargin]))
  have hevent := hupper.eventually (Iio_mem_nhds (ENNReal.ofReal_pos.mpr hε))
  have hsmall : Iio (thirdPrefixTailMargin / 4) ∈ 𝓝[>] (0 : ℝ) :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num [thirdPrefixTailMargin]))
  obtain ⟨h, hh, hs, hb⟩ := (self_mem_nhdsWithin.and (hsmall.and hevent)).exists
  exact ⟨h, hh, hs.le, fun e he0 he m =>
    (actualExtendedThirdFiniteNestedTailMass_le (m := m) he0 he hh hs.le).trans hb.le⟩

end

end ImbalancedChen
