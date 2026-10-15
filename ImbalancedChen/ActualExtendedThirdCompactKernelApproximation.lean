import ImbalancedChen.ActualExtendedThirdGammaApproximation
import ImbalancedChen.ActualExtendedThirdStripIntegral
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Uniform approximation of the actual finite correction kernel off its walls

The actual retained Ico lookup, including its original dispatch tests, is
used throughout. Its missing rho cells and its mu dispatch failures are
excluded only by the two literal strips of width 4e + mesh. The proved
robust Gamma estimate then bounds the same lookup's level error.

The canonical clamped lower factor is uniformly continuous on a concrete
compact argument interval. Both changes in the kernel are paid: the old
level Theta - 2e tends to Theta, and the actual finite level tends to the
literal ideal cap. No modulus of continuity, selector approximation, or
integral limit is a caller hypothesis. This is a compact analytic estimate;
the full integral and same-policy arithmetic count remain separate steps.
-/

namespace ImbalancedChen

noncomputable section

open Set Filter Topology MeasureTheory
open VariableEnvelope
open scoped Classical

theorem actualExtendedThirdFiniteLevel_error_off_strips
    {e h : ℝ} {m : ℕ} {t : Fin 3 → ℝ}
    (he : 0 ≤ e) (hh : 0 ≤ h) (ht : t ∈ actualExtendedThirdCompactOrder h)
    (hfine : e + 7 * actualExtendedThirdDyadicStep m ≤ 3 / 256)
    (hmu : t ∉ actualExtendedThirdWallStrip h mu (4 * e + actualExtendedThirdDyadicStep m))
    (hrho : t ∉ actualExtendedThirdWallStrip h thirdPrefixRho
      (4 * e + actualExtendedThirdDyadicStep m)) :
    0 ≤ actualExtendedThirdIdealCap (t 0) (t 1) (t 2) - actualExtendedThirdFiniteLevel e m t ∧
      actualExtendedThirdIdealCap (t 0) (t 1) (t 2) - actualExtendedThirdFiniteLevel e m t ≤
        2 * e + (9 / 2 : ℝ) * actualExtendedThirdDyadicStep m := by
  have htclosed : t ∈ actualExtendedThirdClosedOrder :=
    ⟨hh.trans ht.1, ht.2.1, ht.2.2.1⟩
  have hstop : t 0 + actualExtendedThirdDyadicStep m ≤ thirdPrefixRho - 4 * e := by
    by_contra hn
    apply hrho
    exact ⟨ht, by linarith [lt_of_not_ge hn], ht.2.2.2⟩
  obtain ⟨j, ⟨hjr, hjt⟩, _⟩ := actualExtendedThirdRetained_unique_cover he htclosed hstop
  have hjp := actualExtendedThirdOwnedCell_subset_physicalCell m j hjt
  have hwall : actualExtendedThirdDyadicHi m j 0 ≤ mu - 4 * e ∨ mu < t 0 := by
    by_cases hx : mu < t 0
    · exact Or.inr hx
    · left
      have hclear : t 0 + actualExtendedThirdDyadicStep m ≤ mu - 4 * e := by
        by_contra hn
        apply hmu
        exact ⟨ht, by linarith [lt_of_not_ge hn], le_of_not_gt hx⟩
      exact (actualExtendedThirdDyadicHi_le_point_add_step hjp 0).trans hclear
  rw [actualExtendedThirdFiniteLevel_on_cell hjr hjt]
  exact actualExtendedThirdPhysicalLevel_error he hjp hfine hwall

private theorem factor_clamp (s : ℝ) :
    actualExtendedThirdLowerFactor (max 2 s) = actualExtendedThirdLowerFactor s := by
  simp only [actualExtendedThirdLowerFactor, ← max_assoc, max_self]

private theorem clamped_arg_mem {h x y z : ℝ} (hh : 0 < h)
    (hx : h ≤ x) (hy : h ≤ y) (hz : h ≤ z) {a : ℝ} (ha : a ≤ thirdPrefixTheta) :
    max 2 ((a - x - y - z) / z) ∈ Icc (2 : ℝ) (max 2 (thirdPrefixTheta / h)) := by
  have hz0 : 0 < z := hh.trans_le hz
  refine ⟨le_max_left _ _, max_le (le_max_left _ _) ?_⟩
  calc
    (a - x - y - z) / z ≤ thirdPrefixTheta / z :=
      div_le_div_of_nonneg_right (by linarith [hh.trans_le hx, hh.trans_le hy]) hz0.le
    _ ≤ thirdPrefixTheta / h := by
      apply (div_le_div_iff₀ hz0 hh).mpr
      exact mul_le_mul_of_nonneg_left hz (by norm_num [thirdPrefixTheta])
    _ ≤ max 2 (thirdPrefixTheta / h) := le_max_right _ _

/-- A genuine modulus is constructed from the actual canonical factor. Its
argument interval depends only on the positive compact cutoff. -/
theorem actualExtendedThirdCapKernel_uniform_approx {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ e λ L x y z : ℝ,
      0 ≤ e → 2 * e ≤ η → λ ≤ thirdPrefixTheta → L ≤ thirdPrefixTheta →
      |λ - L| ≤ η → h ≤ x → h ≤ y → h ≤ z →
        |actualExtendedThirdCapKernel e λ x y z -
          actualExtendedThirdCapKernel 0 L x y z| ≤ ε := by
  let τ : ℝ := ε * h ^ 4 / 16
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have huc : UniformContinuousOn actualExtendedThirdLowerFactor
      (Icc (2 : ℝ) (max 2 (thirdPrefixTheta / h))) :=
    isCompact_Icc.uniformContinuousOn_of_continuous
      continuous_actualExtendedThirdLowerFactor.continuousOn
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff.mp huc τ hτ
  refine ⟨δ * h / 2, by positivity, ?_⟩
  intro e λ L x y z he heη hλ hL hλL hx hy hz
  have hx0 : 0 < x := hh.trans_le hx
  have hy0 : 0 < y := hh.trans_le hy
  have hz0 : 0 < z := hh.trans_le hz
  have hfactor (a b : ℝ) (ha : a ≤ thirdPrefixTheta) (hb : b ≤ thirdPrefixTheta)
      (hab : |a - b| ≤ δ * h / 2) :
      |actualExtendedThirdLowerFactor ((a - x - y - z) / z) -
        actualExtendedThirdLowerFactor ((b - x - y - z) / z)| ≤ τ := by
    have hraw : |(a - x - y - z) / z - (b - x - y - z) / z| ≤ δ / 2 := by
      calc
        _ = |a - b| / z := by
          rw [← sub_div, abs_div, abs_of_pos hz0]
          congr 1
          congr 1
          ring
        _ ≤ (δ * h / 2) / z := div_le_div_of_nonneg_right hab hz0.le
        _ ≤ δ / 2 := by
          apply (div_le_iff₀ hz0).mpr
          nlinarith [mul_le_mul_of_nonneg_left hz (half_pos hδ).le]
    have hclamp :
        |max 2 ((a - x - y - z) / z) - max 2 ((b - x - y - z) / z)| ≤
          |(a - x - y - z) / z - (b - x - y - z) / z| := by
      simpa only [max_comm] using (_root_.abs_max_sub_max_le_abs
        ((a - x - y - z) / z) ((b - x - y - z) / z) (2 : ℝ))
    have hd : dist (max 2 ((a - x - y - z) / z))
        (max 2 ((b - x - y - z) / z)) < δ := by
      rw [Real.dist_eq]
      exact (hclamp.trans hraw).trans_lt (half_lt_self hδ)
    have hv := hclose _ (clamped_arg_mem hh hx hy hz ha)
      _ (clamped_arg_mem hh hx hy hz hb) hd
    rw [Real.dist_eq, factor_clamp, factor_clamp] at hv
    exact hv.le
  have hold : |(thirdPrefixTheta - 2 * e) - thirdPrefixTheta| ≤ δ * h / 2 := by
    have heq : (thirdPrefixTheta - 2 * e) - thirdPrefixTheta = -(2 * e) := by ring
    rw [heq, abs_neg, abs_of_nonneg (mul_nonneg (by norm_num) he)]
    exact heη
  have ho := hfactor (thirdPrefixTheta - 2 * e) thirdPrefixTheta (by linarith) le_rfl hold
  have hn := hfactor λ L hλ hL hλL
  let a := actualExtendedThirdLowerFactor ((thirdPrefixTheta - 2 * e - x - y - z) / z)
  let b := actualExtendedThirdLowerFactor ((λ - x - y - z) / z)
  let c := actualExtendedThirdLowerFactor ((thirdPrefixTheta - x - y - z) / z)
  let d := actualExtendedThirdLowerFactor ((L - x - y - z) / z)
  change |a - c| ≤ τ at ho
  change |b - d| ≤ τ at hn
  have hdiff : |(a - b) - (c - d)| ≤ 2 * τ := by
    calc
      _ = |(a - c) - (b - d)| := by congr 1; ring
      _ ≤ |a - c| + |b - d| := abs_sub _ _
      _ ≤ τ + τ := add_le_add ho hn
      _ = 2 * τ := by ring
  have hnum : |4 * ((a - b) - (c - d))| ≤ 8 * τ := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    linarith
  have hden : 0 < x * y * z ^ 2 := by positivity
  have hdenlower : h ^ 4 ≤ x * y * z ^ 2 := by
    have hxy := mul_le_mul hx hy hh.le hx0.le
    have hz2 := pow_le_pow_left₀ hh.le hz 2
    calc
      _ = (h * h) * h ^ 2 := by ring
      _ ≤ (x * y) * z ^ 2 := mul_le_mul hxy hz2 (sq_nonneg _) (by positivity)
  simp only [actualExtendedThirdCapKernel, mul_zero, sub_zero]
  change |4 * (a - b) / (x * y * z ^ 2) - 4 * (c - d) / (x * y * z ^ 2)| ≤ ε
  rw [← sub_div, ← mul_sub, abs_div, abs_of_pos hden]
  calc
    _ ≤ (8 * τ) / (x * y * z ^ 2) := div_le_div_of_nonneg_right hnum hden.le
    _ ≤ (8 * τ) / h ^ 4 := by
      apply (div_le_div_iff₀ hden (pow_pos hh 4)).mpr
      exact mul_le_mul_of_nonneg_left hdenlower (by positivity)
    _ = ε / 2 := by
      dsimp [τ]
      field_simp [hh.ne']
      <;> ring
    _ ≤ ε := by linarith

/-- The old-cube complement has zero kernel pointwise: clamping at two
pays the original gate, including its equality face. -/
theorem actualExtendedThirdGatedKernel_zero_buffer_eq_capKernel {x y z : ℝ} (hz : 0 < z) :
    actualExtendedThirdGatedKernel 0 x y z =
      actualExtendedThirdCapKernel 0 (actualExtendedThirdIdealCap x y z) x y z := by
  unfold actualExtendedThirdGatedKernel
  split_ifs with hc
  · rfl
  · have hL : actualExtendedThirdIdealCap x y z ≤ thirdPrefixTheta := by
      rw [actualExtendedThirdIdealCap_eq]
      exact min_le_left _ _
    simp only [mul_zero, sub_zero] at hc
    have ho : (thirdPrefixTheta - x - y - z) / z ≤ 2 := by
      apply (div_le_iff₀ hz).mpr
      linarith [le_of_not_gt hc]
    have hn : (actualExtendedThirdIdealCap x y z - x - y - z) / z ≤ 2 := by
      apply (div_le_iff₀ hz).mpr
      linarith [le_of_not_gt hc]
    unfold actualExtendedThirdCapKernel
    simp only [mul_zero, sub_zero, actualExtendedThirdLowerFactor_of_le_two ho,
      actualExtendedThirdLowerFactor_of_le_two hn, sub_self, zero_div]

/-- The same mesh threshold works for every point outside the two actual
wall strips. The limit kernel is the literal unbuffered ideal kernel. -/
theorem actualExtendedThirdFiniteKernel_uniform_approx_off_strips
    {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε) :
    ∃ e₀ : ℝ, 0 < e₀ ∧ e₀ ≤ 1 / 384 ∧ ∃ m₀ : ℕ,
      ∀ e : ℝ, 0 ≤ e → e ≤ e₀ → ∀ m : ℕ, m₀ ≤ m →
        ∀ t ∈ actualExtendedThirdCompactOrder h,
          t ∉ actualExtendedThirdWallStrip h mu (4 * e + actualExtendedThirdDyadicStep m) →
          t ∉ actualExtendedThirdWallStrip h thirdPrefixRho
            (4 * e + actualExtendedThirdDyadicStep m) →
          |actualExtendedThirdFiniteKernel e m t -
            actualExtendedThirdGatedKernel 0 (t 0) (t 1) (t 2)| ≤ ε := by
  obtain ⟨η, hη, happrox⟩ := actualExtendedThirdCapKernel_uniform_approx hh hε
  let e₀ : ℝ := min (η / 8) (min (3 / 1024) (1 / 384))
  have he₀ : 0 < e₀ := by dsimp [e₀]; positivity
  have hgrid : 0 < min (η / 18) (3 / 7168 : ℝ) := by positivity
  obtain ⟨m₀, hm₀⟩ := Filter.eventually_atTop.mp
    (tendsto_actualExtendedThirdDyadicStep.eventually (gt_mem_nhds hgrid))
  refine ⟨e₀, he₀, (min_le_right _ _).trans (min_le_right _ _), m₀, ?_⟩
  intro e he0 he m hm t ht hmu hrho
  have heη : e ≤ η / 8 := he.trans (min_le_left _ _)
  have hegrid : e ≤ 3 / 1024 := he.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hmη : actualExtendedThirdDyadicStep m ≤ η / 18 :=
    (hm₀ m hm).le.trans (min_le_left _ _)
  have hmgrid : actualExtendedThirdDyadicStep m ≤ 3 / 7168 :=
    (hm₀ m hm).le.trans (min_le_right _ _)
  have hfine : e + 7 * actualExtendedThirdDyadicStep m ≤ 3 / 256 := by linarith
  have hlevel := actualExtendedThirdFiniteLevel_error_off_strips he0 hh.le ht hfine hmu hrho
  have hroot : actualExtendedThirdFiniteLevel e m t ≤ thirdPrefixTheta :=
    (actualExtendedThirdFiniteLevel_le_root e m t).trans (by linarith)
  have hL : actualExtendedThirdIdealCap (t 0) (t 1) (t 2) ≤ thirdPrefixTheta := by
    rw [actualExtendedThirdIdealCap_eq]
    exact min_le_left _ _
  have hdiff : |actualExtendedThirdFiniteLevel e m t -
      actualExtendedThirdIdealCap (t 0) (t 1) (t 2)| ≤ η := by
    rw [abs_sub_comm, abs_of_nonneg hlevel.1]
    linarith [hlevel.2]
  rw [actualExtendedThirdGatedKernel_zero_buffer_eq_capKernel (hh.trans_le ht.1)]
  exact happrox e _ _ _ _ _ he0 (by linarith) hroot hL hdiff
    (ht.1.trans (ht.2.1.trans ht.2.2.1)) (ht.1.trans ht.2.1) ht.1

end

end ImbalancedChen
