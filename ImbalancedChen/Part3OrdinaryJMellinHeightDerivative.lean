import ImbalancedChen.Part3OrdinaryJHeightMellinNearZero
import ImbalancedChen.Part3ActualJFixedOrderMellinL1

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.

Standalone actual ordinary-J Mellin parameter differentiation. A genuine
full integrable majorant is built from the fresh ordinary derivative
near-zero power majorant and the actual forced-energy large-q bound.
Actual HasDerivAt under the Mellin integral is then proved; no domination
or derivative-interchange premise is an input. No critical kernel is used.
-/

namespace ImbalancedChen.Part3.OrdinaryJMellinHeightDerivative20261026b

noncomputable section
open Complex Set Filter MeasureTheory
open scoped Topology
open ActualJHeightRadialForcing20261026b ActualJOrderDerivativeUniformLargeQ20261026b
open OrdinaryJHeightMellinNearZero20261026b ActualJFixedOrderMellinL120261026b

theorem ordinaryJHeightMellinIntegrand_continuousOn (s : ℂ) (t : ℝ) :
    ContinuousOn (ordinaryJHeightMellinIntegrand s t) (Ioi 0) := by
  intro q hq
  have hp := Complex.continuousAt_ofReal_cpow_const q (s - 1) (Or.inr hq.ne')
  exact (hp.mul (heightOrderJ_q_hasDerivAt t hq).continuousAt).continuousWithinAt

theorem exists_ordinaryJHeightMellin_full_majorant {s : ℂ}
    (hs0 : 0 < s.re) (hsHalf : s.re < 1 / 2) (T : ℝ) :
    ∃ bound : ℝ → ℝ, IntegrableOn bound (Ioi 0) ∧
      ∀ t : ℝ, |t| ≤ T → ∀ q : ℝ, 0 < q →
        ‖ordinaryJHeightMellinIntegrand s t q‖ ≤ bound q := by
  obtain ⟨C0, hC0, hNear, hNearB⟩ := exists_ordinaryJHeightMellin_near_majorant hs0 T
  obtain ⟨C1, hC1, hTailB⟩ := exists_heightOrderJ_uniform_large_q_bound T
  let bound : ℝ → ℝ := fun q => if q ≤ 1 then C0 * q ^ (s.re / 2 - 1)
    else C1 * q ^ (s.re - 3 / 2)
  have hN : IntegrableOn bound (Ioc 0 1) := by
    apply hNear.congr_fun _ measurableSet_Ioc
    intro q hq
    simp only [bound, if_pos hq.2]
  have hTail : IntegrableOn (fun q : ℝ => C1 * q ^ (s.re - 3 / 2)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : s.re - 3 / 2 < -1)
      (by norm_num : (0 : ℝ) < 1)).const_mul C1
  have hT : IntegrableOn bound (Ioi 1) := by
    apply hTail.congr_fun _ measurableSet_Ioi
    intro q hq
    simp only [bound, if_neg (not_le.mpr hq)]
  have hI := hN.union hT
  rw [Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)] at hI
  refine ⟨bound, hI, ?_⟩
  intro t ht q hq
  by_cases hq1 : q ≤ 1
  · simpa only [bound, if_pos hq1] using hNearB t ht q ⟨hq, hq1⟩
  · have hqge : 1 ≤ q := (lt_of_not_ge hq1).le
    rw [bound, if_neg hq1, ordinaryJHeightMellinIntegrand, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hq]
    simp only [Complex.sub_re, Complex.one_re]
    calc
      q ^ (s.re - 1) * ‖heightOrderJ t q‖ ≤ q ^ (s.re - 1) * (C1 / Real.sqrt q) :=
        mul_le_mul_of_nonneg_left (hTailB t ht q hqge) (Real.rpow_nonneg hq.le _)
      _ = C1 * (q ^ (s.re - 1) / q ^ (1 / 2 : ℝ)) := by rw [Real.sqrt_eq_rpow]; ring
      _ = C1 * q ^ (s.re - 3 / 2) := by
        rw [← Real.rpow_sub hq]
        congr 1
        congr 1
        ring

theorem ordinaryJHeightMellinIntegrand_integrable {s : ℂ}
    (hs0 : 0 < s.re) (hsHalf : s.re < 1 / 2) (t : ℝ) :
    IntegrableOn (ordinaryJHeightMellinIntegrand s t) (Ioi 0) := by
  obtain ⟨bound, hI, hb⟩ := exists_ordinaryJHeightMellin_full_majorant hs0 hsHalf |t|
  apply hI.mono' ((ordinaryJHeightMellinIntegrand_continuousOn s t).aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
  exact hb t le_rfl q hq

theorem actualJMellinIntegrand_height_hasDerivAt (s : ℂ) (t : ℝ) {q : ℝ} (hq : 0 < q) :
    HasDerivAt (fun x : ℝ => actualJMellinIntegrand s x q)
      (ordinaryJHeightMellinIntegrand s t q) t :=
  (generalJ_height_hasDerivAt t hq).const_mul ((q : ℂ) ^ (s - 1))

/-- Genuine native parameter derivative of the ordinary-J Mellin integral,
with the derivative evaluated as the actual integrable height derivative. -/
theorem actualJMellinIntegral_height_hasDerivAt {s : ℂ}
    (hs0 : 0 < s.re) (hsHalf : s.re < 1 / 2) (t0 : ℝ) :
    HasDerivAt (actualJMellinIntegral s)
      (∫ q in Ioi (0 : ℝ), ordinaryJHeightMellinIntegrand s t0 q) t0 := by
  let U : Set ℝ := Ioo (t0 - 1) (t0 + 1)
  let T : ℝ := |t0| + 1
  obtain ⟨bound, hI, hb⟩ := exists_ordinaryJHeightMellin_full_majorant hs0 hsHalf T
  have hU : U ∈ 𝓝 t0 := isOpen_Ioo.mem_nhds ⟨by dsimp [U]; linarith, by dsimp [U]; linarith⟩
  have hmeas : ∀ᶠ t in 𝓝 t0, AEStronglyMeasurable (actualJMellinIntegrand s t)
      (volume.restrict (Ioi 0)) := Eventually.of_forall (fun t =>
    (actualJMellinIntegrand_continuousOn s t).aestronglyMeasurable measurableSet_Ioi)
  have hbound : ∀ᵐ q ∂volume.restrict (Ioi (0 : ℝ)), ∀ t ∈ U,
      ‖ordinaryJHeightMellinIntegrand s t q‖ ≤ bound q := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
    intro t ht
    have htT : |t| ≤ T := by
      dsimp [U] at ht
      dsimp [T]
      apply abs_le.mpr
      constructor <;> linarith [neg_abs_le t0, le_abs_self t0]
    exact hb t htT q hq
  have hdiff : ∀ᵐ q ∂volume.restrict (Ioi (0 : ℝ)), ∀ t ∈ U,
      HasDerivAt (fun x : ℝ => actualJMellinIntegrand s x q)
        (ordinaryJHeightMellinIntegrand s t q) t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
    exact fun t _ => actualJMellinIntegrand_height_hasDerivAt s t hq
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun t q => actualJMellinIntegrand s t q)
    (F' := fun t q => ordinaryJHeightMellinIntegrand s t q) (bound := bound)
    hU hmeas (integrableOn_actualJMellin hs0 hsHalf t0)
    ((ordinaryJHeightMellinIntegrand_continuousOn s t0).aestronglyMeasurable measurableSet_Ioi)
    hbound hI hdiff).2

end
end ImbalancedChen.Part3.OrdinaryJMellinHeightDerivative20261026b
